#!/usr/bin/env python3
"""Build a weekly cyber threat newsletter (one HTML issue) from RSS/Atom feeds.

Pipeline: fetch feeds -> keep recent items -> merge duplicate stories ->
categorize and extract CVE IDs -> rank -> render email-friendly HTML.

Usage:
    python newsletter.py
    python newsletter.py --days 3 --max-per-section 5
    python newsletter.py --feeds feeds.json --title "Weekly Threat Brief"
    python newsletter.py --images feed --logo https://example.com/logo.png

Standard library only (Python 3.9+).
"""

import argparse
import base64
import html
import json
import logging
import re
import sys
import xml.etree.ElementTree as ET
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from difflib import SequenceMatcher
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlparse, urlunparse
from urllib.request import Request, urlopen

log = logging.getLogger("newsletter")

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

FEEDS = [
    {"name": "BleepingComputer", "url": "https://www.bleepingcomputer.com/feed/"},
    {"name": "The Hacker News", "url": "https://feeds.feedburner.com/TheHackersNews"},
    {"name": "Krebs on Security", "url": "https://krebsonsecurity.com/feed/"},
    {"name": "CISA Advisories", "url": "https://www.cisa.gov/cybersecurity-advisories/all.xml"},
    {"name": "Cisco Talos", "url": "https://blog.talosintelligence.com/rss/"},
    {"name": "Unit 42", "url": "https://unit42.paloaltonetworks.com/feed/"},
    {"name": "The Record", "url": "https://therecord.media/feed"},
    {"name": "Schneier on Security", "url": "https://www.schneier.com/feed/atom/"},
]

# Section order follows this list; the highest keyword score decides the section.
CATEGORIES = [
    ("Ransomware & Extortion", r"ransom\w*|extortion"),
    (
        "Vulnerabilities & Patches",
        r"CVE-\d{4}-\d{4,7}|zero[- ]days?|0-days?|vulnerabilit\w*|patch\w*|exploit\w*|RCE|security updates?",
    ),
    (
        "Threat Actors & Malware",
        r"APT\d*|threat actors?|malware|botnet|backdoor|espionage|nation[- ]state|"
        r"state[- ]sponsored|infostealer|phishing|spyware",
    ),
    ("Breaches & Leaks", r"breach\w*|data leak\w*|leak\w*|stolen data|exposed"),
]
CATEGORIES = [(name, re.compile(rf"\b(?:{pattern})\b", re.I)) for name, pattern in CATEGORIES]
FALLBACK_CATEGORY = "Other News"

CVE_RE = re.compile(r"\bCVE-\d{4}-\d{4,7}\b", re.I)

SUMMARY_CHARS = 160
TOP_STORIES = 3
MAX_CVES = 6
DUPLICATE_OVERLAP = 0.7  # share of key title words that must match to merge stories
TITLE_SIMILARITY = 0.85  # near-identical titles are merged regardless of word overlap

FEED_TIMEOUT = 20
PAGE_TIMEOUT = 10
MAX_FEED_BYTES = 5_000_000
PAGE_HEAD_BYTES = 300_000
MAX_WORKERS = 8

LOGO_WIDTH = 150

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

# Email colours
INK, MUTED, SUBTLE = "#111827", "#4b5563", "#6b7280"
ACCENT, ACCENT_BG, ACCENT_DARK = "#b91c1c", "#fef2f2", "#991b1b"
BORDER, PAGE_BG = "#e5e7eb", "#f3f4f6"


# --------------------------------------------------------------------------- #
# Data model
# --------------------------------------------------------------------------- #


@dataclass
class Item:
    title: str
    link: str
    source: str
    published: datetime
    summary: str
    category: str = FALLBACK_CATEGORY
    cves: list = field(default_factory=list)
    also_in: list = field(default_factory=list)
    image: str = ""

    @property
    def coverage(self) -> int:
        return 1 + len(self.also_in)


# --------------------------------------------------------------------------- #
# Fetching
# --------------------------------------------------------------------------- #


def http_get(url: str, accept: str, timeout: int, limit: int) -> bytes:
    """Read at most limit + 1 bytes so callers can detect oversized responses."""
    request = Request(url, headers={"User-Agent": USER_AGENT, "Accept": accept})
    with urlopen(request, timeout=timeout) as response:
        return response.read(limit + 1)


def fetch_feed(url: str) -> bytes:
    accept = "application/rss+xml, application/atom+xml, application/xml, text/xml, */*"
    data = http_get(url, accept, FEED_TIMEOUT, MAX_FEED_BYTES)
    if len(data) > MAX_FEED_BYTES:
        raise ValueError("feed larger than 5 MB")
    return data


# --------------------------------------------------------------------------- #
# Parsing (RSS 2.0 and Atom)
# --------------------------------------------------------------------------- #


def local_name(tag) -> str:
    """Strip the XML namespace: '{http://...}title' -> 'title'."""
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def child_text(element, *names: str) -> str:
    """Text of the first non-empty child matching the names, in priority order."""
    for name in names:
        for child in element:
            if local_name(child.tag) == name and (child.text or "").strip():
                return child.text.strip()
    return ""


def entry_link(element) -> str:
    original = child_text(element, "origLink")  # FeedBurner keeps the real URL here
    if original:
        return original
    fallback = ""
    for child in element:
        if local_name(child.tag) != "link":
            continue
        href = child.get("href")
        if href:  # Atom
            if child.get("rel", "alternate") == "alternate":
                return href
            fallback = fallback or href
        elif (child.text or "").strip():  # RSS
            return child.text.strip()
    return fallback


def strip_tracking(url: str) -> str:
    parts = urlparse(url)
    query = [
        (key, value)
        for key, value in parse_qsl(parts.query, keep_blank_values=True)
        if not key.lower().startswith("utm_")
    ]
    return urlunparse(parts._replace(query=urlencode(query)))


def parse_date(raw: str):
    raw = (raw or "").strip()
    if not raw:
        return None
    try:
        parsed = parsedate_to_datetime(raw)  # RSS: RFC 822
    except (TypeError, ValueError):
        try:
            parsed = datetime.fromisoformat(raw.replace("Z", "+00:00"))  # Atom: ISO 8601
        except ValueError:
            return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


class TextExtractor(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []
        self._skip_depth = 0

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self._skip_depth += 1

    def handle_endtag(self, tag):
        if tag in ("script", "style") and self._skip_depth:
            self._skip_depth -= 1

    def handle_data(self, data):
        if not self._skip_depth:
            self.parts.append(data)


def html_to_text(raw: str) -> str:
    extractor = TextExtractor()
    extractor.feed(raw)
    extractor.close()
    text = re.sub(r"\s+", " ", "".join(extractor.parts)).strip()
    # WordPress feeds append "The post X appeared first on Y."
    return re.sub(r"\s*The post .{0,300}? appeared first on .{0,100}$", "", text).strip()


def shorten(text: str, limit: int = SUMMARY_CHARS) -> str:
    if len(text) <= limit:
        return text
    return text[:limit].rsplit(" ", 1)[0].rstrip(".,;:-") + "…"


def categorize(title: str, body: str) -> str:
    best, best_score = FALLBACK_CATEGORY, 0
    for name, pattern in CATEGORIES:
        score = 3 * len(pattern.findall(title)) + len(pattern.findall(body))
        if score > best_score:
            best, best_score = name, score
    return best


# --- Images ----------------------------------------------------------------- #

IMG_TAG_RE = re.compile(r"<img\b[^>]*?\bsrc\s*=\s*[\"']([^\"']+)[\"']", re.I)
JUNK_IMAGE_RE = re.compile(
    r"pixel|1x1|spacer|tracker|tracking|beacon|smilies|gravatar|emoji|feedburner\.com/~", re.I
)
IMAGE_EXT_RE = re.compile(r"\.(?:jpe?g|png|webp|gif|avif)(?:$|[?#])", re.I)
META_RE = re.compile(r"<meta\b[^>]*>", re.I)
ATTR_RE = re.compile(r"""([\w:-]+)\s*=\s*(?:"([^"]*)"|'([^']*)')""")
PREVIEW_KEYS = ("og:image", "og:image:secure_url", "twitter:image", "twitter:image:src")


def clean_image_url(url: str, base: str = "") -> str:
    """Return an absolute http(s) image URL, or '' if it is unusable."""
    url = html.unescape((url or "").strip())
    if not url:
        return ""
    if url.startswith("//"):
        url = "https:" + url
    url = urljoin(base, url)
    if urlparse(url).scheme not in ("http", "https") or JUNK_IMAGE_RE.search(url):
        return ""
    return url


def is_image(child, url: str) -> bool:
    return (
        (child.get("type") or "").startswith("image/")
        or child.get("medium") == "image"
        or bool(IMAGE_EXT_RE.search(url))
    )


def entry_image(element, raw_html: str, base: str) -> str:
    """Find a thumbnail in the places feeds usually put one."""
    for child in element:
        name = local_name(child.tag)
        if name == "thumbnail":
            found = clean_image_url(child.get("url", ""), base)
        elif name in ("content", "enclosure") and is_image(child, child.get("url") or ""):
            found = clean_image_url(child.get("url", ""), base)
        elif name == "link" and child.get("rel") == "enclosure" and is_image(child, child.get("href", "")):
            found = clean_image_url(child.get("href", ""), base)
        else:
            continue
        if found:
            return found
    for src in IMG_TAG_RE.findall(raw_html):
        found = clean_image_url(src, base)
        if found:
            return found
    return ""


def page_image(page_html: str, base: str) -> str:
    """The preview image a page declares via og:image or twitter:image."""
    for tag in META_RE.findall(page_html):
        attrs = {m.group(1).lower(): m.group(2) or m.group(3) or "" for m in ATTR_RE.finditer(tag)}
        if (attrs.get("property") or attrs.get("name") or "").lower() in PREVIEW_KEYS:
            found = clean_image_url(attrs.get("content", ""), base)
            if found:
                return found
    return ""


def fetch_page_image(url: str) -> str:
    try:
        data = http_get(url, "text/html", PAGE_TIMEOUT, PAGE_HEAD_BYTES)[:PAGE_HEAD_BYTES]
        head = data.decode("utf-8", errors="ignore").split("</head>", 1)[0]
        return page_image(head, url)
    except Exception:
        return ""


def fill_missing_images(items: list) -> None:
    missing = [item for item in items if not item.image]
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        for item, image in zip(missing, pool.map(lambda i: fetch_page_image(i.link), missing)):
            item.image = image


def attach_images(items: list, mode: str) -> None:
    if mode == "none":
        for item in items:
            item.image = ""
        return
    if mode == "all":
        log.info("Looking up preview images for stories without one...")
        fill_missing_images(items)
    log.info("Thumbnails: %d of %d stories", sum(1 for i in items if i.image), len(items))


# --- Feed -> items ---------------------------------------------------------- #


def parse_feed(data: bytes, source: str) -> list:
    if b"<!ENTITY" in data:  # refuse XML entity expansion tricks from untrusted feeds
        raise ValueError("feed contains XML entity declarations")
    items = []
    for element in ET.fromstring(data).iter():
        if local_name(element.tag) not in ("item", "entry"):
            continue
        title = html_to_text(child_text(element, "title"))
        link = strip_tracking(entry_link(element))
        published = parse_date(child_text(element, "pubDate", "published", "updated", "date"))
        if not (title and link and published):
            continue
        if urlparse(link).scheme not in ("http", "https"):
            continue
        body_fields = ("description", "summary", "encoded", "content")
        body = html_to_text(child_text(element, *body_fields))
        raw_html = " ".join(child_text(element, name) for name in body_fields)
        items.append(
            Item(
                title=title,
                link=link,
                source=source,
                published=published,
                summary=shorten(body),
                category=categorize(title, body),
                cves=sorted({c.upper() for c in CVE_RE.findall(f"{title} {body}")}),
                image=entry_image(element, raw_html, link),
            )
        )
    return items


def collect(feeds: list, since: datetime):
    """Fetch all feeds in parallel. Returns (recent items in feed order, error messages)."""

    def load(feed):
        try:
            items = parse_feed(fetch_feed(feed["url"]), feed["name"])
            return [i for i in items if i.published >= since], None
        except Exception as exc:  # one broken feed must not stop the issue
            return [], f"{feed['name']}: {exc}"

    items, errors = [], []
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        for feed, (recent, error) in zip(feeds, pool.map(load, feeds)):
            if error:
                errors.append(error)
                continue
            log.info("  %s: %d recent items", feed["name"], len(recent))
            items.extend(recent)
    return items, errors


# --------------------------------------------------------------------------- #
# Deduplication and ranking
# --------------------------------------------------------------------------- #

STOPWORDS = {
    "about", "after", "against", "attack", "attacks", "being", "cyber", "from",
    "hacker", "hackers", "have", "into", "more", "over", "says", "said", "that",
    "their", "this", "threat", "using", "used", "with", "your",
}  # fmt: skip


def url_key(url: str) -> str:
    parts = urlparse(url)
    return f"{parts.netloc.lower().removeprefix('www.')}{parts.path.rstrip('/')}?{parts.query}"


def stem(word: str) -> str:
    """Crude stemmer so 'patches'/'patch' and 'exploited'/'exploiting' line up."""
    for suffix in ("ing", "ed", "es", "s"):
        if word.endswith(suffix) and len(word) - len(suffix) >= 4:
            return word[: -len(suffix)]
    return word


def title_words(title: str) -> set:
    title = CVE_RE.sub(" ", title.lower())
    words = (w for w in re.findall(r"[a-z0-9]+", title) if len(w) > 3 and w not in STOPWORDS)
    return {stem(w) for w in words}


def same_story(a: Item, b: Item) -> bool:
    if url_key(a.link) == url_key(b.link):
        return True
    words_a, words_b = title_words(a.title), title_words(b.title)
    shared = words_a & words_b
    if len(shared) >= 3 and len(shared) / min(len(words_a), len(words_b)) >= DUPLICATE_OVERLAP:
        return True
    return SequenceMatcher(None, a.title.lower(), b.title.lower()).ratio() >= TITLE_SIMILARITY


def dedupe(items: list) -> list:
    """Merge the same story across outlets. Earlier feeds take priority."""
    kept = []
    for item in items:
        for existing in kept:
            if same_story(existing, item):
                if item.source != existing.source and item.source not in existing.also_in:
                    existing.also_in.append(item.source)
                break
        else:
            kept.append(item)
    return kept


def build_sections(items: list, max_per_section: int):
    ranked = sorted(items, key=lambda i: (-i.coverage, -i.published.timestamp()))
    top = [i for i in ranked if i.coverage >= 2][:TOP_STORIES]
    top_ids = {id(i) for i in top}

    buckets = {}
    for item in ranked:
        if id(item) not in top_ids:
            buckets.setdefault(item.category, []).append(item)

    order = [name for name, _ in CATEGORIES] + [FALLBACK_CATEGORY]
    return top, [(name, buckets[name][:max_per_section]) for name in order if name in buckets]


# --------------------------------------------------------------------------- #
# Rendering (email-friendly HTML: tables and inline styles)
# --------------------------------------------------------------------------- #

IMAGE_MIME = {
    ".png": "image/png",
    ".jpg": "image/jpeg",
    ".jpeg": "image/jpeg",
    ".webp": "image/webp",
    ".gif": "image/gif",
    ".svg": "image/svg+xml",
}


def resolve_logo(spec: str) -> str:
    """Turn --logo (URL or file path) into an <img> src, or '' if unusable."""
    if not spec:
        return ""
    if urlparse(spec).scheme in ("http", "https"):
        return spec
    path = Path(spec).expanduser()
    if not path.is_file():
        path = Path(__file__).resolve().parent / spec
    if not path.is_file():
        log.warning("Logo '%s' not found, continuing without it", spec)
        return ""
    mime = IMAGE_MIME.get(path.suffix.lower())
    if not mime:
        log.warning("Logo '%s' is not a supported image type, continuing without it", spec)
        return ""
    return f"data:{mime};base64,{base64.b64encode(path.read_bytes()).decode()}"


def esc(text: str) -> str:
    return html.escape(text, quote=True)


def cve_chip(cve: str, link: bool = False, label: str = "") -> str:
    label = label or esc(cve)
    if link:
        return (
            f'<a href="https://nvd.nist.gov/vuln/detail/{esc(cve)}" style="display:inline-block;'
            f"font:12px Menlo,Consolas,monospace;background:{ACCENT_BG};color:{ACCENT_DARK};"
            f'padding:4px 8px;border-radius:4px;margin:0 6px 6px 0;text-decoration:none;">{label}</a>'
        )
    return (
        f'<span style="display:inline-block;font:11px Menlo,Consolas,monospace;background:{ACCENT_BG};'
        f'color:{ACCENT_DARK};padding:2px 6px;border-radius:4px;margin:6px 4px 0 0;">{label}</span>'
    )


def render_heading(text: str) -> str:
    return (
        '<tr><td style="padding:22px 28px 6px;font-size:13px;font-weight:700;letter-spacing:.08em;'
        f'text-transform:uppercase;color:{ACCENT};">{esc(text)}</td></tr>'
    )


def render_item(item: Item) -> str:
    meta = f"{esc(item.source)} &middot; {item.published:%a %d %b}"
    if item.also_in:
        meta += f" &middot; also {esc(', '.join(item.also_in))}"

    chips = "".join(cve_chip(cve) for cve in item.cves[:2])
    teaser = (
        f'<div style="font-size:13px;line-height:1.45;color:{MUTED};">{esc(item.summary)}</div>'
        if item.summary
        else ""
    )
    text_cell = (
        f'<a href="{esc(item.link)}" style="font-size:15px;font-weight:600;color:{INK};'
        f'text-decoration:none;line-height:1.3;">{esc(item.title)}</a>'
        f'<div style="font-size:11px;color:{SUBTLE};margin:3px 0 5px;">{meta}</div>'
        f"{teaser}{chips}"
    )
    image_cell = (
        '<td width="128" valign="top" style="width:128px;padding-left:14px;">'
        f'<a href="{esc(item.link)}"><img src="{esc(item.image)}" width="128" height="80" alt="" '
        f'style="display:block;width:128px;height:80px;object-fit:cover;border:0;border-radius:6px;'
        f'background:{BORDER};"></a></td>'
        if item.image
        else ""
    )
    return (
        f'<tr><td style="padding:12px 28px;border-bottom:1px solid {BORDER};">'
        '<table role="presentation" width="100%" cellpadding="0" cellspacing="0"><tr>'
        f'<td valign="top">{text_cell}</td>{image_cell}</tr></table></td></tr>'
    )


def render_cves(counts: Counter) -> str:
    if not counts:
        return ""
    chips = "".join(
        cve_chip(cve, link=True, label=esc(cve) + (f" &times;{n}" if n > 1 else ""))
        for cve, n in counts.most_common(MAX_CVES)
    )
    return render_heading("CVEs in the news") + (
        f'<tr><td style="padding:6px 28px 14px;border-bottom:1px solid {BORDER};">{chips}</td></tr>'
    )


def render_header(title: str, subtitle: str, logo_src: str) -> str:
    logo_cell = ""
    title_style = ""
    if logo_src:
        # White plate: dark wordmarks would disappear against the dark header.
        logo_cell = (
            f'<td class="hdr-cell hdr-logo" valign="middle" width="{LOGO_WIDTH + 38}" '
            f'style="width:{LOGO_WIDTH + 38}px;padding-right:18px;">'
            '<table role="presentation" cellpadding="0" cellspacing="0" '
            'style="background:#ffffff;border-radius:8px;"><tr><td style="padding:7px 10px;">'
            f'<img src="{esc(logo_src)}" width="{LOGO_WIDTH}" alt="{esc(title)}" '
            f'style="display:block;width:{LOGO_WIDTH}px;max-width:100%;height:auto;border:0;">'
            "</td></tr></table></td>"
        )
        title_style = "padding-left:18px;border-left:1px solid #374151;"

    return (
        f'<tr><td style="background:{INK};padding:22px 28px;">'
        '<table role="presentation" width="100%" cellpadding="0" cellspacing="0"><tr>'
        f'{logo_cell}<td class="hdr-cell" valign="middle" style="{title_style}">'
        f'<div style="font-size:21px;font-weight:700;line-height:1.25;color:#ffffff;">{esc(title)}</div>'
        f'<div style="font-size:13px;line-height:1.4;color:#9ca3af;margin-top:6px;">{subtitle}</div>'
        "</td></tr></table></td></tr>"
    )


def render_issue(title, since, until, top, sections, cve_counts, total, logo_src="") -> str:
    rows = []
    if top:
        rows.append(render_heading("Top stories (covered by multiple outlets)"))
        rows.extend(render_item(i) for i in top)
    rows.append(render_cves(cve_counts))
    for name, items in sections:
        rows.append(render_heading(name))
        rows.extend(render_item(i) for i in items)

    shown = top + [i for _, items in sections for i in items]
    sources = {i.source for i in shown} | {s for i in shown for s in i.also_in}
    span = f"{since:%d %b} &ndash; {until:%d %b %Y}"
    subtitle = f"{span} &middot; {total} stories from {len(sources)} source{'' if len(sources) == 1 else 's'}"

    return f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{esc(title)}</title>
<style>
@media only screen and (max-width:480px) {{
  .hdr-cell {{ display:block !important; width:auto !important; padding:0 !important; border:0 !important; }}
  .hdr-logo {{ padding-bottom:14px !important; }}
}}
</style></head>
<body style="margin:0;padding:0;background:{PAGE_BG};font-family:-apple-system,'Segoe UI',Roboto,Helvetica,Arial,sans-serif;">
<table role="presentation" width="100%" cellpadding="0" cellspacing="0" style="background:{PAGE_BG};"><tr><td align="center" style="padding:24px 12px;">
<table role="presentation" width="600" cellpadding="0" cellspacing="0" style="width:100%;max-width:600px;background:#ffffff;border-radius:8px;overflow:hidden;">
{render_header(title, subtitle, logo_src)}
{"".join(rows)}
<tr><td style="padding:22px 28px;font-size:12px;line-height:1.5;color:{SUBTLE};">
  Headlines, short excerpts and thumbnails come from, and link to, the original publishers. Read the full stories at the source.
</td></tr>
</table></td></tr></table></body></html>
"""


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build a weekly cyber threat newsletter from RSS/Atom feeds.")
    parser.add_argument("--days", type=int, default=7, help="days to look back (default: 7)")
    parser.add_argument("--max-per-section", type=int, default=3, help="stories per section (default: 3)")
    parser.add_argument(
        "--images",
        choices=["all", "feed", "none"],
        default="all",
        help="all: feed thumbnails plus article preview images; feed: feed thumbnails only; none: text only",
    )
    parser.add_argument("--title", default="Weekly Cyber Threat Brief", help="newsletter title")
    parser.add_argument("--feeds", help='JSON file with a [{"name": ..., "url": ...}] list')
    parser.add_argument("--logo", default="", help="logo file path or https URL (optional)")
    parser.add_argument("--out", help="output path (default: issues/issue-YYYY-MM-DD.html)")
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    logging.basicConfig(level=logging.INFO, format="%(message)s")

    feeds = json.loads(Path(args.feeds).read_text(encoding="utf-8")) if args.feeds else FEEDS
    until = datetime.now(timezone.utc)
    since = until - timedelta(days=args.days)

    log.info("Fetching %d feeds (last %d days)...", len(feeds), args.days)
    raw_items, errors = collect(feeds, since)
    items = dedupe(raw_items)
    log.info("%d items -> %d after merging duplicate stories", len(raw_items), len(items))

    if not items:
        log.error("No items found. Check your feeds and network.")
        for error in errors:
            log.error("  ! %s", error)
        return 1

    top, sections = build_sections(items, args.max_per_section)
    shown = top + [i for _, group in sections for i in group]
    cve_counts = Counter(cve for item in items for cve in item.cves)
    attach_images(shown, args.images)

    logo_src = resolve_logo(args.logo)
    if logo_src.startswith("data:"):
        log.info(
            "Logo is embedded: fine for browser preview, but Gmail blocks embedded images. "
            "Host the logo and pass its URL to --logo for the email you send."
        )

    out = Path(args.out) if args.out else Path("issues") / f"issue-{until:%Y-%m-%d}.html"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        render_issue(args.title, since, until, top, sections, cve_counts, len(shown), logo_src),
        encoding="utf-8",
    )

    log.info("\nWrote %s (%d stories)", out, len(shown))
    if errors:
        log.warning("\nFeeds that failed (fix the URL or remove them):")
        for error in errors:
            log.warning("  ! %s", error)
    return 0


if __name__ == "__main__":
    sys.exit(main())