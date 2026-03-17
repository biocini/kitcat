#!/usr/bin/env python3
"""
Convert Agda HTML output into a browsable static site.

Agda's --html-highlight=auto produces:
  - .html files for .agda sources (already full HTML)
  - .md files for .lagda.md sources (markdown with <pre class="Agda"> blocks)
  - Agda.css

This script:
  1. Converts .md files to .html (markdown prose + pass-through Agda blocks)
  2. Re-wraps existing .html files in the site template
  3. Generates a module index page
  4. Copies CSS assets
"""

import argparse
import html
import os
import re
import shutil
import sys
from pathlib import Path


def load_template(site_dir: Path) -> str:
    return (site_dir / "template.html").read_text(encoding="utf-8")


def load_css(site_dir: Path) -> str:
    return (site_dir / "style.css").read_text(encoding="utf-8")


# ── Minimal markdown converter ──────────────────────────────
# Handles: headings, paragraphs, links, bold, italic, code
# spans, unordered lists, horizontal rules.  Agda <pre> blocks
# pass through unchanged.

def md_to_html(text: str) -> str:
    """Convert markdown text to HTML, preserving <pre> blocks."""
    # Split on <pre class="Agda"> ... </pre> boundaries
    parts = re.split(r'(<pre class="Agda">.*?</pre>)', text, flags=re.DOTALL)

    result = []
    for part in parts:
        if part.startswith('<pre class="Agda">'):
            result.append(part)
        else:
            result.append(_convert_md_block(part))

    return "\n".join(result)


def _convert_md_block(text: str) -> str:
    """Convert a block of plain markdown to HTML."""
    lines = text.split("\n")
    out = []
    in_list = False
    paragraph = []

    def flush_paragraph():
        if paragraph:
            content = _inline(" ".join(paragraph))
            out.append(f"<p>{content}</p>")
            paragraph.clear()

    def close_list():
        nonlocal in_list
        if in_list:
            out.append("</ul>")
            in_list = False

    for line in lines:
        stripped = line.strip()

        # Blank line
        if not stripped:
            flush_paragraph()
            close_list()
            continue

        # Heading
        m = re.match(r'^(#{1,6})\s+(.*)', stripped)
        if m:
            flush_paragraph()
            close_list()
            level = len(m.group(1))
            raw = m.group(2)
            content = _inline(raw)
            slug = re.sub(r'[^a-z0-9]+', '-', raw.lower()).strip('-')
            out.append(f'<h{level} id="{slug}">{content}</h{level}>')
            continue

        # Horizontal rule
        if re.match(r'^[-*_]{3,}\s*$', stripped):
            flush_paragraph()
            close_list()
            out.append("<hr>")
            continue

        # Unordered list item
        m = re.match(r'^[-*+]\s+(.*)', stripped)
        if m:
            flush_paragraph()
            if not in_list:
                out.append("<ul>")
                in_list = True
            out.append(f"<li>{_inline(m.group(1))}</li>")
            continue

        # Regular text → paragraph
        close_list()
        paragraph.append(stripped)

    flush_paragraph()
    close_list()
    return "\n".join(out)


_SAFE_URL = re.compile(r'^(https?://|/|#|\.\.?/)')


def _make_link(m: re.Match) -> str:
    """Convert a markdown link, sanitizing the URL."""
    text = html.escape(m.group(1))
    url = m.group(2).strip()
    if not _SAFE_URL.match(url):
        return html.escape(m.group(0))
    return f'<a href="{html.escape(url)}">{text}</a>'


def _inline(text: str) -> str:
    """Convert inline markdown: bold, italic, code, links."""
    # Code spans (do first to avoid processing their contents)
    parts = re.split(r'(`[^`]+`)', text)
    result = []
    for part in parts:
        if part.startswith('`') and part.endswith('`'):
            result.append(f'<code>{html.escape(part[1:-1])}</code>')
        else:
            s = part
            # Links: [text](url)
            s = re.sub(r'\[([^\]]+)\]\(([^)]+)\)', _make_link, s)
            # Bold: **text** or __text__
            s = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', s)
            s = re.sub(r'__(.+?)__', r'<strong>\1</strong>', s)
            # Italic: *text* or _text_
            s = re.sub(r'\*(.+?)\*', r'<em>\1</em>', s)
            s = re.sub(r'(?<!\w)_(.+?)_(?!\w)', r'<em>\1</em>', s)
            result.append(s)
    return "".join(result)


# ── Page generation ─────────────────────────────────────────

def render_page(template: str, title: str, body: str, depth: int = 0) -> str:
    """Render a page using the HTML template."""
    prefix = "../" * depth if depth > 0 else ""
    return (
        template
        .replace("{{title}}", html.escape(title))
        .replace("{{body}}", body)
        .replace("{{prefix}}", prefix)
    )


def build_index(modules: list[str], template: str) -> str:
    """Generate the module index page."""
    # Group by top-level namespace
    namespaces: dict[str, list[str]] = {}
    for mod in sorted(modules):
        ns = mod.split(".")[0]
        namespaces.setdefault(ns, []).append(mod)

    body_parts = ['<h1>kitcat</h1>',
                  '<p>Experimental univalent mathematics and '
                  'computer science in Cubical Agda.</p>']

    for ns in sorted(namespaces):
        body_parts.append(f'<h2>{html.escape(ns)}</h2>')
        body_parts.append('<ul class="module-list">')
        for mod in namespaces[ns]:
            href = f"{mod}.html"
            body_parts.append(
                f'<li><a href="{href}">{html.escape(mod)}</a></li>'
            )
        body_parts.append('</ul>')

    return render_page(template, "kitcat — Module Index",
                       "\n".join(body_parts))


# ── Main build pipeline ────────────────────────────────────

def build(agda_dir: Path, out_dir: Path, site_dir: Path):
    template = load_template(site_dir)
    custom_css = load_css(site_dir)

    out_dir.mkdir(parents=True, exist_ok=True)

    # Copy and augment CSS
    agda_css = agda_dir / "Agda.css"
    if agda_css.exists():
        combined = agda_css.read_text(encoding="utf-8") + "\n\n/* kitcat */\n" + custom_css
        (out_dir / "Agda.css").write_text(encoding="utf-8", data=combined)
    else:
        (out_dir / "Agda.css").write_text(encoding="utf-8", data=custom_css)

    modules = []

    # Process .md files (literate Agda → HTML)
    for md_file in sorted(agda_dir.glob("*.md")):
        mod_name = md_file.stem  # e.g. "Core.Type"
        modules.append(mod_name)

        content = md_file.read_text(encoding="utf-8")
        body = md_to_html(content)
        page = render_page(template, mod_name, body)

        (out_dir / f"{mod_name}.html").write_text(encoding="utf-8", data=page)

    # Process .html files (plain Agda — re-wrap in template)
    for html_file in sorted(agda_dir.glob("*.html")):
        mod_name = html_file.stem
        # Skip Agda stdlib files — just copy them
        if mod_name.startswith("Agda."):
            shutil.copy2(html_file, out_dir / html_file.name)
            continue

        modules.append(mod_name)

        content = html_file.read_text(encoding="utf-8")
        # Extract body from existing HTML
        m = re.search(r'<body>(.*?)</body>', content, re.DOTALL)
        body = m.group(1) if m else content
        page = render_page(template, mod_name, body)

        (out_dir / html_file.name).write_text(encoding="utf-8", data=page)

    # Generate index
    index_html = build_index(modules, template)
    (out_dir / "index.html").write_text(encoding="utf-8", data=index_html)

    print(f"Built {len(modules)} module pages + index → {out_dir}")


def main():
    parser = argparse.ArgumentParser(description="Build kitcat HTML site")
    parser.add_argument("agda_dir", type=Path,
                        help="Directory containing Agda HTML output")
    parser.add_argument("out_dir", type=Path,
                        help="Output directory for final site")
    parser.add_argument("--site-dir", type=Path,
                        default=Path(__file__).parent,
                        help="Directory containing template.html and style.css")
    args = parser.parse_args()

    if not args.agda_dir.is_dir():
        print(f"Error: {args.agda_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    build(args.agda_dir, args.out_dir, args.site_dir)


if __name__ == "__main__":
    main()
