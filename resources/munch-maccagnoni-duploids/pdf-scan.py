#!/usr/bin/env python3
r"""Report what a `pdftotext` extraction drops or reorders, from `duploids.pdf`.

Usage:

    python3 pdf-scan.py duploids.pdf
    python3 pdf-scan.py duploids.pdf --no-line-map
    python3 pdf-scan.py duploids.pdf --check

The scanner walks the page tree, decompresses each page content stream,
and tokenizes the path operators while it tracks the CTM. It prints three
reports. Every count in the entry's Files section comes from one of them.

1. Filled circular clusters. The paper draws its composition operator
   U+2299 as a vector path, three near-circular subpaths that share a
   center, so `pdftotext` emits nothing for it. Each cluster is one
   occurrence of the glyph. The report ends with a per-line count, which
   is the Count column of the entry's glyph table.
2. Stroked paths. Every other drawn mark: box edges, inference bars,
   subterm markers, over/underline rules, footnote separators, diagram
   arrows, ditto rules, table rules and cover-page decoration. The report
   ends with a count per category.
3. Interleaved two-column displays. Regions where the extraction leaves a
   display out of reading order. This third report is a candidate list,
   not a closed inventory, and it says so in its own footer.

A row of the first two reports carries the page, the position and the
size in PDF user space, the stroke width, the category, and the
`duploids.pdftext` line that the mark sits on. The first report also
gives the number of filled subpaths it dropped as not near-circular, so
a claim that the document draws no second path glyph is checkable here.

`--check` reads the entry's own `README.md` and compares it against a
fresh run. It reads the headline sentence of each report, all five
columns of the glyph table, the arithmetic that places those glyphs, the
stroked-path table (every count, page set and line reference, ranges
included), the page-6 rule counts and widths, and the
interleaved-display table's ranges with the arithmetic that accounts for
the regions. The glyph table's two content columns go against the fresh
extraction itself, so a retyped cell fails. A few claims the entry
states twice go against each other rather than against the scan, and the
comparison list names those. It exits non-zero on any difference the
script does not declare. `DECLARED_CORRECTIONS` holds the differences
the entry states on purpose, each with its reason and with the patterns
that find its disclosure in the entry. A declared correction that no
longer matches the scan, the entry, or its disclosure is itself a
failure. `EXPECTED_CHECKS` pins the number of comparisons a run makes,
so a claim deleted from the entry fails the run rather than quietly
removing its own test.

The category names are tuned to this document, not to PDFs in general.
Any page-1 vertical stroke becomes "HAL cover-page decoration", any
horizontal stroke wider than 300 points becomes a "Table 1 rule", a
stroke 55 to 58 points wide near x=134.77 becomes a "footnote
separator", and one literal pair of extraction line numbers separates
the §2.2 rules from Proposition 13's subterm markers. Point the script
at another PDF and the geometry stays right, but the names mislead.

Two limits of the PDF reader. It finds objects by scanning the raw bytes
for `N G obj`, so it reads no object stream (`/ObjStm`): a producer that
compresses its page dictionaries yields an empty page list. And the
tokenizer matches a literal string as `\([^)]*\)`, which ends early on
an escaped `\)`. The leaked tail can tokenize as `b` or `f` and inject a
phantom path. This document uses hex strings, so that hazard does not
fire here.

The line map runs `pdftotext` once over the whole document for the line
numbering, then `pdftotext -bbox-layout` once per page for the word
boxes. It aligns the two by text, not by position. The correction patch
keeps the line count and the line order of the extraction, so a line
number here indexes the vendored `duploids.pdftext` too. A `~` suffix
marks a line matched by vertical distance alone, and `-` marks a mark
with no text line within 24 points.

Standard library only. Poppler supplies `pdftotext`. `--no-line-map`
drops the correlation. Then the third report is empty, and two categories
that the line map separates (the over/underline rules of §2.2 and
Proposition 13's subterm markers) collapse into one.
"""

import argparse
import math
import os
import re
import subprocess
import sys
import zlib
from collections import defaultdict

# ---------------------------------------------------------------- PDF objects

OBJ_RE = re.compile(rb"(?:^|[\r\n>])(\d+)\s+(\d+)\s+obj\b")


def load_objects(data):
    """Map object number to its raw body bytes.

    The scan reads the raw file, so an object inside an object stream
    (`/ObjStm`) never appears. A producer that compresses its page
    dictionaries would leave `page_order` with nothing to walk. This
    document stores its page dictionaries uncompressed.
    """
    objects = {}
    for match in OBJ_RE.finditer(data):
        num = int(match.group(1))
        start = match.end()
        end = data.find(b"endobj", start)
        if end < 0:
            continue
        objects[num] = data[start:end]
    return objects


def stream_bytes(body):
    """Decode the stream of one object body, or return None."""
    marker = body.find(b"stream")
    if marker < 0:
        return None
    start = marker + len(b"stream")
    if data_at(body, start) == b"\r":
        start += 1
    if data_at(body, start) == b"\n":
        start += 1
    end = body.find(b"endstream", start)
    raw = body[start:end if end >= 0 else len(body)]
    if b"/FlateDecode" in body[:marker]:
        try:
            return zlib.decompress(raw)
        except zlib.error:
            return zlib.decompressobj().decompress(raw)
    return raw


def data_at(body, index):
    return body[index:index + 1]


def refs(body, key):
    """Every `N 0 R` reference under one dictionary key."""
    match = re.search(re.escape(key.encode()) + rb"\s*(\[[^\]]*\]|\d+\s+\d+\s+R)", body)
    if not match:
        return []
    return [int(n) for n in re.findall(rb"(\d+)\s+\d+\s+R", match.group(1))]


def page_order(objects):
    """The page objects, in document order, by a page-tree walk."""
    root = None
    for body in objects.values():
        if b"/Type" in body and b"/Catalog" in body:
            pages = refs(body, "/Pages")
            if pages:
                root = pages[0]
                break
    order = []
    seen = set()

    def walk(num):
        if num in seen or num not in objects:
            return
        seen.add(num)
        body = objects[num]
        if b"/Type" in body and re.search(rb"/Type\s*/Pages", body):
            for kid in refs(body, "/Kids"):
                walk(kid)
        elif re.search(rb"/Type\s*/Page\b", body):
            order.append(num)

    if root is not None:
        walk(root)
    if not order:
        order = sorted(n for n, b in objects.items() if re.search(rb"/Type\s*/Page\b", b))
    return order


def page_content(objects, page_num):
    """The concatenated content stream of one page."""
    body = objects[page_num]
    chunks = []
    for ref in refs(body, "/Contents"):
        if ref in objects:
            payload = stream_bytes(objects[ref])
            if payload:
                chunks.append(payload)
    return b"\n".join(chunks)


# -------------------------------------------------------------- path scanning

# The literal-string branch `\([^)]*\)` ends at the first `)`, so an
# escaped `\)` inside a literal string leaks its tail to the tokenizer,
# where `b` or `f` would read as a painting operator and add a phantom
# path. This document writes its strings in hex, so no literal string
# reaches the tokenizer at all.
TOKEN_RE = re.compile(rb"(<[^>]*>|\([^)]*\)|/[^\s/\[\]<>()]+|[-+.\d]+|[A-Za-z*'\"]+|\[|\])")

PAINT_STROKE = {"S", "s", "B", "B*", "b", "b*"}
PAINT_FILL = {"f", "F", "f*", "B", "B*", "b", "b*"}
PAINT_ALL = PAINT_STROKE | PAINT_FILL | {"n"}


class Subpath(object):
    def __init__(self):
        self.points = []

    def add(self, point):
        self.points.append(point)

    @property
    def bbox(self):
        xs = [p[0] for p in self.points]
        ys = [p[1] for p in self.points]
        return min(xs), min(ys), max(xs), max(ys)

    @property
    def center(self):
        x0, y0, x1, y1 = self.bbox
        return (x0 + x1) / 2.0, (y0 + y1) / 2.0

    @property
    def size(self):
        x0, y0, x1, y1 = self.bbox
        return x1 - x0, y1 - y0

    def near_circular(self):
        width, height = self.size
        if width <= 0 or height <= 0:
            return False
        if abs(width - height) > 0.35 * max(width, height):
            return False
        cx, cy = self.center
        radius = (width + height) / 4.0
        if radius <= 0:
            return False
        for x, y in self.points:
            distance = math.hypot(x - cx, y - cy)
            if abs(distance - radius) > 0.45 * radius:
                return False
        return True


def apply_ctm(ctm, x, y):
    a, b, c, d, e, f = ctm
    return a * x + c * y + e, b * x + d * y + f


def multiply(m, n):
    a, b, c, d, e, f = m
    a2, b2, c2, d2, e2, f2 = n
    return (
        a * a2 + b * c2,
        a * b2 + b * d2,
        c * a2 + d * c2,
        c * b2 + d * d2,
        e * a2 + f * c2 + e2,
        e * b2 + f * d2 + f2,
    )


def scan_page(content):
    """Every painted path on one page, as (paint, [Subpath, ...], width)."""
    tokens = [t.decode("latin-1") for t in TOKEN_RE.findall(content)]
    ctm = (1.0, 0.0, 0.0, 1.0, 0.0, 0.0)
    stack = []
    width = 1.0
    width_stack = []
    subpaths = []
    current = None
    start = (0.0, 0.0)
    here = (0.0, 0.0)
    operands = []
    paths = []

    def flush(paint):
        if current is not None and current.points:
            subpaths.append(current)
        if subpaths:
            paths.append((paint, list(subpaths), width))

    for token in tokens:
        if re.match(r"^[-+.\d]+$", token):
            try:
                operands.append(float(token))
            except ValueError:
                operands.append(0.0)
            continue
        if token.startswith("/") or token in ("[", "]") or token.startswith("(") or token.startswith("<"):
            continue
        op = token
        if op == "q":
            stack.append(ctm)
            width_stack.append(width)
        elif op == "Q":
            if stack:
                ctm = stack.pop()
            if width_stack:
                width = width_stack.pop()
        elif op == "cm" and len(operands) >= 6:
            ctm = multiply(tuple(operands[-6:]), ctm)
        elif op == "w" and operands:
            width = operands[-1]
        elif op == "m" and len(operands) >= 2:
            if current is not None and current.points:
                subpaths.append(current)
            current = Subpath()
            here = start = apply_ctm(ctm, operands[-2], operands[-1])
            current.add(here)
        elif op == "l" and len(operands) >= 2:
            if current is None:
                current = Subpath()
            here = apply_ctm(ctm, operands[-2], operands[-1])
            current.add(here)
        elif op in ("c", "v", "y") and len(operands) >= 2:
            if current is None:
                current = Subpath()
            count = {"c": 6, "v": 4, "y": 4}[op]
            args = operands[-count:] if len(operands) >= count else operands
            for i in range(0, len(args) - 1, 2):
                current.add(apply_ctm(ctm, args[i], args[i + 1]))
            here = current.points[-1]
        elif op == "re" and len(operands) >= 4:
            if current is not None and current.points:
                subpaths.append(current)
            x, y, w, h = operands[-4:]
            current = Subpath()
            for px, py in ((x, y), (x + w, y), (x + w, y + h), (x, y + h), (x, y)):
                current.add(apply_ctm(ctm, px, py))
            subpaths.append(current)
            current = None
            here = start = apply_ctm(ctm, x, y)
        elif op == "h":
            if current is not None and current.points:
                current.add(start)
        elif op in PAINT_ALL:
            flush(op)
            subpaths = []
            current = None
        operands = []
    return paths


# ----------------------------------------------------------------- clustering

def cluster_filled(records, tolerance=1.0):
    """Group filled near-circular subpaths that share a center."""
    clusters = []
    for page, subpath in records:
        placed = False
        for cluster in clusters:
            if cluster["page"] != page:
                continue
            cx, cy = cluster["center"]
            sx, sy = subpath.center
            if abs(cx - sx) <= tolerance and abs(cy - sy) <= tolerance:
                cluster["members"].append(subpath)
                placed = True
                break
        if not placed:
            clusters.append({"page": page, "center": subpath.center, "members": [subpath]})
    return clusters


# ------------------------------------------------------------- classification

FLAT = 1.0          # a rule thinner than this in one axis counts as a segment
JOIN = 4.0          # how far a box corner may miss, in points


def shape_of(subpath):
    """The geometric kind of one stroked subpath."""
    w, h = subpath.size
    if w > FLAT and h > FLAT:
        return "curve"
    if w <= FLAT and h > FLAT:
        return "vertical"
    if h <= FLAT and w > FLAT:
        return "horizontal"
    return "dot"


def find_boxes(marks):
    """Index the marks that make up a four-sided box.

    The paper draws a box as four separate segments, two horizontal and
    two vertical, with a font character at each corner. A box is a pair
    of horizontal segments of the same width and center, plus two
    vertical segments that stand between them at the two ends.
    """
    horizontals = [i for i, m in enumerate(marks) if m["shape"] == "horizontal"]
    verticals = [i for i, m in enumerate(marks) if m["shape"] == "vertical"]
    used = set()
    boxes = []
    for a in horizontals:
        for b in horizontals:
            if a >= b or a in used or b in used:
                continue
            top, bottom = marks[a], marks[b]
            if top["page"] != bottom["page"]:
                continue
            if abs(top["w"] - bottom["w"]) > JOIN or abs(top["cx"] - bottom["cx"]) > JOIN:
                continue
            low, high = sorted((top["cy"], bottom["cy"]))
            if high - low < 1.0 or high - low > 200.0:
                continue
            sides = []
            for v in verticals:
                side = marks[v]
                if v in used or side["page"] != top["page"]:
                    continue
                if side["y0"] < low - JOIN or side["y1"] > high + JOIN:
                    continue
                if min(abs(side["cx"] - top["x0"]), abs(side["cx"] - top["x1"])) > JOIN:
                    continue
                sides.append(v)
            if len(sides) == 2:
                members = [a, b] + sides
                used.update(members)
                boxes.append(members)
    return boxes


SECTION_2_2_LINES = ("l.300", "l.307")   # the two lines of §2.2 that carry a rule


# --------------------------------------------------- interleaved two-column displays

ROW_SHARE = 0.4     # vertical overlap that puts two text lines on one rendered row
COLUMN_GAP = 5.0    # horizontal gap that starts a new column, in points


def rendered_rows(rows):
    """Group text lines that share a rendered row."""
    groups = []
    for row in sorted(rows, key=lambda r: (r[1], r[3])):
        placed = False
        for group in groups:
            for other in group:
                height = min(row[2] - row[1], other[2] - other[1])
                if min(row[2], other[2]) - max(row[1], other[1]) > ROW_SHARE * height:
                    group.append(row)
                    placed = True
                    break
            if placed:
                break
        if not placed:
            groups.append([row])
    return groups


def columns_of(group):
    """Split one rendered row into columns by horizontal gap."""
    group = sorted(group, key=lambda r: r[3])
    columns = [[group[0]]]
    for row in group[1:]:
        if row[3] > max(r[4] for r in columns[-1]) + COLUMN_GAP:
            columns.append([row])
        else:
            columns[-1].append(row)
    return columns


def interleaved(bands):
    """Every region where the extraction leaves a display out of reading order.

    A rendered row that holds two or more columns reaches the extraction
    as one text line per column. The extraction breaks reading order when
    it puts a line of a later column before a line of an earlier one, or
    when it puts a line of some other row between two lines of this row.
    The detector reports the merged line range of each such region.

    This detector is not a completeness guarantee. It reads the layout
    that `pdftotext` itself computed, so a display that the layout
    analysis reads as one column does not appear here. Treat the output
    as a candidate list to check against page renders, never as a closed
    inventory.
    """
    numbered = set()
    for page in bands:
        numbered.update(row[0] for row in bands[page])
    hits = []
    for page in sorted(bands):
        for group in rendered_rows(bands[page]):
            if len(group) < 2:
                continue
            columns = columns_of(group)
            if len(columns) < 2:
                continue
            lines = sorted(row[0] for row in group)
            between = [n for n in range(lines[0], lines[-1] + 1)
                       if n in numbered and n not in lines]
            per_column = [sorted(row[0] for row in column) for column in columns]
            reordered = any(max(per_column[i]) > min(per_column[i + 1])
                            for i in range(len(per_column) - 1))
            if between or reordered:
                hits.append((page, lines[0], lines[-1], len(columns)))
    regions = []
    for page, first, last, width in sorted(hits):
        if regions and regions[-1][0] == page and first <= regions[-1][2] + 1:
            regions[-1][2] = max(regions[-1][2], last)
            regions[-1][3] = max(regions[-1][3], width)
            regions[-1][4] += 1
        else:
            regions.append([page, first, last, width, 1])
    return regions


def label(mark, boxed):
    """The paper-level name of one stroked mark.

    Each test below reads a geometric signature or the extraction line
    that the mark maps to. A render of the page confirms every name.

    One test needs the line map. The over/underline rules of §2.2 and
    Proposition 13's subterm markers share a stroke width and overlap in
    length, so geometry alone does not separate them. What separates them
    is the text they mark, so the scanner reads the extraction line.
    """
    if boxed:
        return "box edge"
    shape = mark["shape"]
    if shape == "curve":
        return "adjunction-diagram arrow"
    if shape == "vertical":
        if mark["page"] == 1:
            return "HAL cover-page decoration"
        return "figure column separator"
    if mark["lw"] < 2.0:
        return "Definition 3 ditto rule"
    if mark["w"] > 300.0:
        return "Table 1 rule"
    if 55.0 <= mark["w"] <= 58.0 and abs(mark["x0"] - 134.77) < 3.0:
        return "footnote separator"
    if mark["lw"] > 5.0:
        if mark["line"] is None:
            return "short rule, §2.2 or Proposition 13"
        if mark["line"] in SECTION_2_2_LINES:
            return "over/underline rule of §2.2"
        return "Proposition 13 subterm marker"
    return "inference bar"


# -------------------------------------------------------------- the line map

def run(cmd):
    try:
        return subprocess.check_output(cmd, stderr=subprocess.DEVNULL).decode("utf-8", "replace")
    except (OSError, subprocess.CalledProcessError):
        return None


def build_line_map(pdf_path, page_count):
    """The line map, and the extraction lines it numbers.

    The map sends (page, y in PDF user space) to a line number. The
    extraction is `pdftotext <pdf>`, one file for the whole document, and
    the correction patch keeps its line count and its line order. So a
    line number here indexes the vendored `duploids.pdftext` too, and the
    second return value is the uncorrected text of those lines, index
    `N - 1` for line `N`. The self-check reads it to test the glyph
    table's "The extraction reads" column against a fresh extraction.

    One whole-document run of `pdftotext` gives the line numbering, and
    a form feed separates its pages. Then `pdftotext -bbox-layout -f N -l N`
    gives the box of every text line of a page, with its words. The
    scanner aligns the two by text, not by position, so a page whose
    reading order surprises the layout analysis cannot drift the map.
    """
    whole = run(["pdftotext", pdf_path, "-"])
    if whole is None:
        return None, None
    page_text = whole.split("\f")
    offset = 0
    bands = {}
    lines = []
    for page in range(1, page_count + 1):
        if page > len(page_text):
            break
        text_lines = page_text[page - 1].split("\n")
        if text_lines and text_lines[-1] == "":
            text_lines.pop()
        xml_text = run(["pdftotext", "-bbox-layout", "-f", str(page), "-l", str(page),
                        pdf_path, "-"])
        if xml_text is None:
            return None, None
        boxes = parse_bbox(xml_text)
        rows = []
        cursor = 0
        for number, text in enumerate(text_lines, start=1):
            key = "".join(text.split())
            if not key:
                continue
            used = align(key, boxes, cursor)
            if not used:
                continue
            taken = [boxes[i] for i in used]
            words = []
            for box in taken:
                words.extend(box[5])
            rows.append((
                offset + number,
                min(b[1] for b in taken),
                max(b[3] for b in taken),
                min(b[0] for b in taken),
                max(b[2] for b in taken),
                words,
            ))
            cursor = used[-1] + 1
        bands[page] = rows
        lines.extend(text_lines)
        offset += len(text_lines)
    return bands, lines


def align(key, boxes, cursor, lookahead=8):
    """The layout lines that make up one extraction line, or None.

    The layout analysis and the plain extraction agree on reading order
    but not always on line breaks. A hyphenated word can break a rendered
    row that the plain extraction keeps whole, so one extraction line can
    cover several layout lines. The matcher joins layout lines until the
    text agrees, and it drops a trailing hyphen at each join.
    """
    for probe in range(cursor, min(cursor + lookahead, len(boxes))):
        head = boxes[probe][4]
        if not head:
            continue
        if head == key:
            return [probe]
        stem = head.rstrip("-")
        if len(stem) < 4 or not key.startswith(stem):
            continue
        used = [probe]
        acc = stem
        index = probe + 1
        while acc != key and index < len(boxes):
            tail = boxes[index][4]
            if acc + tail == key:
                used.append(index)
                acc = key
                break
            if key.startswith(acc + tail.rstrip("-")) and tail:
                used.append(index)
                acc += tail.rstrip("-")
                index += 1
                continue
            break
        if acc == key:
            return used
    return None


BBOX_LINE_RE = re.compile(
    r'<line xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">(.*?)</line>',
    re.S)
BBOX_WORD_RE = re.compile(
    r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>')


def parse_bbox(xml_text):
    """Every layout line, in reading order, with its words.

    A row is (xMin, yMin, xMax, yMax, text, words), and a word is
    (xMin, yMin, xMax, yMax). The text drops all whitespace, so a
    subscript that the layout splits into two words still matches the
    plain extraction.
    """
    rows = []
    for match in BBOX_LINE_RE.finditer(xml_text):
        words = []
        text = []
        for word in BBOX_WORD_RE.finditer(match.group(5)):
            words.append(tuple(float(word.group(i)) for i in (1, 2, 3, 4)))
            text.append(unescape(word.group(5)))
        rows.append((float(match.group(1)), float(match.group(2)),
                     float(match.group(3)), float(match.group(4)),
                     "".join("".join(text).split()), words))
    return rows


def unescape(text):
    for entity, char in (("&amp;", "&"), ("&lt;", "<"), ("&gt;", ">"),
                         ("&quot;", '"'), ("&apos;", "'")):
        text = text.replace(entity, char)
    return text


def nearest_line(bands, page, x0, x1, y_user, media_height, mode="left", slack=2.0):
    """The extraction line that a mark spanning [x0, x1] at y sits on.

    A rendered row can reach the extraction as several text lines, one
    per column, so the vertical band alone does not decide. Two rules
    settle the column.

    `mode="left"` suits the composition glyph. A binary operator stands
    between its operands, and the entry writes it at the end of the line
    that carries its left operand, so the scanner takes the line whose
    text ends nearest to the left of the mark.

    `mode="overlap"` suits a drawn rule. A rule sits over, under or
    beside the text it marks, and an overline sits above its own line's
    band, so a band test alone reads it onto the line above. The scanner
    instead takes the lines whose horizontal extent the rule overlaps,
    then the one whose band is vertically nearest.

    A `~` suffix marks a match outside every band, and `-` marks no text
    line within 24 points.
    """
    rows = bands.get(page) if bands else None
    if not rows:
        return "-"
    y_top = media_height - y_user
    if mode == "left":
        inside = [r for r in rows if r[1] - slack <= y_top <= r[2] + slack]
        if not inside:
            return fallback(rows, y_top)
        holding = [r for r in inside if r[3] <= x0 <= r[4]]
        if holding:
            return "l.%d" % holding[0][0]
        before = [r for r in inside if r[4] <= x0]
        if before:
            return "l.%d" % max(before, key=lambda r: r[4])[0]
        return "l.%d" % min(inside, key=lambda r: r[3])[0]
    span = max(x1 - x0, 0.5)
    candidates = []
    for row in rows:
        covered = 0.0
        gap = None
        for wx0, wy0, wx1, wy1 in row[5]:
            overlap = min(x1, wx1) - max(x0, wx0)
            if overlap <= 0:
                continue
            covered += overlap
            if y_top < wy0:
                here = wy0 - y_top
            elif y_top > wy1:
                here = y_top - wy1
            else:
                here = 0.0
            gap = here if gap is None else min(gap, here)
        if gap is None or gap > 14.0:
            continue
        coverage = min(covered / span, 1.0)
        candidates.append((-round(coverage, 1), round(gap, 2), row[0]))
    if candidates:
        candidates.sort()
        return "l.%d" % candidates[0][2]
    return fallback(rows, y_top)


def fallback(rows, y_top):
    """The nearest line by vertical distance alone, or `-`."""
    best = min(rows, key=lambda r: min(abs(y_top - r[1]), abs(y_top - r[2])))
    gap = min(abs(y_top - best[1]), abs(y_top - best[2]))
    if gap > 24.0:
        return "-"
    return "l.%d~" % best[0]


# ------------------------------------------------------------------- reporting

def line_key(line):
    """Sort an `l.NNN` label by its number, with `-` last."""
    match = re.match(r"l\.(\d+)", line)
    return int(match.group(1)) if match else 10 ** 9


def line_number(line):
    """The integer of an `l.NNN` label, with any `~` dropped, or None."""
    if not line:
        return None
    match = re.match(r"l\.(\d+)", line)
    return int(match.group(1)) if match else None


def media_box(objects, page_num):
    body = objects[page_num]
    match = re.search(rb"/MediaBox\s*\[([^\]]*)\]", body)
    if not match:
        return 595.28, 841.89
    parts = [float(v) for v in re.findall(rb"[-+.\d]+", match.group(1))]
    return parts[2] - parts[0], parts[3] - parts[1]


def measure(pdf_path, use_line_map=True):
    """Every number the reports and the self-check read, from one scan."""
    with open(pdf_path, "rb") as handle:
        data = handle.read()
    objects = load_objects(data)
    pages = page_order(objects)
    _, media_height = media_box(objects, pages[0])

    filled = []
    stroked = []
    dropped = 0
    for index, page_num in enumerate(pages, start=1):
        content = page_content(objects, page_num)
        for paint, subpaths, width in scan_page(content):
            for subpath in subpaths:
                circular = paint in PAINT_FILL and subpath.near_circular()
                if circular:
                    filled.append((index, subpath))
                elif paint in PAINT_STROKE:
                    stroked.append((index, subpath, width))
                elif paint in PAINT_FILL:
                    dropped += 1

    bands = None
    lines = None
    if use_line_map:
        bands, lines = build_line_map(pdf_path, len(pages))
        if bands is None:
            sys.stderr.write("warning: pdftotext unavailable, the line column reads '-'\n")

    clusters = cluster_filled(filled)
    clusters.sort(key=lambda c: (c["page"], -c["center"][1], c["center"][0]))
    per_line = defaultdict(int)
    per_page = defaultdict(int)
    sizes = defaultdict(int)
    for cluster in clusters:
        cx, cy = cluster["center"]
        cluster["line"] = nearest_line(bands, cluster["page"], cx, cx, cy,
                                       media_height, "left")
        per_line[(cluster["page"], cluster["line"])] += 1
        per_page[cluster["page"]] += 1
        sizes[len(cluster["members"])] += 1

    marks = []
    for page, subpath, width in stroked:
        cx, cy = subpath.center
        w, h = subpath.size
        x0, y0, x1, y1 = subpath.bbox
        marks.append({
            "page": page, "cx": cx, "cy": cy, "w": w, "h": h, "lw": width,
            "x0": x0, "x1": x1, "y0": y0, "y1": y1,
            "shape": shape_of(subpath),
        })
    for mark in marks:
        mark["line"] = None if bands is None else nearest_line(
            bands, mark["page"], mark["x0"], mark["x1"], mark["cy"],
            media_height, "overlap")
    boxed = set()
    for members in find_boxes(marks):
        boxed.update(members)
    counts = defaultdict(int)
    pages_of = defaultdict(set)
    lines_of = defaultdict(set)
    for index, mark in enumerate(marks):
        mark["label"] = label(mark, index in boxed)
        counts[mark["label"]] += 1
        pages_of[mark["label"]].add(mark["page"])
        number = line_number(mark["line"])
        if number is not None:
            lines_of[mark["label"]].add(number)

    return {
        "pages": len(pages),
        "clusters": clusters,
        "cluster_sizes": dict(sizes),
        "cluster_per_line": dict(per_line),
        "cluster_per_page": dict(per_page),
        "dropped_fills": dropped,
        "marks": marks,
        "boxes": len(boxed) // 4,
        "loose": len(marks) - len(boxed),
        "counts": dict(counts),
        "pages_of": dict(pages_of),
        "lines_of": dict(lines_of),
        "bands": bands,
        "lines": lines,
        "regions": interleaved(bands) if bands else [],
    }


def report(m):
    """Print the three reports."""
    print("== Filled circular clusters: the U+2299 composition glyph ==")
    print("%-5s %-9s %-9s %-9s %s" % ("page", "x", "y", "subpaths", "line"))
    for cluster in m["clusters"]:
        cx, cy = cluster["center"]
        print("%-5d %-9.2f %-9.2f %-9d %s" % (
            cluster["page"], cx, cy, len(cluster["members"]), cluster["line"]))
    print("")
    print("clusters: %d" % len(m["clusters"]))
    print("subpaths per cluster: %s" % ", ".join(
        "%d cluster(s) of %d" % (count, size)
        for size, count in sorted(m["cluster_sizes"].items())))
    print("per page: %s" % ", ".join(
        "%d (%d)" % (p, m["cluster_per_page"][p]) for p in sorted(m["cluster_per_page"])))
    print("filled subpaths dropped as not near-circular: %d" % m["dropped_fills"])
    print("")
    print("per extraction line:")
    print("  %-10s %-6s %s" % ("line", "page", "count"))
    per_line = m["cluster_per_line"]
    for (page, line) in sorted(per_line, key=lambda k: line_key(k[1])):
        print("  %-10s %-6d %d" % (line, page, per_line[(page, line)]))
    print("  %-10s %-6s %d" % ("total", "", sum(per_line.values())))
    print("")

    marks = m["marks"]
    order = sorted(range(len(marks)), key=lambda i: (marks[i]["page"], -marks[i]["cy"],
                                                     marks[i]["cx"]))
    print("== Stroked paths ==")
    print("%-5s %-9s %-9s %-8s %-8s %-7s %-30s %s" % (
        "page", "x", "y", "width", "height", "lw", "category", "line"))
    for index in order:
        mark = marks[index]
        print("%-5d %-9.2f %-9.2f %-8.2f %-8.2f %-7.3f %-30s %s" % (
            mark["page"], mark["cx"], mark["cy"], mark["w"], mark["h"], mark["lw"],
            mark["label"], mark["line"] or "-"))
    print("")
    print("stroked paths: %d, in %d boxes and %d loose marks" % (
        len(marks), m["boxes"], m["loose"]))
    counts = m["counts"]
    print("%-30s %5s   %s" % ("category", "count", "pages"))
    for category in sorted(counts, key=lambda c: (-counts[c], c)):
        print("%-30s %5d   %s" % (
            category, counts[category],
            ", ".join(str(p) for p in sorted(m["pages_of"][category]))))
    print("%-30s %5d" % ("total", sum(counts.values())))
    print("")

    print("== Interleaved two-column displays (candidates) ==")
    if m["bands"] is None:
        print("the line map is off, so this report is empty")
        return
    print("%-5s %-14s %-9s %s" % ("page", "range", "columns", "rendered rows"))
    for page, first, last, width, count in m["regions"]:
        print("%-5d %-14s %-9d %d" % (page, "l.%d-%d" % (first, last), width, count))
    print("")
    print("regions: %d" % len(m["regions"]))
    print("This is a candidate list, not a closed inventory. Check each")
    print("region against a render of its page.")


# ------------------------------------------------------------------ self-check

ENTRY_CATEGORY = {
    "box edges around a display": "box edge",
    "inference bars": "inference bar",
    "Proposition 13's subterm markers": "Proposition 13 subterm marker",
    "the over/underline of §2.2": "over/underline rule of §2.2",
    "footnote separators": "footnote separator",
    "adjunction-diagram arrows": "adjunction-diagram arrow",
    "Definition 3's ditto rules": "Definition 3 ditto rule",
    "Table 1's rules": "Table 1 rule",
    "figure column separators": "figure column separator",
    "the HAL cover-page rule": "HAL cover-page decoration",
}

# Where the entry publishes a line number the scan does not produce, the
# difference is declared here with its reason, and the entry says the
# same thing in prose. An undeclared difference fails the check. So does
# a declared one that no longer matches the scan or the entry.
#
# This is the one place where a green run and a withheld correction could
# coexist, so `disclosed` and `uncertain` pin the entry's prose too. Each
# is a pattern the entry has to carry. `disclosed` names the line the
# scan produces and the line the entry publishes, in that order.
# `uncertain` names the lines the scan marks with `~`. A pattern that
# finds nothing fails the check, so the disclosure cannot vanish in
# silence.
DECLARED_CORRECTIONS = {
    "Definition 3 ditto rule": {
        "scan": {247, 250, 252},
        "entry": {249, 250, 252},
        "why": ("the first rule sits in the horizontal gap between the row"
                " label and the row text, which the line map does not cover"),
        "disclosed": (r"A fresh run puts Definition 3's first ditto rule at"
                      r" `l\.(\d+)`\. The rule belongs to the row whose text"
                      r" is `l\.(\d+)`"),
        "uncertain": (r"marks the other two ditto rules `l\.(\d+)~` and"
                      r" `l\.(\d+)~`"),
    },
}

# The number of results one `--check` run produces against an entry that
# matches the scan. A deleted claim removes its own comparison, so without
# this pin the run would shrink in silence and still exit 0. Raise or lower
# it whenever a check is added or removed.
EXPECTED_CHECKS = 90

PAGES_RE = re.compile(r"PDF pages?\s+(\d+(?:(?:,\s*|\s+and\s+)\d+)*)")
GLYPH_ROW_RE = re.compile(
    r"^\|\s*`l\.(\d+)`\s*\|\s*`([^|]*)`\s*\|\s*`([^|]*)`\s*\|"
    r"\s*(\d+)\s*\|\s*(\d+)\s*\|\s*$")
STROKE_ROW_RE = re.compile(r"^\|\s*([^|]+?)\s*\|\s*(\d+)\s*\|\s*([^|]*?)\s*\|\s*[^|]*\|\s*$")
DISPLAY_ROW_RE = re.compile(r"^\|\s*`l\.(\d+)-(\d+)`\s*\|\s*[^|]*\|\s*([^|]*?)\s*\|\s*$")

NUMBER_WORDS = {
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6,
    "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11,
    "twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
    "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19,
    "twenty": 20,
}


GLYPH = "⊙"


def numbers(text):
    return [int(n) for n in re.findall(r"\d+", text)]


def squeeze(text):
    """The text with every run of whitespace removed."""
    return "".join(text.split())


def count_word(text):
    """The integer that a digit string or an English count word names."""
    key = text.strip().lower()
    if key.isdigit():
        return int(key)
    return NUMBER_WORDS.get(key, key)


def read_entry(path):
    """The entry's published counts, parsed from its Markdown."""
    with open(path, encoding="utf-8") as handle:
        text = handle.read()
    flat = " ".join(text.split())
    entry = {"prose": flat, "glyph_rows": [], "stroke_rows": [],
             "display_rows": []}

    for row in text.splitlines():
        match = GLYPH_ROW_RE.match(row)
        if match:
            entry["glyph_rows"].append({
                "line": int(match.group(1)),
                "reads": match.group(2),
                "writes": match.group(3),
                "page": int(match.group(4)),
                "count": int(match.group(5)),
            })

    in_table = False
    for row in text.splitlines():
        if row.startswith("| Kind | Strokes |"):
            in_table = True
            continue
        if in_table:
            if not row.startswith("|"):
                break
            if set(row) <= set("| -"):
                continue
            match = STROKE_ROW_RE.match(row)
            if match:
                entry["stroke_rows"].append(
                    (match.group(1), int(match.group(2)), match.group(3)))

    in_table = False
    for row in text.splitlines():
        if row.startswith("| Range | The display |"):
            in_table = True
            continue
        if in_table:
            if not row.startswith("|"):
                break
            if set(row) <= set("| -"):
                continue
            match = DISPLAY_ROW_RE.match(row)
            if match:
                entry["display_rows"].append(
                    (int(match.group(1)), int(match.group(2)), match.group(3)))
    return entry


def check(m, entry):
    """Compare the entry against the scan. Return a list of results."""
    out = []

    def ok(what):
        out.append(("ok", what, ""))

    def fail(what, said, found):
        out.append(("FAIL", what, "entry %s, scan %s" % (said, found)))

    def note(what, why):
        out.append(("declared", what, why))

    def compare(what, said, found):
        if said == found:
            ok(what)
        else:
            fail(what, said, found)

    flat = entry["prose"]
    regions = [(first, last) for _, first, last, _, _ in m["regions"]]

    match = re.search(r"draws that path exactly (\d+) times", flat)
    if match:
        compare("glyph occurrences in prose",
                int(match.group(1)), len(m["clusters"]))
    else:
        fail("glyph occurrences in prose", "no sentence found",
             len(m["clusters"]))

    match = re.search(r"finds (\d+) such clusters, on PDF pages ([^.]*)\.", flat)
    if match:
        compare("glyph clusters", int(match.group(1)), len(m["clusters"]))
        said = dict((int(p), int(c))
                    for p, c in re.findall(r"(\d+) \((\d+)\)", match.group(2)))
        compare("glyph clusters per page", said, m["cluster_per_page"])
    else:
        fail("glyph clusters", "no sentence found", len(m["clusters"]))

    match = re.search(r"and it sums to (\d+)\.", flat)
    if match:
        compare("glyph table total",
                int(match.group(1)), sum(m["cluster_per_line"].values()))

    match = re.search(
        r"Every cluster holds (\w+) subpaths, and no cluster holds any other"
        r" number", flat)
    if match:
        compare("subpaths per cluster",
                {count_word(match.group(1)): len(m["clusters"])},
                m["cluster_sizes"])
    else:
        fail("subpaths per cluster", "no sentence found", m["cluster_sizes"])

    glyph_rows = entry["glyph_rows"]
    said = dict(((row["page"], row["line"]), row["count"]) for row in glyph_rows)
    found = dict(((page, line_number(line)), count)
                 for (page, line), count in m["cluster_per_line"].items())
    if said == found:
        ok("glyph table, %d rows" % len(said))
    else:
        for key in sorted(set(said) | set(found)):
            if said.get(key) != found.get(key):
                fail("glyph row page %d l.%s" % key,
                     said.get(key, "absent"), found.get(key, "absent"))

    # The two content columns. The extraction column must be text a fresh
    # `pdftotext` puts on that line. The patch column must be the same
    # text with the glyph inserted and nothing else changed, and it must
    # carry as many glyphs as the Count cell claims. Whitespace is
    # ignored, because a patch hunk may consume a space beside a glyph.
    lines = m["lines"]
    if lines is None:
        fail("glyph table, the extraction column",
             "the line map is off", "no extraction to read")
    else:
        compare("glyph table, the extraction column against a fresh extraction",
                [row["line"] for row in glyph_rows
                 if row["line"] > len(lines)
                 or squeeze(row["reads"]) not in squeeze(lines[row["line"] - 1])],
                [])
    compare("glyph table, the patch column against the extraction column",
            [row["line"] for row in glyph_rows
             if squeeze(row["writes"]).replace(GLYPH, "") != squeeze(row["reads"])],
            [])
    compare("glyph table, the count column against the patch column",
            [row["line"] for row in glyph_rows
             if row["writes"].count(GLYPH) != row["count"]],
            [])

    trailing = [row for row in glyph_rows if row["writes"].rstrip().endswith(GLYPH)]
    glyphs = sum(row["count"] for row in glyph_rows)
    match = re.search(r"(\w+) of the (\d+) fall at a display that", flat)
    if match:
        compare("glyph occurrences at a broken display",
                count_word(match.group(1)), len(trailing))
        compare("the glyph total in the placement sentence",
                int(match.group(2)), glyphs)
    else:
        fail("glyph occurrences at a broken display", "no sentence found",
             len(trailing))

    # A line reference carries a period, so a sentence that lists several
    # of them ends at the first period that a space follows.
    match = re.search(r"(\w+) lines therefore end in `⊙`: (.*?)\.(?=\s)", flat)
    if match:
        compare("lines that end in the glyph",
                count_word(match.group(1)), len(trailing))
        compare("the lines that end in the glyph",
                set(int(n) for n in re.findall(r"`l\.(\d+)`", match.group(2))),
                set(row["line"] for row in trailing))
    else:
        fail("lines that end in the glyph", "no sentence found", len(trailing))

    inline = glyphs - len(trailing)
    match = re.search(r"writes the other (\d+) inside a line", flat)
    if match:
        compare("glyph occurrences inside a line", int(match.group(1)), inline)
    else:
        fail("glyph occurrences inside a line", "no sentence found", inline)

    operator_named = 0
    match = re.search(
        r"(\w+) of those name the operator rather than apply it, so they have"
        r" no operands at all: (.*?)\.(?=\s)", flat)
    if match:
        per_line = dict((int(line), count_word(word))
                        for word, line in re.findall(r"(\w+) at `l\.(\d+)`",
                                                     match.group(2)))
        operator_named = sum(v for v in per_line.values() if isinstance(v, int))
        compare("glyph occurrences that name the operator",
                count_word(match.group(1)), operator_named)
        compare("the lines that name the operator", per_line,
                dict((line, said.get((page, line)))
                     for (page, line) in said if line in per_line))
    else:
        fail("glyph occurrences that name the operator", "no sentence found",
             "two lines expected")

    opening = 0
    match = re.search(r"(\w+) more, the first `⊙` on `l\.(\d+)`, opens the group",
                      flat)
    if match:
        value = count_word(match.group(1))
        opening = value if isinstance(value, int) else 0
    match = re.search(r"The remaining (\d+) carry both operands", flat)
    if match:
        compare("glyph occurrences with both operands on the line",
                int(match.group(1)), inline - operator_named - opening)
    else:
        fail("glyph occurrences with both operands on the line",
             "no sentence found", inline - operator_named - opening)

    match = re.search(
        r"(\w+) of the (\d+) sit on `l\.(\d+)` and `l\.(\d+)`, beside a"
        r" trailing `⊙`", flat)
    if match:
        pair = [int(match.group(3)), int(match.group(4))]
        beside = sum(row["count"] - 1 for row in trailing
                     if row["line"] in pair)
        compare("glyph occurrences beside a trailing glyph",
                count_word(match.group(1)), beside)
        compare("the restated count of occurrences with both operands",
                int(match.group(2)), inline - operator_named - opening)
    else:
        fail("glyph occurrences beside a trailing glyph", "no sentence found",
             "two lines expected")

    if "finds no second path-drawn character" in flat:
        compare("filled subpaths dropped as not near-circular",
                0, m["dropped_fills"])

    match = re.search(r"Besides the (\d+) `⊙` clusters", flat)
    if match:
        compare("the restated glyph total", int(match.group(1)), glyphs)
    else:
        fail("the restated glyph total", "no sentence found", glyphs)

    match = re.search(r"finds (\d+)\s*stroked paths over all (\d+) page content streams",
                      flat)
    if match:
        compare("stroked paths", int(match.group(1)), len(m["marks"]))
        compare("pages scanned", int(match.group(2)), m["pages"])
    else:
        fail("stroked paths", "no sentence found", len(m["marks"]))

    match = re.search(r"accounts for all (\d+), and it reproduces", flat)
    if match:
        compare("the restated stroked-path total",
                int(match.group(1)), len(m["marks"]))
    else:
        fail("the restated stroked-path total", "no sentence found",
             len(m["marks"]))

    page6 = [mark for mark in m["marks"] if mark["page"] == 6]
    rules = [mark for mark in page6
             if mark["label"] == "over/underline rule of §2.2"]
    rule_lines = m["lines_of"].get("over/underline rule of §2.2", set())

    match = re.search(r"(\w+) such rules fall on PDF page 6", flat)
    if match:
        compare("page 6 rules in the patch section",
                count_word(match.group(1)), len(rules))
    else:
        fail("page 6 rules in the patch section", "no sentence found",
             len(rules))

    # A group rule spans two characters, so it is wider than a
    # single-character one. The two widest are the group rules.
    spans = sorted(round(mark["w"], 1) for mark in rules)
    group = [w for w in spans if spans and w == spans[-1]]
    match = re.search(
        r"(\w+) of the (\w+) rules span a group, so the (\w+) drawn rules"
        r" become (\w+) combining characters, on (\w+) lines", flat)
    if match:
        compare("page 6 group rules", count_word(match.group(1)), len(group))
        compare("page 6 rules the group sentence counts",
                count_word(match.group(2)), len(rules))
        compare("page 6 drawn rules the group sentence counts",
                count_word(match.group(3)), len(rules))
        compare("page 6 combining characters",
                count_word(match.group(4)),
                len(rules) - len(group) + 2 * len(group))
        compare("page 6 lines the rules fall on",
                count_word(match.group(5)), len(rule_lines))
    else:
        fail("page 6 group rules", "no sentence found", len(group))

    match = re.search(
        r"finds (\w+) stroked paths on that page: these (\w+), plus the (\w+)"
        r" edges of the box", flat)
    if match:
        compare("page 6 stroked paths", count_word(match.group(1)), len(page6))
        compare("page 6 over/underline rules",
                count_word(match.group(2)), len(rules))
        compare("page 6 box edges",
                count_word(match.group(3)), len(page6) - len(rules))
    else:
        fail("page 6 stroked paths", "no sentence found", len(page6))

    widths = sorted(round(mark["w"], 1) for mark in rules)
    match = re.search(
        r"The two group rules measure ([\d.]+) points against ([\d.]+) to"
        r" ([\d.]+) for the four single-character rules", flat)
    if match and len(widths) == 6:
        compare("page 6 group rule width",
                [float(match.group(1))] * 2, widths[-2:])
        compare("page 6 single-character rule widths",
                [float(match.group(2)), float(match.group(3))],
                [widths[0], widths[-3]])
    else:
        fail("page 6 rule widths", "no sentence found", widths)

    seen = set()
    for kind, count, where in entry["stroke_rows"]:
        category = ENTRY_CATEGORY.get(kind)
        if category is None:
            fail("stroked category name", kind, "not a scan category")
            continue
        seen.add(category)
        compare("stroked count, %s" % category, count, m["counts"].get(category, 0))
        pages = PAGES_RE.search(where)
        if pages:
            compare("stroked pages, %s" % category,
                    set(numbers(pages.group(1))), m["pages_of"].get(category, set()))
        boxes = re.search(r"(\d+) boxes", where)
        if boxes:
            compare("boxes", int(boxes.group(1)), m["boxes"])
        ranged = re.search(r"`l\.(\d+)-(\d+)`", where)
        if ranged:
            # A range names the display the marks sit in, not their own
            # first and last line. So the test is containment, plus
            # membership in the third report's region list.
            first, last = int(ranged.group(1)), int(ranged.group(2))
            found = m["lines_of"].get(category, set())
            if found and first <= min(found) and max(found) <= last:
                ok("stroked line range, %s" % category)
            else:
                fail("stroked line range, %s" % category,
                     "l.%d-%d" % (first, last), "lines %s" % sorted(found))
            compare("stroked line range is a scan region, %s" % category,
                    (first, last) in regions, True)
            continue
        said = set(int(n) for n in re.findall(r"`l\.(\d+)`", where))
        if not said:
            continue
        found = m["lines_of"].get(category, set())
        declared = DECLARED_CORRECTIONS.get(category)
        if said == found:
            if declared:
                fail("declared correction, %s" % category,
                     "a difference from the scan", "the two now agree")
            else:
                ok("stroked lines, %s" % category)
        elif declared and declared["entry"] == said and declared["scan"] == found:
            note("stroked lines, %s" % category, declared["why"])
        else:
            fail("stroked lines, %s" % category, sorted(said), sorted(found))
    for category in sorted(set(m["counts"]) - seen):
        fail("stroked category", "no row", category)

    # Every declared correction has to reach the reader as prose.
    match = re.search(r"(\w+) differences? (?:is|are) deliberate", flat)
    if match:
        compare("the deliberate differences the entry states",
                count_word(match.group(1)), len(DECLARED_CORRECTIONS))
    else:
        fail("the deliberate differences the entry states", "no sentence found",
             len(DECLARED_CORRECTIONS))

    for category, declared in sorted(DECLARED_CORRECTIONS.items()):
        scan_only = sorted(declared["scan"] - declared["entry"])
        entry_only = sorted(declared["entry"] - declared["scan"])
        match = re.search(declared["disclosed"], flat)
        if match:
            compare("the entry discloses the correction, %s" % category,
                    [int(n) for n in match.groups()], scan_only + entry_only)
        else:
            fail("the entry discloses the correction, %s" % category,
                 "no sentence found", scan_only + entry_only)
        match = re.search(declared["uncertain"], flat)
        if match:
            compare("the entry names the uncertain lines, %s" % category,
                    set(int(n) for n in match.groups()),
                    declared["scan"] & declared["entry"])
        else:
            fail("the entry names the uncertain lines, %s" % category,
                 "no sentence found",
                 sorted(declared["scan"] & declared["entry"]))

    match = re.search(
        r"finds (\d+) regions where the extraction leaves a display out of"
        r" reading order, over PDF pages ([^.]*)\.", flat)
    if match:
        compare("interleaved regions", int(match.group(1)), len(m["regions"]))
        compare("interleaved region pages",
                set(numbers(match.group(2))),
                set(region[0] for region in m["regions"]))
    else:
        fail("interleaved regions", "no sentence found", len(m["regions"]))

    rows = entry["display_rows"]

    # No scan can say whether a digest reads a range, so the third column
    # is an editorial judgment. What the check reads is the entry against
    # itself: the prose that counts the "yes" rows against the rows.
    match = re.search(r'read the (\w+) ranges the table marks "yes"', flat)
    if match:
        compare("interleaved rows marked yes", count_word(match.group(1)),
                len([row for row in rows if row[2].startswith("yes")]))
    else:
        fail("interleaved rows marked yes", "no sentence found",
             len([row for row in rows if row[2].startswith("yes")]))

    covered = set()
    for first, last, _ in rows:
        inside = set(r for r in regions if first <= r[0] and r[1] <= last)
        covered |= inside
        compare("interleaved row l.%d-%d holds a region" % (first, last),
                bool(inside), True)
    rest = [r for r in regions if r not in covered]

    match = re.search(
        r"The (\w+) rows cover (\w+) of the script's (\d+) regions", flat)
    if match:
        compare("interleaved table rows", count_word(match.group(1)), len(rows))
        compare("regions the table covers",
                count_word(match.group(2)), len(covered))
        compare("regions in the third report",
                int(match.group(3)), len(regions))
    else:
        fail("interleaved table coverage", "no sentence found", len(covered))

    match = re.search(
        r"So `l\.(\d+)-(\d+)` covers the script's `l\.(\d+)-(\d+)` and"
        r" `l\.(\d+)-(\d+)`, and `l\.(\d+)-(\d+)` covers its `l\.(\d+)-(\d+)`"
        r" and `l\.(\d+)-(\d+)`\.", flat)
    if match:
        edges = [int(v) for v in match.groups()]
        named = [(edges[i], edges[i + 1]) for i in range(0, len(edges), 2)]
        for whole in (named[0], named[3]):
            compare("split display l.%d-%d is a table row" % whole,
                    whole in set((a, b) for a, b, _ in rows), True)
        for part in named[1:3] + named[4:]:
            compare("split region l.%d-%d is a scan region" % part,
                    part in regions, True)
    else:
        fail("split displays", "no sentence found", "two expected")

    match = re.search(
        r"The other (\w+) regions carry no mathematics a digest reads\.(.*?)"
        r"Proposition 13's proof chain \((\d+)\)", flat)
    if match:
        compare("regions no digest reads",
                count_word(match.group(1)), len(rest))
        parts = numbers(" ".join(re.findall(r"\((\d+)\)", match.group(2))))
        compare("the breakdown of those regions",
                sum(parts) + int(match.group(3)), len(rest))
    else:
        fail("regions no digest reads", "no sentence found", len(rest))

    match = re.search(
        r"also loses (\w+) drawn inference bars, (\w+) per derivation", flat)
    if match:
        bars = count_word(match.group(1))
        per = count_word(match.group(2))
        compare("inference bars in prose",
                bars, m["counts"].get("inference bar", 0))
        compare("inference bars over two derivations",
                bars, per * 2 if isinstance(per, int) else per)
    else:
        fail("inference bars in prose", "no sentence found",
             m["counts"].get("inference bar", 0))

    match = re.search(r"A clean run makes (\d+) comparisons", flat)
    if match:
        compare("the comparison count the entry publishes",
                int(match.group(1)), EXPECTED_CHECKS)
    else:
        fail("the comparison count the entry publishes", "no sentence found",
             EXPECTED_CHECKS)

    total = len(out) + 1
    if total == EXPECTED_CHECKS:
        ok("check count, %d" % total)
    else:
        out.append(("FAIL", "check count",
                    "ran %d, this script expects %d" % (total, EXPECTED_CHECKS)))

    return out


def main():
    parser = argparse.ArgumentParser(
        description="Inventory the drawn paths of duploids.pdf. The category"
                    " names are tuned to that document and mislabel any other.")
    parser.add_argument("pdf", help="the PDF to scan")
    parser.add_argument("--no-line-map", action="store_true",
                        help="skip the pdftotext correlation")
    parser.add_argument("--check", action="store_true",
                        help="compare the entry README against a fresh scan")
    parser.add_argument("--readme", default=None,
                        help="the entry README to check (default: beside this script)")
    args = parser.parse_args()

    m = measure(args.pdf, not args.no_line_map)

    if not args.check:
        report(m)
        return 0

    path = args.readme
    if path is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "README.md")
    results = check(m, read_entry(path))
    failures = [r for r in results if r[0] == "FAIL"]
    print("== Entry check against a fresh scan ==")
    print("readme: %s" % path)
    for status, what, detail in results:
        print("%-9s %-46s %s" % (status, what, detail))
    print("")
    print("checks: %d, declared: %d, failures: %d" % (
        len(results), len([r for r in results if r[0] == "declared"]), len(failures)))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
