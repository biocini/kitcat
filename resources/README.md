# resources/ — vetted source references

Each entry is one source (paper, book chapter, thesis, slide deck,
web reference) in its own directory: `resources/<slug>/`.

An entry directory is self-contained: its README.md carries
everything needed to cite and audit the source, and entries
reference at most other entries in this tree — never files elsewhere
in the repository — so an entry stays a reliable citation target as
the repository changes around it. An entry is built to serve a
construction *at speed*: when a proof turns on a source, the reader
opens the vendored copy and jumps to the cited line, so the map
below is line-anchored, not vague.

## Canonical source format

House the source's own markup when it exists. The format hierarchy:

1. **Source markup** — LaTeX `.tex` (an arXiv e-print), or other
   markup. Math and structure stay intact and greppable; this is
   the canonical form, preferred over everything below.
2. **PDF** — when no source markup is available.
3. **Transcribed text** (`.pdftext`) — a `pdftotext` extraction, the
   lowest form: a greppability fallback beside a PDF when the source
   markup is absent.

Each entry records its canonical format (LaTeX-source / PDF / scan).
All vendored and derived forms are gitignored — the source tarball,
the extracted markup, the `.pdftext` — so only tracked, regenerable
metadata leaves the machine. A new unfolded-source file extension not
yet ignored is added to `.gitignore` as encountered.

## Entry format — `resources/<slug>/README.md`

- **Citation** — full bibliographic record: authors, title, venue,
  year, DOI or arXiv id, URL.
- **Vetting** — who opened the document and when, and what it was
  checked to say. A directed agent ingestion produces a PROVISIONAL
  entry (say so here); it becomes vetted only after Lane confirms.
  No load-bearing citation rests on a PROVISIONAL entry.
- **Files** — an inventory of the vendored artifacts (the source
  tarball, the extracted markup or `.pdftext`), naming the canonical
  format and which file the reader greps.
- **Document hash** — sha256 of the **canonical artifact** (the
  e-print tarball for a LaTeX source; the PDF for a PDF-only source)
  plus its filename (`shasum -a 256 <file>`). The canonical-format
  record disambiguates which artifact the hash is of. The hash and
  publication data are tracked; any copy re-verifies against them.
- **Section map** — a location→content map anchored to lines in the
  vendored readable copy (`l.NNN` into the `.tex`/`.pdftext`), with a
  jump note (`sed -n 'A,Bp' <file>`). Map **depth tracks the
  source's load**: a full line-anchored map for a load-bearing or
  mechanization-target source, a short outline for a background
  reference. A load-bearing citation resolves at `<file>:LINE`, not
  "Definition 1, §2".
- **What the source establishes** — the source's actual deliverables
  and their status in the field. Entries record what the source
  states, not what the repository has proven: every mathematical
  claim here is CONJECTURED until machine-checked.

The depth standard: a full line-anchored map for an implemented or
load-bearing source, a one-line outline for a background reference.
The kitcat exemplar is the Rijke entry (`resources/rijke-hott/`),
the library's foundational reference.

## Acquiring documents

When a load-bearing claim rests on a source not yet vendored, the
default action is to ingest it (ingest-on-firsthand-need), producing
a PROVISIONAL entry — not merely to propose a candidate. Fetch by
stable identifier: for an arXiv source, `curl
https://arxiv.org/e-print/<id>` for the canonical LaTeX-source
tarball and `https://arxiv.org/abs/<id>` for metadata (the
paper-search capability maps this; feynman alpha is not relied on);
otherwise the source's stable URL or a user-supplied file. Compute
the sha256 of the canonical artifact and record it; for an existing
entry, check it against the recorded hash before citing from the
local copy. A hash mismatch is a FATAL finding: stop and resolve
which document the entry describes before citing anything.

An agent may ask to vendor a source at any time, especially when a
construction under development draws on it. Workflows also propose
candidate entries in their provenance sidecars; a PROVISIONAL entry
becomes vetted at the human confirmation step.
