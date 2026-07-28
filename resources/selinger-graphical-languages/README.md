---
artifact: selinger-graphical-languages.tar.gz
sha256: bacd84e3703ad02ae079a72928adace3b155118516ad1181cd4c378aa0960c0f
format: latex-source
fetch-url: https://arxiv.org/e-print/0908.3347
metadata-url: https://arxiv.org/abs/0908.3347
doi: 10.1007/978-3-642-12821-9_4
version: v1
fetched: 2026-07-28
sha256-inner: 5e0cc5254cb2dc9996eb777bb84bfe5f60708a7413850c09ed96e1aadd8e29a7
---

# Selinger — A survey of graphical languages for monoidal categories

## Citation

Peter Selinger. *A survey of graphical languages for monoidal
categories*. In *New Structures for Physics*, Springer Lecture Notes
in Physics 813, pp. 289–355, 2011. arXiv:0908.3347 (v1, 23 Aug
2009). DOI 10.1007/978-3-642-12821-9_4.

The abstract presents the paper as "intended as a reference guide to
various notions of monoidal categories and their associated string
diagrams" (arXiv abstract page).

## Vetting

Directed agent ingestion, 2026-07-28. **PROVISIONAL.**

What was opened and checked: the arXiv abstract page, read for the
bibliographic record above (title, author, version, journal
reference, DOI); the vendored copy verified byte-for-byte against
the arXiv v1 e-print (98 files, per-file sha256 manifests compared);
the section map's line anchors checked mechanically against
`graphical.tex`.

Nothing further was read. **No statement audit has been run, so this
entry carries no `Statements verified:` field and supports no
load-bearing citation.** Content digests are deliberately absent
rather than written from an unread source.

## Files

- `selinger-graphical-languages.tar.gz`: the canonical artifact,
  the arXiv e-print tarball (`latex-source`).
- Unpacked beside it, 98 files: `graphical.tex` (the file the
  reader greps), `graphical.sty`, `graphical.bbl`, the
  `llamp`/`zllamp` diagram-font sources (`.sty`, `.mf`, `.fd`), and
  87 `.eps` string-diagram figures.

All vendored forms are gitignored. Re-fetching is mechanical from
the frontmatter.

## Source provenance

The unpacked source has been present in this directory since
2026-07-27; the fetcher and host of that copy were not recorded.
The canonical tarball was fetched from the arXiv e-print URL on
2026-07-28, and the unpacked copy was verified byte-identical to
the tarball's contents by per-file hash manifest (98 files). arXiv
serves the e-print stably; no paywall.

## Section map

Top-level structure of `graphical.tex`, by line (anchors checked
2026-07-28; jump with `sed -n 'A,Bp' graphical.tex`). Outline
depth: this is a background reference with no load-bearing
citation yet.

- l.39 Introduction
- l.199 Categories
- l.459 Monoidal categories (l.877 braided, l.1074 balanced, the
  twist θ, l.1125 symmetric)
- l.1188 Autonomous categories (l.1546 pivotal, l.1698 spherical
  pivotal, l.1791 braided autonomous, l.1917 braided pivotal,
  l.2047 tortile, l.2150 compact closed)
- l.2237 Traced categories (l.2569 braided traced, l.2719
  balanced traced, l.2814 symmetric traced)
- l.2895 Products, coproducts, and biproducts
- l.3367 Dagger categories
- l.4026 Bicategories
- l.4080 Beyond a single tensor product
- l.4167 Summary: the table of which graphical language is sound
  and complete for which structure

## What the source establishes

A reference survey of monoidal-category structures (braided,
balanced, symmetric, autonomous, pivotal, tortile, traced, dagger,
and their combinations) and their string-diagram languages, with
the soundness and completeness status of each graphical language
flagged and collected in the Summary table. Entries record what
the source states; every mathematical claim here is CONJECTURED
until machine-checked.
