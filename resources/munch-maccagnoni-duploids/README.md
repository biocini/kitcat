---
artifact: duploids.pdf
sha256: a39faa7cfe1f882fcb70c4263ce9d9108a431f3698fe98759587316216cb5ac9
format: pdf
fetch-url: none
metadata-url: https://inria.hal.science/hal-00996729v1
doi: 10.1007/978-3-642-54830-7_26
version: v1
fetched: 2026-07-27
---

# Munch-Maccagnoni — Models of a Non-Associative Composition

## Citation

Guillaume Munch-Maccagnoni. *Models of a Non-Associative
Composition*. FoSSaCS 2014 — 17th International Conference on
Foundations of Software Science and Computation Structures, April
2014, Grenoble, France. LNCS; pp. 396–410.
DOI 10.1007/978-3-642-54830-7_26. HAL Id hal-00996729, version 1
(submitted 26 May 2014), <https://inria.hal.science/hal-00996729v1>.

The vendored copy is the HAL author deposit, which carries the HAL
cover page ahead of the article proper (the article's own title page
begins at `l.28`).

From the abstract: "We characterise the polarised evaluation order
through a categorical structure where the hypothesis that composition
is associative is relaxed. Duploid is the name of the structure, as a
reference to Jean-Louis Loday's duplicial algebras. The main result is
a reflection Adj → Dupl where Dupl is a category of duploids and
duploid functors, and Adj is the category of adjunctions and pseudo
maps of adjunctions."

This is the originating duploid paper, cited as the duploids reference
by [`mangel-classical-notions`](../mangel-classical-notions/README.md).

## Vetting

Directed agent ingestion, 2026-07-27. **PROVISIONAL.**

What was opened and checked: the HAL cover page and the article's
title page and abstract, read to build the bibliographic record above;
the section map's line anchors below, produced mechanically over the
extraction and spot-checked against the numbered statements they name.

Nothing further was read. **No statement audit has been run, so this
entry carries no `Statements verified:` field and supports no
load-bearing citation.** Content digests are deliberately absent
rather than written from an unread source.

## Files

- `duploids.pdf` — the canonical artifact, the HAL v1 deposit. This
  is the format of record; the entry is `format: pdf` because no
  source markup was supplied.
- `duploids.pdftext` — greppability fallback, and the file the
  section map's `l.NNN` anchors index. Native text layer; no OCR
  chain was needed or run.

Extraction provenance, regenerable byte-identically:

```
pdftotext duploids.pdf duploids.pdftext
```

with `pdftotext version 26.06.0` (Poppler). 975 lines.

## Source provenance

Lane placed the PDF in the repository root on 2026-07-27; it was
moved into this entry unmodified. No fetch was performed by the
ingesting agent, so `fetch-url` is `none` rather than a URL that was
not exercised — the recorded `sha256` is the identity of the file as
supplied, and it has not been checked against any public copy.

The HAL record is open access and the article's HAL landing page is
recorded as `metadata-url`; the Springer version behind the DOI is
paywalled. A re-fetcher should expect the HAL deposit to carry the
cover page reproduced in the vendored copy, and should treat a
byte-difference against the recorded hash as a re-ingestion.

## Section map

Anchors index `duploids.pdftext`. Jump with
`sed -n 'A,Bp' duploids.pdftext`.

- HAL cover page — `l.1`
- Title, author, abstract — `l.28`
- Introduction — `l.40`
- **Definition 1** (pre-duploid) — `l.180`
- **Definition 2** (linear morphism) — `l.233`
- **Definition 3** (the sub-categories of a pre-duploid) — `l.246`
- **Definition 5** (thunk, after Führmann) — `l.286`
- **Proposition 6** (thunkable for thunk-force = thunkable for
  pre-duploids) — `l.315`
- **Definition 7** (duploid, first form) — `l.418`
- **Proposition 8** (`wrap N` thunkable; dually `force P` linear) —
  `l.434`
- **Definition 9** (duploid) — `l.440`
- **Proposition 10** (the construction is a pre-duploid) — `l.576`
- **Remark 11** (P is the Kleisli category of the monad GF; N dually)
  — `l.581`
- **Proposition 12** (every adjunction determines a duploid) — `l.607`
- **Proposition 13** (thunkability criterion) — `l.614`
- **Proposition 14** (linearity criterion) — `l.647`
- **Definition 18** (functor of pre-duploids) — `l.768`
- **Proposition 19** — `l.772`
- **Definition 20** (the category `Dupl`) — `l.786`
- **Proposition 21** (↑ ⊣ ↓ on the sub-categories) — `l.827`
- **Proposition 22** (D isomorphic to the duploid of its adjunction) —
  `l.840`
- **Definition 23** (equalising requirement) — `l.851`
- **Proposition 24** — `l.854`
- **Proposition 25** — `l.867`
- **Definition 26** (pseudo map of adjunctions) — `l.880`
- **Definition 27** (the category `Adj`) — `l.897`
- **Theorem 28** (the reflection and the equivalence) — `l.899`

Map depth is an outline of the numbered statements only. It is not a
content map, and it does not stand in for the statement audit.
