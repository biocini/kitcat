# Petrakis — Categories with dependent and codependent arrows (slides)

## Citation

Iosif Petrakis. *Categories with dependent and codependent arrows*.
Talk slides, 4th meeting of Working Group 6 (Syntax and Semantics
of Type Theories) of the EuroProofNet COST Action CA20111, Genoa,
17–18 April 2025; talk given Friday 18 April, 15:45–16:10.
Slides: <https://europroofnet.github.io/_pages/WG6/Genova/talks/petrakis.pdf>
(linked from the meeting programme,
<https://europroofnet.github.io/wg6-genoa/programme/>).
Author affiliation (per the title slide): University of Verona.

## Vetting

Opened 2026-07-11 by Claude (Fable 5), at Lane's direction as part
of the founding `resources/` ingestion. Checked: title slide
against the citation; talk title, slot, and slides link against the
EuroProofNet programme page; the outline below extracted from the
slide titles (pdftotext). Bit-identity of the vendored file with
the EuroProofNet URL above verified by sha256 on 2026-07-11.

Brought to the `resources/` format bar 2026-07-12 by Claude (Opus
4.8): canonical format recorded, Files inventory added, and the
slide outline upgraded to a slide-region map with `l.NNN` anchors
into the `.pdftext` plus slide numbers, with the codependent half
(the reason this entry exists) mapped in full. The recorded PDF
hash was re-verified (`shasum -a 256`) and matches.

PROVISIONAL: agent-vetted; Lane's confirmation of this entry is
pending. No load-bearing citation rests on a PROVISIONAL entry.

## Files

Canonical format: **PDF** (slides — a beamer compile; no source
markup is published). All vendored and derived forms are
gitignored; only this README is tracked.

- `petrakis-slides.pdf` — the canonical artifact: a 59-page beamer
  compile (overlay steps counted). This is the file the hash below
  is of.
- `petrakis-slides.pdftext` — a `pdftotext` extraction of the
  canonical PDF (greppability fallback; the map's `l.NNN` anchors
  index this file). Regenerate with
  `pdftotext petrakis-slides.pdf petrakis-slides.pdftext`.

Grep `petrakis-slides.pdftext` for a slide title; jump with
`sed -n 'A,Bp' petrakis-slides.pdftext`.

## Document hash

sha256 of the canonical artifact (the 59-page slides PDF):

```
84aa016de6cbac08820cc9710d80f9c40a01acde075ea0c469b1d50e58d7f826  petrakis-slides.pdf
```

## Section map

Line anchors are into `petrakis-slides.pdftext`; jump with
`sed -n 'A,Bp' petrakis-slides.pdftext`. Slide numbers count
beamer overlay steps (the pdftotext line ranges are the stable
anchor; slide numbers are advisory). The dependent half is a short
outline — it is citable from the paper `petrakis-dep-arrows`
(arXiv:2303.14754); the **codependent half** is mapped in full,
because these slides are the only source that carries it (the
Petrakis–Ehrhardt preprint it draws on, "Categories with dependent
and codependent arrows", 2024, is unpublished — listed at the
References slide `l.1618`).

**Front matter (dependent half — outline; see `petrakis-dep-arrows`):**

- Stated aim (model Π categorically, independent of Σ) — `l.9`
  (slide 2).
- Dependent Category Theory; family-arrows λ ∈ fHom(a) — `l.109`
  (slide 6); constant family-arrows — `l.161` (slide 8).
- (fam, Σ)-categories; Sigma-objects — `l.248` (slide 11);
  (fam, Σ) with 1 = Pitts/Cartmell type-categories — `l.363`
  (slide 12); Sigma-objects on a topos — `l.434` (slide 15).
- dep-arrows Φ ∈ dHom(a, λ) — `l.481` (slide 16); Theorem (Ehrhardt)
  — `l.626` (slide 22); (dep, Σ)-categories, Sigma-objects — `l.673`
  (slide 24); Theorem with proof sketch — `l.777` (slide 27).

**The codependent dual (the load-bearing half — new relative to the
arXiv paper):**

- "What we add that is not traced to dependent functions" (the
  pivot slide) — `l.900` (slide 30).
- coDependent Category Theory (section divider) — `l.909`
  (slide 31).
- Categories with cofamily-arrows ρ ∈ cofHom(a) — `l.911`
  (slide 32); any category C as a cofam-category — `l.952`
  (slide 33); cofamily-arrows on a topos — `l.973` (slide 34).
- Interaction with an initial object 0; the cofamily-arrow
  extensionality property (cofarrExt) — `l.1009` (slide 35).
- Categories with cofamily-arrows and coSigma-objects — `l.1042`
  (slide 36); coSigma in Set — `l.1075` (slide 37); coSigma in Ring
  with ring-epimorphisms (ideals) — `l.1106` (slide 38); binary
  coproducts — `l.1141` (slide 39); coSigma-objects on a topos —
  `l.1166` (slide 40).
- Categories with codep-arrows χ ∈ codHom(a, ρ), ρ ∈ cofHom(a) —
  `l.1189` (slide 41); a (cofam, Q)-category is a codep-category —
  `l.1244` (slide 43); the dual to the dependent arrow Pr₂ is the
  codependent arrow — `l.1296` (slide 45); a (cofam, Q)-category is
  a (codep, Q)-category — `l.1324` (slide 46).
- Dependent and coDependent Category Theory; cofam(A) := A, toward
  the canonical codependent architecture of the category of small
  types — `l.1369` (slide 47), `l.1374` (slide 48); the interplay
  between the dependent and codependent features — `l.1450`
  (slide 49); higher Σ-objects and the dual codependent
  arrow-structures — `l.1536`–`l.1551` (slides 53–54).
- References — `l.1603` (slide 57).

## What the source establishes

Everything below records what the source states; every mathematical
claim is CONJECTURED until machine-checked. Slides are a talk
artifact: statements are compressed and carry no proofs. For the
dependent-arrows half, the paper *Categories with dependent arrows*
(arXiv:2303.14754, entry `petrakis-dep-arrows`) is the citable
source; the codependent half extends beyond that paper and is not
yet published, so this entry supports no load-bearing citation on
its own.

**Stated aim** (opening slides): model the Π-type categorically as
a fundamental notion, independent of a corresponding implementation
of the Σ-type, and without requiring a strong MLTT background —
distinct from finding categorical models for the whole of MLTT.

The dependent development (family-arrows fHom, (fam, Σ)-categories
with Sigma-objects, dep-arrows dHom, (dep, Σ)-categories) is dualized
into a codependent development: cofamily-arrows cofHom, coSigma-objects
(worked in Set, in Ring with ring-epimorphisms, and on a topos, and
recovered from binary coproducts), and codependent arrows codHom
dual to the dependent second-projection arrow — building toward the
canonical cofamily and codependent architecture of the category of
small types (per the programme abstract).
