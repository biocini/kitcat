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
PROVISIONAL: agent-vetted; Lane's confirmation of this entry is
pending.

## Document hash

59 PDF pages (beamer compile; overlay steps counted).

```
84aa016de6cbac08820cc9710d80f9c40a01acde075ea0c469b1d50e58d7f826  petrakis-slides.pdf
```

## Summaries

Everything below records what the source states; every mathematical
claim is CONJECTURED until machine-checked. Slides are a talk
artifact: statements are compressed and carry no proofs; for the
dependent-arrows half, the paper *Categories with dependent arrows*
(arXiv:2303.14754, entry `petrakis-dep-arrows`) is the citable
source. The codependent half extends beyond that paper.

**Stated aim** (opening slides): model the Π-type categorically as
a fundamental notion, independent of a corresponding implementation
of the Σ-type, and without requiring a strong MLTT background —
this is distinct from finding categorical models for the whole of
MLTT.

**Outline from slide titles:**

- Arrows vs functions: what arrows preserve and what they add.
- Categories with family-arrows (λ ∈ fHom(a)); constant
  family-arrows; family-arrows on a topos (Pitts); what fam-arrows
  preserve/forget about families of types.
- (fam, Σ)-categories: Sigma-objects; examples (binary products;
  a commutative-ring example; Sigma-objects on a topos).
- Categories with dep-arrows (Φ ∈ dHom(a, λ)): what dep-arrows
  preserve/forget about dependent functions; any category carries
  two induced dep-structures; every (fam, Σ)-category is a
  dep-category; the canonical dep-structure on a topos; existence
  of dep-structures **not** induced by the canonical construction.
- (dep, Σ)-categories: second projections as dependent arrows; a
  Theorem slide with proof sketch; (dep, Σ)-structures not induced
  by the canonical one.
- The codependent dual (new relative to the arXiv paper): additions
  not traced to dependent functions; categories with
  cofamily-arrows (ρ ∈ cofHom(a)); any category as a
  cofam-category; cofamily-arrows on a topos; interaction with an
  initial object 0; coSigma-objects (examples in Set and in Ring
  with ring-epimorphisms; binary coproducts); coSigma-objects on a
  topos; toward the canonical cofamily and codependent architecture
  of the category of small types (per the programme abstract).
