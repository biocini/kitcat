# Rijke — Introduction to Homotopy Type Theory

The library's **foundational reference**: the underlying formalism
of kitcat is univalent mathematics, and this is the standard text
for it. Every role that reasons mathematically — analyzer, coder,
reviewer, researcher, ingest, writer — draws on it for the idiom.

## Citation

Egbert Rijke. *Introduction to Homotopy Type Theory*.
arXiv:2212.11082 [math.LO], December 2022.
<https://arxiv.org/abs/2212.11082>. (A revised version of the
author's lecture notes; later published by Cambridge University
Press, 2025.)

## Vetting

PROVISIONAL. Ingested 2026-07-12 by Claude (Opus 4.8) at Lane's
direction (R7 — the foundational-source standard), via the
ingestion protocol: the arXiv LaTeX e-print fetched directly
(`curl https://arxiv.org/e-print/2212.11082`), the canonical
artifact hashed, and the source tree read for the section map
below. The document hash was checked stable across two independent
fetches. This entry becomes vetted only on Lane's confirmation; no
load-bearing citation rests on a PROVISIONAL entry.

## Files

Canonical format: **LaTeX source** (an arXiv e-print). All vendored
and derived forms are gitignored; only this README is tracked.

- `rijke-hott.tar.gz` — the canonical artifact (the arXiv e-print
  source tarball). This is the file the hash below is of.
- the extracted LaTeX tree beside it — `hott-intro.tex` (the main
  file: `\input`s the parts), the three part files
  (`chapter-type-theory.tex`, `chapter-univalent-foundations.tex`,
  `chapter-circle.tex`), and one `.tex` per lecture (mapped below),
  plus `bibliography.bib` and `cambridge7A.cls`.

Grep the lecture `.tex` for a definition; jump with
`sed -n 'A,Bp' <lecture>.tex`.

## Document hash

sha256 of the canonical artifact (the e-print tarball), stable
across independent arXiv fetches:

```
562be57f5f652004b7f0a816a9196b417f661e1f21f203e7a99f1fa034cb628d  rijke-hott.tar.gz
```

Fallback if the gzip wrapper ever varies — sha256 of the inner
(uncompressed) tar, `gunzip -c rijke-hott.tar.gz | shasum -a 256`:

```
51ad7e31941f4959b8241c3e6c5518dac0cb750a87f731bc27cbe17a41a70b7f
```

## Section map

Three parts (`hott-intro.tex:170–172`), each `\input`ing one
`.tex` per lecture. Depth is at the lecture-file level — grep the
named file for a specific definition.

**Part I — Martin-Löf type theory** (`chapter-type-theory.tex`):
- `dtt.tex` — dependent type theory: the rules, judgments, Π.
- `pi.tex` — the Π-type: functions, currying, composition.
- `nat.tex` — the natural numbers and induction.
- `inductive.tex` — inductive types in general; the pattern.
- `identity.tex` — the **identity type**, `refl`, the induction
  principle (path induction), transport, `ap`.
- `universes.tex` — universes; type families as maps into a
  universe.
- `modular-arithmetic.tex`, `number-theory.tex` — worked
  developments over ℕ.

**Part II — Univalent foundations**
(`chapter-univalent-foundations.tex`):
- `equivalences.tex` — **equivalences**: `is-equiv`, half-adjoint
  vs bi-invertible, the contractible-fibers characterization.
- `contractible.tex` — contractible types; `is-contr`; singleton
  induction.
- `fundamental.tex` — the fundamental theorem of identity types
  (a family is an equivalence iff its total space is contractible).
- `hierarchy.tex` — the **h-level hierarchy**: propositions, sets,
  `is-prop`/`is-set`, truncation levels.
- `funext.tex` — function extensionality.
- `propositional-truncation.tex` — propositional truncation and
  its universal property.
- `images.tex` — the image of a map; (surjection, embedding)
  factorization.
- `finite-types.tex` — finite types; counting.
- `univalence.tex` — the **univalence axiom** and its consequences.
- `set-quotients.tex` — set quotients.
- `groups.tex` — groups (as sets with structure); the univalent
  treatment.
- `W-types.tex` — W-types (well-founded trees).

**Part III — The circle** (`chapter-circle.tex`):
- `circle.tex` — the **circle** as a higher inductive type; its
  induction and recursion principles.
- `circle-universal-cover.tex` — the universal cover; ΩS¹ ≃ ℤ.

## What the source establishes

A self-contained development of dependent type theory and univalent
foundations from first principles: the identity type and path
induction; equivalences and the fundamental theorem; the h-level
hierarchy; function extensionality, propositional truncation, and
the univalence axiom; and a first higher inductive type (the
circle) with the ℤ computation of its loop space. It fixes the
vocabulary and proof idioms kitcat's own developments use —
`is-contr`/`is-prop`/`is-set`, `is-equiv` via contractible fibers,
transport and `ap`, the fundamental theorem — so a kitcat
construction can cite the standard definition rather than restate
it. Everything recorded here is the source's own content, stated in
its own terms; a kitcat result is machine-checked only when its
module or `Gloss.*` certificate says so.
