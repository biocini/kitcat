# Melliès — A micrological study of negation

## Citation

Paul-André Melliès. *A micrological study of negation*. Annals of
Pure and Applied Logic 168(2), February 2017, pp. 321–372.
DOI: 10.1016/j.apal.2016.10.008.
Author manuscript (the vendored copy):
<https://www.irif.fr/~mellies/tensorial-logic/3-microlocal-study-of-negation.pdf>.

Naming note: the paper's title is "micrological"; the manuscript
URL slug says "microlocal" (an older slug the author's site still
serves). The author's tensorial-logic page
(<https://www.irif.fr/~mellies/tensorial-logic.html>) currently
links a *different, later* compile
(`4-micrological-study-of-negation.pdf`, sha256 `9d4f4208…`, with a
`-old` variant `4b6a1f3a…` also hosted); the vendored copy is its
own vintage and every section/definition/proposition number below
refers to it, not to the later compile or the journal version.

## Vetting

Opened 2026-07-11 by Claude (Fable 5), at Lane's direction as part
of the founding `resources/` ingestion. Checked: title page and
abstract against the citation; the plan-of-the-paper paragraph and
the definition/proposition inventory below extracted from the full
text (pdftotext) of the vendored copy. Journal record (APAL 168(2),
pp. 321–372, DOI) confirmed against dblp's APAL volume 168 index.
Bit-identity of the vendored file with the IRIF URL above verified
by sha256 on 2026-07-11.

Brought to the `resources/` format bar 2026-07-12 by Claude (Opus
4.8): canonical format recorded, Files inventory added, and the
key-item locations promised "by pdftotext line region" actually
supplied as `l.NNN` anchors into the `.pdftext`. The recorded PDF
hash was re-verified (`shasum -a 256`) and matches.

PROVISIONAL: agent-vetted; Lane's confirmation of this entry is
pending (the format authority governs what the marker means).

Statements verified: 4/4 CONFIRMED (spot-check), 2026-07-13, by
verifier (Claude), @ 0b482777.

## Files

Canonical format: **PDF** (no source markup is published for this
paper). All vendored and derived forms are gitignored; only this
README is tracked.

- `3-microlocal-study-of-negation.pdf` — the canonical artifact:
  the 41-page IRIF manuscript compile (this is **not** the journal
  compile; the published APAL version spans 52 journal pages, and
  all numbering below is pinned to this vendored 41-page vintage).
  This is the file the hash below is of.
- `micrological-negation.pdftext` — a `pdftotext` extraction of the
  canonical PDF (greppability fallback; the map's `l.NNN` anchors
  index this file). Regenerate with
  `pdftotext 3-microlocal-study-of-negation.pdf micrological-negation.pdftext`.
  Provenance: pdftotext 26.06.0 (flake-pinned poppler; regenerate
  inside `nix develop`); regenerating with this version reproduces
  the vendored extraction byte-identically (checked 2026-07-13
  against a temp-file regeneration).

Grep `micrological-negation.pdftext` for a definition; jump with
`sed -n 'A,Bp' micrological-negation.pdftext`.

## Source URL and re-fetch

Fetched 2026-07-11 from the author's IRIF tensorial-logic page:
<https://www.irif.fr/~mellies/tensorial-logic/3-microlocal-study-of-negation.pdf>
(bit-identity of the vendored copy with this URL verified by sha256
at fetch time). Re-fetch attempt:

```
curl -L -o 3-microlocal-study-of-negation.pdf \
  https://www.irif.fr/~mellies/tensorial-logic/3-microlocal-study-of-negation.pdf
```

The recorded URL served this 41-page vintage at fetch time, but the
vendored manuscript is NOT the compile the author's page currently
links (`4-micrological-study-of-negation.pdf`, a later compile —
see the naming note under Citation). A re-fetch may therefore yield
a different document: the URL still served a PDF when HEAD-checked
2026-07-13, but which compile it now serves was not re-downloaded.
The hash below is the identity of this vintage.

## Document hash

sha256 of the canonical artifact (the 41-page manuscript PDF):

```
0b482777192521606253a92264176f077027adbdcf888cb02f2d9d2ec0405a50  3-microlocal-study-of-negation.pdf
```

## Section map

Line anchors are into `micrological-negation.pdftext`; jump with
`sed -n 'A,Bp' micrological-negation.pdftext`. Section numbers are
as fixed by the paper's plan-of-the-paper paragraph (`l.444`); the
subsection header text is verbatim from the extraction. All numbers
are pinned to the vendored 41-page vintage.

- **§1 Introduction** — `l.11`. Plan of the paper — `l.444`.
- **§2 Linearly distributive categories** (Cockett–Seely) — `l.458`.
  - Right duality in linearly distributive categories — `l.694`.
  - Definition 1 (right duality in a ld category) — `l.700`.
  - Proposition 1 (its basic consequences) — `l.817`.
  - Corollary 2 (∗-autonomous category = symmetric ld category with
    a right duality) — `l.893`.
- **§3 Dialogue chiralities** (recalled from the author's earlier
  work as the symmetric, two-sided formulation) — `l.897`.
  - Proposition 3 (a dialogue chirality is the same as a pair of
    monoidal categories (A, 7, true) and (B, 6, false) with a
    monoidal equivalence and adjunction data) — `l.1013`.
  - Proposition 4 (an alternative formulation of the same) — `l.1308`.
- **§4 Transjunctions and parametric monads** — Transjunctions
  `l.1454`.
  - Definition 2 (transjunction, F ⊣ G along L₁ ⊣ R₁ and L₂ ⊣ R₂)
    — `l.1458`.
  - Proposition 5 (a transjunction along the two adjunctions) —
    `l.1542`.
  - Definition 3 (homomorphism between transjunctions) — `l.1661`.
  - Parametric monads — `l.1905`.
  - Definition 4 (parametric monad: a lax monoidal functor into a
    0-cell of a 2-category) — `l.1909`.
  - Commutators between parametric monads — `l.2033`; Definition 5
    (commutator between two parametric monads) — `l.2064`.
- **§5 Linearly distributive chiralities** (the technical core) —
  `l.2519`.
  - Right duality in linearly distributive chiralities — `l.3068`.
  - Proposition 6 (every ld chirality equipped with a right duality
    induces the dialogue-chirality structure) — `l.3466`.
  - §5.4 Depolarization — Definition 6 (depolarized ld chirality)
    `l.4118`; Proposition 9 (a ld category is the same as a
    depolarized ld chirality) `l.4121`; Proposition 10 (the two
    notions of right duality coincide) `l.4125`.
- Conclusion — `l.4137`. References — `l.4162`.

## What the source establishes

Everything below records what the source states (checked against
the vendored copy); every mathematical claim is CONJECTURED until
machine-checked.

A purely combinatorial presentation of dialogue categories, based
on the symmetric notion of *linearly distributive chirality*; the
micrological analysis decomposes the molecular notion of negation
in tensorial logic into primary elements. The core result: dialogue
chiralities coincide with linearly distributive chiralities
equipped with a right duality when the underlying monoidal category
is symmetric (Proposition 6 supplies one direction) — a discrepancy
remains in the non-symmetric case. §2 recalls linearly distributive
categories (Cockett–Seely) with the right duality of specific
interest; §3 recalls dialogue chirality as the symmetric, two-sided
formulation; the depolarization results (Def 6, Props 9–10) identify
a linearly distributive category with a depolarized linearly
distributive chirality.

**Framing.** The introduction argues that the "classical"
symmetries of linear logic are intrinsic to logic itself and apply
to intuitionistic systems; the decomposition of tensorial negation
recovers an adjunction between left and right negation functors,
linear distributivity laws, axiom/cut combinators, and an
involutive change of frame reversing the two players' viewpoints.
