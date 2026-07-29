---
artifact: mangel-classical-notions.tar.gz
sha256: 8d9edc19055a23bd32a40d4e613b4462235b1a8497b6ce4310a028bc5a319a6d
format: latex-source
fetch-url: https://arxiv.org/e-print/2502.13033
metadata-url: https://arxiv.org/abs/2502.13033
doi: 10.1145/3776715
version: v4
fetched: 2026-07-24
sha256-inner: d300fb10e5c9228f2687fc671aff2406576f3974920f9c717faf792282b06a5b
---

# Mangel, Melliès & Munch-Maccagnoni — Classical notions of computation and the Hasegawa-Thielecke theorem

A syntax and semantics for classical logic with a computationally
involutive negation, via a polarised effect calculus (the linear
classical *L*-calculus). Accommodating call-by-value and call-by-name
in one structure makes composition fail to associate; the paper takes
that failure as the subject matter, developing **non-associative
categories** (unital magmoids), the classes of **thunkable** and
**linear** maps that non-associativity makes expressible, adjunctions
between graph morphisms, and polarised notions of symmetric monoidal
closed duploid and dialogue duploid. It shows these are the direct-style
counterparts of adjunction models — linear effect adjunctions for
linear call-by-push-value, dialogue chiralities for linear
continuations — interprets the calculus in any dialogue duploid,
exhibits a syntactic dialogue duploid, and proves the
Hasegawa-Thielecke theorem: central and thunkable maps coincide in any
dialogue duploid. This is the extended version, with additional
illustrations and proofs.

Load declaration: duploid-tier reference, held at statement depth over
the non-associative-category and duploid material (§2–§3) — the source
for the polarity vocabulary the deductive-system work reaches toward —
and at outline depth over the calculus, the semantics, and the
theorem's proof.

## Citation

Éléonore Mangel, Paul-André Melliès and Guillaume Munch-Maccagnoni.
*Classical notions of computation and the Hasegawa-Thielecke theorem
(extended version)*. arXiv:2502.13033 [cs.LO], v4, 2 December 2025
(v1: 18 February 2025). <https://arxiv.org/abs/2502.13033>. Published
in *Proceedings of the ACM on Programming Languages* (POPL 2026); DOI
10.1145/3776715. Subjects: cs.LO; cs.PL; math.CT.

## Vetting

PROVISIONAL. Ingested 2026-07-24 by Claude (Fable 5) at Lane's
direction, from a Lane-supplied tarball verified byte-identical to the
live arXiv e-print (sha256 match against a fresh fetch of `fetch-url`,
same session). The introduction's thunkable/linear material and §2–§3
were read in the vendored `article.tex` during ingestion.

Statements verified: 7/7 CONFIRMED (digest-level), 2026-07-28, by
Claude (Sonnet 5), @ 8d9edc19055a. All seven Content digests below
were independently re-read against `article.tex` at their cited
anchors and confirmed verbatim; two anchor-precision corrections and
one source-level typo (a codomain slip in the composition-law diagram
at l.1531, already given correctly in the digest below) are recorded
in `outputs/duploids-statement-audit.md`.

## Files

- `mangel-classical-notions.tar.gz` — the arXiv e-print (v4), the
  canonical artifact. Contains `article.tex`, `article.bbl`,
  `acmart.cls`, and `00README.json` (toplevel `article.tex`, TeX Live
  2023, pdflatex).
- `article.tex` — extracted markup, the file the reader greps; all
  line anchors below index into it.
- `article.bbl` — extracted bibliography.
- `acmart.cls` — the publisher class file, extracted with the source.

## Source provenance

Supplied by Lane at the repository root on 2026-07-24 as the duploid
reference for the deductive-system work. During ingestion the same
session, a fresh fetch of `https://arxiv.org/e-print/2502.13033`
produced a byte-identical file (sha256 `8d9edc19…`), authenticating the
vendored copy as the arXiv-served current e-print; the abs page listed
four versions, v4 (2 Dec 2025) being current at that time, which
matches the internal file dates.

## Section map

Jump note: `sed -n 'A,Bp' article.tex`.

- l.421–447 — Abstract.
- l.489–1510 — §1 Introduction: how non-associativity emerges between
  call-by-value and call-by-name (l.491), the non-associative category
  of an adjunction (l.732), **thunkable and linear maps** (l.1059),
  continuations and dialogue duploids (l.1198), the
  Hasegawa-Thielecke theorem (l.1347), contributions (l.1468).
- l.1511–1677 — §2 Non-associative categories: the definition
  (l.1526), the opposite, path association, linear and thunkable maps
  (l.1551–1570).
- l.1678–1878 — §3 Duploids: polarity (definition l.1694), positive
  and negative shifts (l.1712), **duploid** (l.1819), duploid functors
  (l.1841), and the adjunction characterisation (theorem l.1860).
- l.1879–1998 — §4 Symmetric monoidal duploids (definition l.1975).
- l.1999–2268 — §5–§6 Graph morphisms and adjunctions between them;
  symmetric monoidal closed duploids.
- l.2269–2599 — §7 The linear call-by-push-value *L*-calculus.
- l.2600–2691 — §8 Dialogue duploids (definition l.2651).
- l.2692–3035 — §9–§10 The linear classical *L*-calculus; the
  syntactic dialogue duploid (l.2952), syntactic centrality (l.3014).
- l.3036–3173 — §11 The Hasegawa-Thielecke theorem.
- l.3174–3538 — §12 The one-sided variant of the calculus.
- l.3539–3730 — §13 Classical notions of computation, historically.
- l.3731–end — Appendices: Joyal's lemma (l.3731), diagram chasing
  (l.3752), non-functoriality of the shift (l.3880), the appendix
  developments of §5–§6 (l.3951, l.4107), linearly distributive
  duploids (l.4280), dialogue duploids and functors (l.4336), the
  interpretation and its soundness (l.4402, l.4486), syntactically
  thunkable and central expressions (l.4757), and a direct equational
  proof of the theorem (l.4845).

## Content digests

- **Non-associative category** (l.1526): a *unital magmoid*, or
  non-associative category, is a reflexive graph equipped with a
  composition `M(Y,Z) × M(X,Y) → M(X,Z)` satisfying only the
  neutrality equations `f ∘ id_X = f = id_Y ∘ f`, where `id` is the
  chosen map of the reflexive graph. `M^op` reverses the maps.
- **Association, thunkable, linear** (l.1084–1093, l.1552–1562): a
  path `(f,g,h)` of length 3 *associates* when `(h ∘ g) ∘ f = h ∘ (g ∘
  f)`. A map `f` is **thunkable** when every length-3 path starting
  with `f` associates; dually `h` is **linear** when every length-3
  path ending with `h` associates. The paper reads thunkability as the
  syntactic property of an effectful expression being substitutable
  like a value.
- **Polarity** (definition l.1694): an object `X` is *positive* when
  every map out of `X` is linear, and *negative* when every map into
  it is thunkable. An object may be both — which is the case for every
  object of an associative category — and `(−)^op` reverses the
  polarities.
- **Shifts** (l.1712): a positive shift assigns to each `X` an object
  `⇓X` with a thunkable epi `ω_X : X → ⇓X` universal among maps out of
  `X` for factorisation through a *linear* map; a negative shift is a
  positive shift on `M^op`.
- **Duploid** (l.1819): a non-associative category with a positive and
  a negative shift in which every object is positive or negative (or
  both). Composition `g ∘ f` is written with one notation when the
  middle object is positive and another when it is negative — the two
  disciplines are one operation read at the two polarities, not two
  independent operations. Notations are fixed for the subcategories of
  linear maps, of thunkable maps, and the full subcategories of
  positive and of negative objects.
- **Adjunctions and duploids** (theorem l.1857, after Munch-Maccagnoni):
  every non-associative category arising from an adjunction `L ⊣ R`
  carries a duploid structure whose positive part is equivalent to the
  Kleisli category of `T = R∘L` and whose negative part is equivalent
  to the co-Kleisli category of `K = L∘R`; it is associative exactly
  when the monad (equivalently the comonad) is idempotent. Conversely
  every duploid induces an adjunction between its thunkable-positive
  and linear-negative parts, whose associated non-associative category
  is equivalent to it.
- **The theorem** (§11, l.3036): central and thunkable maps coincide in
  any dialogue duploid — in particular for any double-negation monad on
  a symmetric monoidal category. Proved both semantically and
  syntactically; a direct equational proof is in the appendix (l.4845).

## What the source establishes

A direct-style semantics for polarised classical computation in which
non-associativity is structural rather than defective: non-associative
categories with the thunkable/linear vocabulary, duploids and their
symmetric monoidal and dialogue refinements, the correspondence with
adjunction models and dialogue chiralities, an interpretation of the
linear classical *L*-calculus together with a syntactic dialogue
duploid, and the Hasegawa-Thielecke theorem identifying central and
thunkable maps there. Published in PACMPL (POPL 2026). Every
mathematical claim recorded here is CONJECTURED until machine-checked
in this repository.
