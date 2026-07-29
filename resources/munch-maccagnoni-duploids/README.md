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
by [`mmmm-classical-notions`](../mmmm-classical-notions/README.md).

## Vetting

Directed agent ingestion, 2026-07-27. **PROVISIONAL.**

What was opened and checked: the HAL cover page and the article's
title page and abstract, read to build the bibliographic record above;
the section map's line anchors below, produced mechanically over the
extraction and spot-checked against the numbered statements they name.

Statements verified: 24/24 CONFIRMED (digest-level), 2026-07-28, by
Claude (Sonnet 5), @ a39faa7cfe1f. All 24 numbered statements were
read in full against `duploids.pdftext` at their section-map anchors;
every anchor confirmed correct, no drift found. Two source-level
findings from that pass: Proposition 8's own statement is correct,
but its proof's closing sentence ("Hence `wrap_N` is linear") is a
genuine error in the published text, confirmed against a direct
render of `duploids.pdf` page 8 rather than the extraction alone; and
mmmm-classical-notions's duploid definition, credited "a slight
variant of" this paper's (`article.tex:1817`), is not verified to
coincide with either of this paper's two duploid definitions
(Definition 7, Definition 9) — see `outputs/duploids-statement-audit.md`
for the full audit.

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

## Content digests

Statement-level, in the source's own notation. `•` is composition in
the positive subcategory, `◦` in the negative subcategory; `f g`
(juxtaposition, applicative order) means "apply `g` then `f`" — the
reverse of this repository's diagrammatic convention.

- **Pre-duploid** (Definition 1, l.180): a set of objects `|D|` with a
  polarity map `ϖ : |D| → {+, ⊖}`, hom-sets `D(A,B)`, a composition
  `g f ∈ D(A,C)` for `f ∈ D(A,B)`, `g ∈ D(B,C)` — written `g • f` when
  `B` is positive, `g ◦ f` when `B` is negative — and identities. Three
  associativity laws hold, one per fixed polarity pattern on the middle
  two objects: `(••)` `(h•g)•f = h•(g•f)` over `A→P→Q→B`; `(◦◦)`
  `(h◦g)◦f = h◦(g◦f)` over `A→N→M→B`; `(•◦)` `(h•g)◦f = h•(g◦f)` over
  `A→N→P→B`. Left open: paths `A→P→N→B` need not associate.
- **Linear, thunkable** (Definition 2, l.233): `f` is linear when
  `f(gh) = (fg)h` for all `g,h`; `f` is thunkable when `h(gf) = (hg)f`
  for all `g,h`. Any `f : P → A` (positive source) is automatically
  linear; any `f : A → N` (negative target) is automatically thunkable.
  Both classes are closed under composition and identity. Terminology
  after Führmann and Hasegawa.
- **Sub-categories** (Definition 3, l.246): `D_l`, `D_t` — linear,
  thunkable morphisms of `D`; `N_l` — linear morphisms of `N`; `P_t` —
  thunkable morphisms of `P`. `N`/`N_l` are the full subcategories of
  `D_t`/`D_l` restricted to negative objects; `P`/`P_t` symmetrically
  for `D_l`/`D_t` restricted to positive objects.
- **Thunk** (Definition 5, l.286, after Führmann): a functor `L : P →
  P` with `ε : L → 1`, `ϑ : 1 → L`, `ϑ_L : L → L²` natural, satisfying
  `ε•ϑ = id`, `Lε•ϑ_L = id_L`, `ϑ_L•ϑ = Lϑ•ϑ`; induces a comonad
  `(L,ε,ϑ_L)`. A thunk-force category `(P,•,id,L,ϑ,ε)` builds a
  pre-duploid: positive objects are `P`'s objects, negative objects a
  disjoint copy `⇑|P|`, with Führmann's own "thunkable" (`Lf•ϑ_P =
  ϑ_Q•f`) recalled for comparison against Definition 2.
- **Proposition 6** (l.315): for the pre-duploid built from a
  thunk-force category, `f : P → Q` is thunkable in Führmann's sense
  iff thunkable per Definition 2. Corollary: `ϑ` is natural iff the
  pre-duploid is a category (`◦•`-associativity holds).
- **Duploid, first form** (Definition 7, l.418): a pre-duploid `D` with
  mappings `⇓ : |N|→|P|`, `⇑ : |P|→|N|` and, for all `P,N`, morphisms
  `delay_P : P→⇑P`, `force_P : ⇑P→P`, `wrap_N : N→⇓N`, `unwrap_N :
  ⇓N→N` satisfying `force_P◦(delay_P•f) = f`, `(f◦unwrap_N)•wrap_N =
  f`, `delay_P•force_P = id_⇑P`, `wrap_N◦unwrap_N = id_⇓N`. Superseded
  by the equivalent Definition 9.
- **Proposition 8** (l.434): for any `N`, `wrap_N` is thunkable; dually
  for any `P`, `force_P` is linear. Proof (for `wrap_N`): `h◦(g•wrap_N)
  = (h◦(g•wrap_N)◦unwrap_N)•wrap_N = (h◦(g•wrap_N◦unwrap_N))•wrap_N =
  (h◦g)•wrap_N`, using `wrap_N◦unwrap_N = id_⇓N`. **Note**: the
  proposition's statement is correct, and the derived equation is
  exactly Definition 2's thunkable shape (`h(gf)=(hg)f` with
  `f=wrap_N`); the published proof's own closing sentence nonetheless
  reads "Hence `wrap_N` is linear" — a genuine error in the paper's
  text, confirmed against a direct render of the PDF page, not an
  extraction artifact. This proposition licenses Definition 9's
  simplification.
- **Duploid** (Definition 9, l.440): "A duploid is a pre-duploid `D`
  given with mappings `⇓ : |N|→|P|` and `⇑ : |P|→|N|`, together with a
  family of invertible linear maps `force_P : ⇑P→P` and a family of
  invertible thunkable maps `wrap_N : N→⇓N`," introduced as "the
  following equivalent definition of a duploid" — equivalent to
  Definition 7 via Proposition 8, with `delay_P`, `unwrap_N` recovered
  as `force_P⁻¹`, `wrap_N⁻¹`. This is the definition
  `mmmm-classical-notions`'s README credits as "a slight variant of"
  (`article.tex:1817`); the correspondence is not verified — see
  `outputs/duploids-statement-audit.md`.
- **The duploid construction** (Proposition 10, l.576, from §3.2):
  given an adjunction `F ⊣ G : C1 → C2` with `♯ : C1(F−,=) → C2(−,G=)`
  natural, `♭ = ♯⁻¹`, negative objects `|C1|`, positive objects `|C2|`,
  `|D| = |C1| ⊎ |C2|`, `D(A,B) = C1(FA⁺,B⁻)` with `g◦_D f =
  (g♯◦_{C2}f♯)♭`: this data is a pre-duploid. `••`-associativity is
  inherited from `C1`; `◦◦` from `♯`/`♭` mutually inverse; `•◦` from
  naturality of `♯`/`♭`.
- **Remark 11** (l.581): in that construction, `P` is the Kleisli
  category `(C2)_GF` of the monad `GF`, `N` the Kleisli category
  `(C1)_FG` of the comonad `FG`; shifts `⇑P := FP`, `⇓N := GN`,
  `delay_P := id^{C1}_{FP}`, `force_P := (id_{GFP})♭`, `wrap_N :=
  id^{C1}_{FGN}`, `unwrap_N := (id_{GN})♭`.
- **Proposition 12** (l.607): every adjunction determines a duploid
  (Proposition 10 plus Remark 11's shift data); stated as an immediate
  corollary with no separate proof.
- **Proposition 13, thunkability criterion** (l.614): for `f ∈
  D(A,P)`, `f` is thunkable iff `(wrap_⇑P◦delay_P)•f =
  wrap_⇑P◦(delay_P•f)`; dually for `f ∈ D(N,B)`, `f` is linear iff
  `f◦(unwrap_N•force_⇓N) = (f◦unwrap_N)•force_⇓N`.
- **Proposition 14, linearity criterion** (l.647): for `F ⊣_{(η,ε)} G :
  C1 → C2` and its duploid `D`: `f ∈ D(N,A)` is linear iff
  `f◦ε_{FGN} = f◦FGε_N`; `f ∈ D(A,P)` is thunkable iff its transpose
  `f♯ ∈ C2(A⁺,GFP)` satisfies `η_{GFP}◦f♯ = GFη_P◦f♯`. (Immediately
  after, Corollary 15 — not independently audited — gives: the
  associated duploid is a category iff the adjunction is idempotent.)
- **Functor of pre-duploids** (Definition 18, l.768): a
  polarity-preserving `|F| : |D1|→|D2|` with `F_{A,B} : D1(A,B) →
  D2(FA,FB)` preserving identities and composition. A **functor of
  duploids** additionally sends `force_P` to a linear morphism and
  `wrap_N` to a thunkable morphism.
- **Proposition 19** (l.772): `F` is a functor of duploids iff it
  restricts to functors `F_t : D_t→D'_t`, `F_l : D_l→D'_l` with `F :
  D(−,=) → D'(F_t−,F_l=)` natural.
- **The category `Dupl`** (Definition 20, l.786): objects duploids,
  morphisms duploid functors (Definition 18).
- **Proposition 21** (l.827): for a duploid `D`, `↑ : P_t→N_l` (the
  restriction of `⇑`) is left adjoint to `↓ : N_l→P_t` (the restriction
  of `⇓`), with unit `wrap_⇑◦delay` and co-unit `unwrap•force_⇓`.
- **Proposition 22** (l.840): `D` is isomorphic to the duploid
  constructed (Proposition 10/Remark 11) from the adjunction `↑ ⊣ ↓` of
  Proposition 21.
- **Equalising requirement** (Definition 23, l.851): an adjunction `F
  ⊣_{(η,ε)} G` satisfies it when, for all `P`, `η_P` equalises
  `η_{GFP}` and `GFη_P`, and for all `N`, `ε_N` co-equalises `ε_{FGN}`
  and `FGε_N`.
- **Proposition 24** (l.854): the equalising requirement holds iff (1)
  every `ε_N` epi and `η_P` mono (`F`,`G` faithful), (2) every linear
  `f ∈ D(N,A)` factors as `g◦ε_N`, (3) every thunkable `f ∈ D(A,P)`
  factors as `η_P◦g`.
- **Proposition 25** (l.867): the adjunction `↑ ⊣ ↓ : N_l → P_t` of
  Proposition 21 satisfies the equalising requirement.
- **Pseudo map of adjunctions** (Definition 26, l.880, after Jacobs): a
  quadruple `(H1,H2,φ,ψ)` of functors `H1 : C1→C1'`, `H2 : C2→C2'` with
  natural isomorphisms `φ : F'H2 ≃ H1F`, `ψ : G'H1 ≃ H2G` preserving
  `η`,`ε` up to isomorphism.
- **The category `Adj`** (Definition 27, l.897): adjunctions between
  locally small categories as objects, pseudo maps as morphisms;
  `Adj_eq` the full subcategory satisfying the equalising requirement.
- **The reflection theorem** (Theorem 28, l.899): a reflection and
  equivalence `Dupl ≃ Adj_eq ⊳ Adj`. `j : Adj → Dupl` is the duploid
  construction (Proposition 10 + Remark 11); `i : Dupl → Adj_eq` sends
  a duploid to the adjunction `↑ ⊣ ↓` of Proposition 21 (in `Adj_eq` by
  Proposition 25); Proposition 22 gives `jiD ≃ D`. The paper states the
  full proof is in the author's PhD thesis; glosses `j` as completing
  values with all pure (thunkable) expressions and stacks with all
  linear evaluation contexts.
