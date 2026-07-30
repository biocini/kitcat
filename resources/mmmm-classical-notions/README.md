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
Hasegawa-Thielecke theorem: in any dialogue duploid, a map is central
for `⊗` exactly when it is thunkable. This is the extended version,
with additional illustrations and proofs.

Load declaration: duploid-tier reference, held at statement depth over
the non-associative-category, duploid, symmetric-monoidal-duploid,
graph-adjunction and dialogue-duploid material (§2–§5, §8 and §11,
together with the dialogue-chirality definition in §1). It is the
source for the thunkable, linear and central vocabulary of polarity,
and for the adjunction characterisations of a duploid. The closed
structure (§6), the calculus, the semantics, the one-sided variant and
the historical section are mapped at outline depth.

## Citation

Éléonore Mangel, Paul-André Melliès and Guillaume Munch-Maccagnoni.
*Classical notions of computation and the Hasegawa-Thielecke theorem
(extended version)*. arXiv:2502.13033 [cs.LO], v4, 2 December 2025
(v1: 18 February 2025). <https://arxiv.org/abs/2502.13033>. Published
in *Proceedings of the ACM on Programming Languages* (POPL 2026); DOI
10.1145/3776715. Subjects: cs.LO; cs.PL; math.CT.

## Vetting

Provisional marker retired 2026-07-29 (Vetted, below). Ingested
2026-07-24 by Claude (Fable 5) at Lane's direction, from a
Lane-supplied tarball verified byte-identical to the live arXiv
e-print (sha256 match against a fresh fetch of `fetch-url`, same
session). The introduction's thunkable/linear material and §2–§3 were
read in the vendored `article.tex` during ingestion.

Statements verified: 30/30 CONFIRMED (digest-level), 2026-07-29, by
Claude (Opus 5), @ 8d9edc19055a.

The audit read all 30 digests independently against `article.tex` at
their cited anchors, accepting no prior pass's verdict: 23 near-verbatim
renderings and 7 faithful paraphrases, 0 not confirmed. It also
confirmed two source-level typos, which the digests below already read
correctly rather than transcribe: a codomain slip in the
composition-law diagram at l.1531, and a `⊢` for `⊣` slip in the
Dialogue duploid's currification family at l.2661, where the source's
own convention (l.1859, l.2683) uses `⊣` for adjunction.

Vetted: 2026-07-29, Lane (ratified at Lane's explicit direction,
conveyed in-session).

## Files

- `mangel-classical-notions.tar.gz` — the arXiv e-print (v4), the
  canonical artifact. Contains `article.tex`, `article.bbl`,
  `acmart.cls`, and `00README.json` (toplevel `article.tex`, TeX Live
  2023, pdflatex).
- `article.tex` — extracted markup, the file the reader greps; all
  line anchors below index into it.
- `article.bbl` — extracted bibliography.
- `acmart.cls` — the publisher class file, extracted with the source.
- `00README.json` — the arXiv build manifest, extracted with the
  source.

## Source provenance

Supplied by Lane on 2026-07-24 as the reference for duploids and the
polarity vocabulary. During ingestion the same
session, a fresh fetch of `https://arxiv.org/e-print/2502.13033`
produced a byte-identical file (sha256 `8d9edc19…`), authenticating the
vendored copy as the arXiv-served current e-print; the abs page listed
four versions, v4 (2 Dec 2025) being current at that time, which
matches the internal file dates.

## Section map

Jump note: `sed -n 'A,Bp' article.tex`.

- l.421–444 — Abstract.
- l.489–1510 — §1 Introduction: how non-associativity emerges between
  call-by-value and call-by-name (l.491), the non-associative category
  of an adjunction (l.732), **thunkable and linear maps** (l.1059),
  continuations and dialogue duploids (l.1198), **dialogue chirality**
  (definition l.1269), the Hasegawa-Thielecke theorem (l.1347),
  contributions (l.1468).
- l.1511–1677 — §2 Non-associative categories: the definition
  (l.1526), the opposite, path association, linear and thunkable maps
  (l.1552–1562).
- l.1678–1878 — §3 Duploids: polarity (definition l.1694), positive
  and negative shifts (l.1712), the contextual-isomorphism note
  (l.1750), the shift on maps (l.1761), non-functoriality of the shift
  and its repair (proposition l.1795), **duploid** (l.1819), duploid
  functors (l.1841), the 2-category `Dupl` (l.1850), and the
  adjunction characterisation (theorem l.1857).
- l.1879–1998 — §4 Symmetric monoidal duploids: centrality (l.1942),
  symmetric monoidal Freyd structure (l.1950), the positive structure
  (definition l.1975) with its negative dual (l.1981), and the second
  characterisation (theorem l.1988).
- l.1999–2162 — §5 Graph morphisms and adjunctions between them: every
  thunkable map is central (proposition l.2074) with the counterexample
  refuting the converse (l.2081), adjunction between graph morphisms
  (l.2106), its two preservation properties (l.2133), and the duploid
  re-characterisation (l.2154).
- l.2163–2268 — §6 Symmetric monoidal closed duploids.
- l.2269–2599 — §7 The linear call-by-push-value *L*-calculus.
- l.2600–2691 — §8 Dialogue duploids: strong monoidal functor
  (l.2615), monoidal equivalence (l.2640), **dialogue duploid**
  (definition l.2651), the `*`-autonomous remark (l.2674), and the
  chirality correspondence (theorem l.2681).
- l.2692–3035 — §9–§10 The linear classical *L*-calculus; the
  syntactic dialogue duploid (l.2952), syntactic centrality (l.3014).
- l.3036–3173 — §11 The Hasegawa-Thielecke theorem: the semantic
  theorem (l.3044), the syntactic theorem (l.3080), two boxed monad
  equivalences (l.3110, l.3123), the Hasegawa corollary (l.3134),
  linearly distributive duploids (l.3154), and the `⅋`/linear
  refinement (l.3165).
- l.3174–3538 — §12 The one-sided variant of the calculus.
  Extended-version content only: `\begin{arxiv}` at l.3172 and
  `\end{arxiv}` at l.3537 bracket this section alone, so it is absent
  from the published PACMPL version. §13 opens after l.3537 and does
  appear there.
- l.3539–3690 — §13 Classical notions of computations: turning around
  Joyal's obstruction theorem.
- l.3691–3712 — §14 Conclusion and future work.
- l.3714–3730 — Acknowledgements (l.3714), `\printbibliography`
  (l.3722), `\ifbool{arxiv}{}{\end{document}}` (l.3725 — the published
  build ends here, so every appendix below is extended-version
  content), and the `\appendix` break (l.3727).
- l.3731–end — Appendices: Joyal's obstruction theorem (l.3731),
  diagram chasing (l.3752), non-functoriality of the shift (l.3880),
  the appendix developments of §5–§6 (l.3951, l.4107), linearly
  distributive duploids (l.4280), dialogue duploids and functors
  (l.4336), the interpretation and its soundness (l.4402, l.4486),
  syntactically thunkable and central expressions (l.4757), and a
  direct equational proof of the theorem (l.4845).

## Content digests

Category names follow the source. `𝒟` and `ℰ` are duploids, `ℳ` is a
non-associative category, and `𝒜`, `ℬ` are the two sides of an
adjunction. `𝒫` and `𝒩` are the full subcategories of positive and of
negative objects. `𝒫_t` is the thunkable maps of `𝒫`, and `𝒩_l` the
linear maps of `𝒩`. `⟑` and `⟇` render the source's `\tensorialand` and
`\tensorialor` macros (stmaryrd's `\varowedge` and `\varovee`, a wedge
and a vee inside a circle); Unicode has no circled wedge or vee, so the
digests use the nearest wedge/vee-with-dot forms, U+27D1 and U+27C7.

- **Dialogue chirality** (definition l.1269, after Melliès): a pair of
  symmetric monoidal categories `(𝒜, ⟑, true)` and `(ℬ, ⟇, false)`
  equipped with three things. First, an adjunction `L : 𝒜 ⇄ ℬ : R`.
  Second, a symmetric monoidal equivalence
  `(−)* : (𝒜, ⟑, true) ≃ (ℬ, ⟇, false)^op`. Third, a family of
  bijections called *currifications*,
  `χ_{A₁,A₂,B} : 𝒜(A₁ ⟑ A₂, RB) ≅ 𝒜(A₁, R(A₂* ⟇ B))`, natural in `A₁`,
  `A₂` and `B` and satisfying a coherence diagram. The paper takes this
  as the symmetric reformulation, up to equivalence, of a dialogue
  category.
- **Non-associative category** (l.1526): a *unital magmoid*, or
  non-associative category, is a reflexive graph equipped with a
  composition `ℳ(Y,Z) × ℳ(X,Y) → ℳ(X,Z)` satisfying only the
  neutrality equations `f ∘ id_X = f = id_Y ∘ f`, where `id` is the
  chosen map of the reflexive graph. `ℳ^op` reverses the maps.
- **Association, thunkable, linear** (l.1084–1094 and l.1552–1562,
  with the value-substitution reading at l.1065–1068): a
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
- **Shifts** (l.1712): a positive shift assigns to each object `X` an
  object `⇓X` with a thunkable epi `ω_X : X → ⇓X`, subject to a lifting
  property. For every map `f : X → Y` there is a **unique** linear map
  `f† : ⇓X → Y` with `f = f† ∘ ω_X`. A negative shift `(⇑, δ)` is a
  positive shift on `ℳ^op`, so it comes with `δ_Y : ⇑Y → Y` and a
  unique thunkable `f† : X → ⇑Y`.
- **Contextual isomorphism** (l.1750–1758): the map
  `ω̄_X := id_X† : ⇓X → X` (l.1738) is a two-sided inverse to `ω_X`,
  with `ω̄_X ∘ ω_X = id_X` and `ω_X ∘ ω̄_X = id_{⇓X}` (l.1743–1745).
  The paper still declines to
  call `ω_X` an isomorphism. The correct notion in a non-associative
  category asks the map and its inverse to be both thunkable and
  linear, which reflects Levy's observation on contextual isomorphisms.
  `X` and `⇓X` are isomorphic in that sense exactly when `X` is
  positive.
- **The shift on maps** (l.1761–1775): the positive shift extends from
  objects to maps. It sends `f ∈ ℳ(X,Y)` to the unique
  `⇓f ∈ ℳ(⇓X, ⇓Y)` making `⇓f ∘ ω_X = ω_Y ∘ f` commute, and this map is
  `⇓f := (ω_Y ∘ f)†`. The shift carries thunkable maps to thunkable
  maps and preserves identities. It does **not** preserve composition
  (l.1778–1791).
- **Functoriality of the shift, recovered** (proposition l.1795): the
  square comparing `⇓(f' ∘ f)` with `⇓f' ∘ ⇓f` commutes precisely when
  the length-3 path `X →f X' →f' X'' →ω_{X''} ⇓X''` associates, that
  is, when `ω_{X''} ∘ (f' ∘ f) = (ω_{X''} ∘ f') ∘ f`.
- **Duploid** (l.1819): a non-associative category with a positive and
  a negative shift in which every object is positive or negative (or
  both). Composition `g ∘ f` is written with one notation when the
  middle object is positive and another when it is negative — the two
  disciplines are one operation read at the two polarities, not two
  independent operations. Six notations are fixed (l.1830–1837):
  `𝒟_l` and `𝒟_t` for the subcategories of linear and of thunkable
  maps, `𝒫` and `𝒩` for the full subcategories of positive and of
  negative objects, `𝒫_t` for the thunkable maps of `𝒫`, and `𝒩_l` for
  the linear maps of `𝒩`. The composition-notation split sits at
  l.1838–1839.
- **Duploid functor** (definition l.1841): a duploid functor
  `F : 𝒟 → ℰ` is a function `F : |𝒟| → |ℰ|` preserving polarities of
  objects, together with a family `F_{X,Y} : 𝒟(X,Y) → ℰ(FX,FY)`
  preserving compositions, identities, linearity and thunkability.
- **The 2-category `Dupl`** (proposition l.1850): duploids, duploid
  functors and thunkable linear natural transformations form a
  2-category `Dupl`.
- **Adjunctions and duploids** (theorem l.1857, after Munch-Maccagnoni):
  every non-associative category arising from an adjunction `L ⊣ R`
  carries a duploid structure whose positive part is equivalent to the
  Kleisli category of `T = R∘L` and whose negative part is equivalent
  to the co-Kleisli category of `K = L∘R`; it is associative exactly
  when the monad (equivalently the comonad) is idempotent. Conversely
  every duploid `𝒟` induces an adjunction `L : 𝒫_t ⇄ 𝒩_l : R` between
  its thunkable-positive and linear-negative parts, with `L = ⇑` the
  left adjoint and `R = ⇓` the right adjoint, both given by the shift
  operators (l.1872–1873). The duploid associated to that adjunction is
  equivalent **as a duploid** to `𝒟` (l.1874).
- **Central** (l.1942–1944): in a premonoidal category, the square
  built from `f ⋉ A₂`, `A₁ ⋊ g`, `f ⋉ A₂'` and `A₁' ⋊ g`, for maps
  `f : A₁ → A₁'` and `g : A₂ → A₂'`, need not commute. A map `f` is
  called **central** when that square commutes for every map `g`. The
  paper notes that the identity-on-objects functor `ι` into a Kleisli
  category sends every morphism to a central one (l.1945–1946).
- **Symmetric monoidal Freyd structure** (definition l.1950): also
  called a symmetric premonoidal `[→,Set]`-category, after Power and
  Robinson. It is a symmetric premonoidal category `(𝒫, ⊗, 1)`, a
  symmetric monoidal category `(ℳ, ⊗, 1)`, and an identity-on-objects
  functor `ι : ℳ → 𝒫`. The functor transports the monoidal structure of
  `ℳ` strictly to the premonoidal structure of `𝒫`, and every morphism
  `ι(f)` is central in `𝒫`.
- **Symmetric monoidal duploid** (definition l.1975, dual at
  l.1981–1985): a (positive) symmetric monoidal structure `(⊗, 1)` on a
  duploid `𝒟` is a symmetric monoidal Freyd structure
  `(𝒫_t, ⊗, 1) → (𝒫, ⊗, 1)` for the inclusion `𝒫_t ↪ 𝒫`. The dual
  negative structure `(𝒟, ⅋, ⊥)` is a symmetric monoidal Freyd
  structure `(𝒩_l, ⅋, ⊤) → (𝒩, ⅋, ⊤)` for the inclusion `𝒩_l ↪ 𝒩`. The
  source writes the unit as `⊥` in the first phrase and as `⊤` in the
  Freyd structure.
- **Adjunctions and symmetric monoidal duploids** (theorem l.1988):
  every non-associative category associated to an adjunction
  `L : 𝒜 ⇄ ℬ : R`, where `𝒜` is symmetric monoidal and the monad
  `T = R∘L` is strong, carries a (positive) symmetric monoidal duploid
  structure. Conversely every (positive) symmetric monoidal duploid
  induces the adjunction `𝒫_t ⇄ 𝒩_l` of the theorem at l.1857, with
  `𝒫_t` symmetric monoidal and its associated monad strong.
- **Thunkable implies central, and the converse fails** (proposition
  l.2074, counterexample l.2081–2090): every thunkable map is central,
  because `⇓` preserves thunkability, so `⇓f` is also thunkable, and
  thus central for `⊗⁺`. The converse fails. In the symmetric monoidal
  duploid of the finite-distribution monad `T : Set → Set`, `T` is
  commutative, so every map is central. The maps into positive
  objects that are thunkable are exactly those of the form
  `x ↦ |b(x)⟩`, the Dirac distribution at `b(x)`.
- **Adjunction between graph morphisms** (definition l.2106): for graph
  morphisms `F : 𝒟 ⇀ ℰ` and `G : ℰ ⇀ 𝒟` between non-associative
  categories, an adjunction between graph morphisms (written
  `F : 𝒟 ⇌ ℰ : G`) is an isomorphism of graph morphisms
  `φ : ℰ(F−,=) ≅ 𝒟(−,G=)`, natural component-wise. Naturality means
  `Gg ∘ φ(f) = φ(g ∘ f)` and `φ(f) ∘ h = φ(f ∘ Fh)`, for every
  `f ∈ ℰ(FX,Y)` and all morphisms `g` of `ℰ` and `h` of `𝒟`. `F` and
  `G` are graph morphisms only, so this is weaker than an adjunction of
  functors.
- **What a graph adjunction preserves** (proposition l.2133): for such
  an adjunction, (1) `F` preserves thunkability and `G` preserves
  linearity. (2) For morphisms `f`, `g` of `ℰ`, `G(f ∘ g) = Gf ∘ Gg`
  holds if and only if `f ∘ g ∘ ε_X` associates, where
  `ε_X := φ⁻¹(id_{GX})`. That holds for instance whenever `f` is linear
  or the domain of `g` is negative. The dual statement holds for `F`
  and `η_X = φ(id_{FX})`.
- **Duploid as a graph adjunction** (proposition l.2154–2160): a
  duploid `𝒟` is the same thing as a non-associative category in which
  every object is positive or negative (or both). The extra data is a
  left adjoint `⇓` and a right adjoint `⇑` to the identity graph
  morphism `Id_𝒟`, with `⇓A` positive and `⇑A` negative for every
  object `A`.
- **Strong monoidal functor of duploids** (definition l.2615): a strong
  monoidal functor `F : (𝒟, ⊗, 1) → (ℰ, ⊗, 1)` between symmetric
  monoidal duploids is a duploid functor `𝒟 → ℰ` with a family of
  thunkable and linear isomorphisms `m_{X,Y} : FX ⊗ FY → F(X ⊗ Y)` and
  `m_1 : 1 → F(1)`. The family is natural in each component
  independently and makes the same coherence diagrams commute as in the
  monoidal-category case.
- **Monoidal equivalence** (definition l.2640): take strong monoidal
  functors `F : 𝒟 → ℰ` and `G : ℰ → 𝒟` between symmetric monoidal
  duploids. The pair is a monoidal equivalence when there exist
  families of thunkable and linear isomorphisms `ν_X : F(GX) → X` and
  `ν'_X : G(FX) → X`, both natural in `X` and compatible with the
  respective `m_{X,Y}` and `m_1`.
- **Dialogue duploid** (definition l.2651): a duploid `𝒟` with a
  positive and a negative symmetric monoidal duploid structure,
  `(𝒟, ⊗, 1)` and `(𝒟, ⅋, ⊥)`, related by a strong monoidal equivalence
  `(−)* : (𝒟, ⊗, 1) ≃ (𝒟, ⅋, ⊥)^op`. It also carries a family of
  adjunctions `− ⊗ Y ⊣ Y* ⅋ −` between graph morphisms, called
  *currification*, `χ_{X,Y,Z} : 𝒟(X ⊗ Y, Z) ≅ 𝒟(X, Y* ⅋ Z)`, natural
  component-wise in `X`, `Y` and `Z`. Up to monoidality, symmetry and
  associativity, `χ` satisfies
  `χ_{A,B⊗C,D} = χ_{A,B,C*⅋D} ∘ χ_{A⊗B,C,D}`. An associative dialogue
  duploid is the same thing as a `*`-autonomous category (l.2674–2675).
- **Dialogue duploids and dialogue chiralities** (theorem l.2681):
  every duploid associated to a dialogue chirality `L ⊣ R` carries a
  dialogue duploid structure. Conversely every dialogue duploid `𝒟`
  induces a dialogue chirality structure on the adjunction
  `𝒫_t ⇄ 𝒩_l`, and the dialogue duploid associated to it is equivalent
  to `𝒟` via strong monoidal duploid functors that also preserve the
  duality.
- **The Hasegawa-Thielecke theorem** (l.3044): in a dialogue duploid, a
  morphism is central for `⊗` if and only if it is thunkable. The
  abstract adds that this covers any double-negation monad on a
  symmetric monoidal category (l.442–443). The proof rests on writing
  `g ∘ f` by internal duality (l.3051–3060). A direct equational proof
  is in the appendix (l.4845).
- **Syntactic Hasegawa-Thielecke theorem** (theorem l.3080): an
  expression of the linear classical *L*-calculus is syntactically
  central for `⊗` if and only if it is syntactically thunkable.
- **Two monad equivalences** (l.3110–3116 and l.3123–3128): the source
  states both in boxed display, with no numbered environment. For a
  duploid `𝒟` associated to an adjunction `L ⊣ R`, the monad `R∘L` is
  idempotent if and only if every morphism of `𝒟` is thunkable. For a
  symmetric monoidal duploid `𝒟` associated to `L ⊣ R` with `𝒜`
  symmetric monoidal and `T = R∘L` strong, `T` is commutative if and
  only if every morphism of `𝒟` is central.
- **Hasegawa's corollary** (corollary l.3134–3136): the continuation
  monad of a dialogue category is commutative if and only if it is
  idempotent. The source attributes the statement to Hasegawa, by way
  of Melliès and Tabareau, and derives it from the syntactic theorem
  for a dialogue duploid associated to a dialogue category.
- **Linearly distributive duploid** (definition l.3154–3163): a duploid
  with a pair of positive and negative symmetric monoidal structures.
  The two are related by a family `A ⊗ (B ⅋ C) → (A ⊗ B) ⅋ C`, natural
  component-wise, respecting the usual coherence diagrams for a
  linearly distributive category (Cockett and Seely). An associative
  linearly distributive duploid is the same thing as a linearly
  distributive category.
- **The `⅋`/linear refinement** (l.3165–3170): the source *suggests*,
  rather than proves, a dual refinement. A variant of the syntactic
  argument in Munch-Maccagnoni's thesis (p.262) suggests that in any
  linearly distributive duploid which is closed, a morphism is central
  for `⅋` if and only if it is linear. Closed here means an
  isomorphism `𝒟(X ⊗ Y, Y' ⅋ Z) ≅ 𝒟(X, (Y ⊸ Y') ⅋ Z)`, natural in `X`,
  `Y'` and `Z` component-wise. This is a different statement from the
  `⊗`/thunkable theorem at l.3044.

## What the source establishes

A direct-style semantics for polarised classical computation in which
non-associativity is structural rather than defective: non-associative
categories with the thunkable/linear vocabulary, duploids and their
symmetric monoidal and dialogue refinements, the correspondence with
adjunction models and dialogue chiralities, an interpretation of the
linear classical *L*-calculus together with a syntactic dialogue
duploid, and the Hasegawa-Thielecke theorem identifying the maps
central for `⊗` with the thunkable maps there. Published in PACMPL
(POPL 2026). Every
mathematical claim recorded here is CONJECTURED until machine-checked
in this repository.
