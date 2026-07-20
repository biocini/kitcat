# Session log — 2026-07-19 — wit-calculus naturality, displaced triangle, Cat.Displayed

Objective: `assoc⋉₁-nrm` (the roadmap's shared bottleneck), then
`triangle₁`; then, on Lane's direction, a concrete `Cat.Displayed`
draft while the wit-calculus experience was fresh.

Branch: `monoidal-visible-frames`.

## What was done / strongest finding

- **`assoc⋉₁-nrm` dissolved into a definition.** The planned lemma
  related `assoc⋉₁` at `⊗₁-nrm` witnesses to the θ-based `⊗₁-assoc`.
  Every proof route tried (canonical-lift uniqueness through the two
  families, family interpolation, J-straightening, fiber-square
  transport) reduces to one obstruction: a level-0 cube relating the
  opaque `assoc-σ⋉₀` witness-path square to `sq-from-∙ (assoc-ap)`'s
  square. The cube's interior is not prop-fillable — fst-fibers of the
  contractible representability fiber are path spaces in `C.ob`, not
  props — so it could only be built by uncompressing `ap-fst-fiber`'s
  path algebra at the square level. The transcription discipline
  resolves it instead: at level 0 the associator *is* `assoc⋉₀` at
  `⊗₀-nrm`s, definitionally; the θ-based `⊗₁-assoc` (commit `1fee68b`)
  simply predated the wit calculus (`58ee03e`). Now
  `⊗₁-assoc := assoc⋉₁` at `⊗₁-wit-nrm`s — same type, no lemma, and
  the associator θ-plumbing (`nestL`, `nestR`, `nestL₁`, `nestR₁`,
  `assoc-ap`, `assoc-sq`, `assoc-line`) is deleted.
- **The wit-level repr-calculus** (the analogues predicted for
  `triangle₁`) in `theory₁`'s witness-calculus section:
  `⊗₁-wit-nrm`; `_↝̂_` (displaced `_↝_`, `comp-pathp₂` as `∙`);
  opaque `⊗₁-wit-σ` (the displaced propositionality path:
  `is-prop→PathP` through pointwise `⊗₁-wit-contr`, transported along
  the `i ∧ k` connection — the `assoc-σ⋉₁` pattern generalized to
  arbitrary level-0 prop-paths); `⊗₁-wit-unique` (its hom component,
  the displaced `⊗₀-repr-unique`). `assoc-σ⋉₁` is now `⊗₁-wit-σ`'s
  instance at the `⋉₁`-bracketings, a one-liner sealed over
  `assoc-σ⋉₀`.
- **Unitors collapsed onto the wit calculus** by the same argument:
  `⊗₀-unitr`/`⊗₀-unitl` are `⊗₀-repr-unique` at `⋉₀`/`↝`-witnesses,
  so `⊗₁-unitr`/`⊗₁-unitl` are `⊗₁-wit-unique` at the `↝̂`-transports
  of the normal pairings along `▾₁-idn` / `⊗₁-emb-idn-absorb`. The
  θ-recipe survives in its one irreplaceable role:
  `⊗₁-emb-image-contr` keeps `unitl-ap`/`unitl-sq`/`unitl-line`;
  the `unitr-*` trio is deleted.
- **`triangle₁`** (`Cat.Monoidal.Coherence`): the `⋉`-form displaced
  triangle. `r̂₁ r̂₂ r̂₀¹ r̂₀² ŝ₀ ŝ₁ ŝ₂` as `⊗₁-wit`s (`⋉₁` at normal
  witnesses, `↝̂` along the reversed `ê`-lines); `face₁-r`/`face₁-l`/
  `loop₁` as `⊗₁-wit-unique` lines over their level-0 mates;
  `assoc-eq₁` the displaced `assoc-eq` — a constant square under
  unfolding, one level up from `assoc-eq = refl`; `loop₁-refl` the
  displaced `loop-refl` and `is-coh₁`'s first consumer: `triangle₀`
  gained `loop-sq` (the factored fiber square `loop-refl` projects),
  and the level-1 square is `is-prop→SquareP` at the wit family over
  that same `loop-sq`, with far edge `ĉ` the `↝̂`-image of the
  coherence square — `is-coh₁ φ ψ (~ i) (~ t)` feeds `_↝̂_` directly,
  validating the field shape.

## `Cat.Displayed` — the representable presentation, displaced

From Lane's sketch, corrected against the current source and this
session's findings, and checked in full — no holes:

- **`Cat.Displayed`** (mirrors `Cat.Type` column for column):
  `reflexive-graphᴰ` (`ob[_]`/`hom[_]`/`idn[_]`), `virtualᴰ` (the
  context calculus Σ-by-Σ; `composite[_]` with the base context a
  VISIBLE Π per the 7755ce7 discipline — the sketch had it hidden —
  and `_$ᴰ_` as the implicit applicator), `representableᴰ`
  (`is-representable[_]` as the fiber of `emb[_]` over a base
  witness — the general form of `⊗₁-wit` with the squared base
  collapsed to one witness; `nrm[_]`, `pre[_]`/`post[_]`/`sub[_]`/
  `cosub[_]`, and the operator calculus under current names:
  `_▾ᴰ_ _▴ᴰ_ _▿ᴰ_ _▵ᴰ_`, not the sketch's pre-ffd2741
  `·`-family), `category-axiomsᴰ` (fields `emb[_]`,
  `interchange♭ᴰ` in ♭ form over displayed representables,
  `spineᴰ-contr`, `unitᴰ`; `_⨾ᴰ_` and the spine projections
  derived; `theory C` opened — the spine displaces over derived
  theory; no enrichment field, confirming `⊗₁-emb-⨾` as
  double-categorical data), `categoryᴰ`.
- **`Cat.Displayed.Base`** (`theoryᴰ`, mirrors `Cat.Base`):
  `hom≃total-representableᴰ`; `hfiberᴰ` with both Kan-lid boxes and
  `pull-contrᴰ`/`push-contrᴰ` (the base's plain-path `cat.fill`
  extension becomes the `fil` box, as in `⊗₁-hfiber`);
  `cast-pathᴰ`/`cast-path⁻¹ᴰ`; the displaced unit chain
  (`comp-eq-evᴰ/preᴰ/postᴰ`, `pre-is-postᴰ`, `absorb-lᴰ/rᴰ`) by
  `comp-pathp₁` links whose base sides mirror the `Cat.Base` terms
  exactly, so the types match definitionally; `idn-▴ᴰ`/`▾-idnᴰ`
  as direct interval terms; `emb-idn-absorbᴰ`; `unitl-ap` (the
  base-theory computation of `ap emb (unitl f)`, token-ported from
  Bifunctor's) with `sq-from-∙`/`unitl-line` giving
  `emb-image-contrᴰ`; then the displaced witness calculus
  (`repr-contrᴰ`, opaque `repr-σᴰ`, `repr-uniqueᴰ`, `_⋉ᴰ_`,
  `_↝ᴰ_`) and the identities as one-construction projections:
  `assoc-σ⋉ᴰ` is `repr-σᴰ` at the `⋉ᴰ`-bracketings (no unfolding
  gymnastics — base `assoc-σ⋉` is transparent), `assocᴰ` is
  `assoc⋉ᴰ` at `nrm[_]`s, unitors are `repr-uniqueᴰ` at
  `↝ᴰ`-transports. Finally `cartesian`: `is-cartesian`/
  `is-cocartesian` in CPS form (one `emb[_]` application),
  `idn-cartesian` by transporting `id-equiv` along `absorb-rᴰ`,
  `cartesian-lift`/`is-fibration`, with the non-contractibility of
  lifts noted as a displayed-univalence condition, not a theorem.
- **`Core.Kan` gains `comp-pathp₁`** — the unary-family sibling of
  `comp-pathp₂` (the displayed families `hom[_] x' y'`/
  `composite[_] x' y'` are unary where the monoidal ones were
  binary). The existing `comp-pathp` (type-path version) does not
  serve: its line is `(A ∙ B) i`, not `F ((pa ∙ qa) i)`, and the
  gap is an `ap-comp` redex per glue.
- Deferred, recorded in the module prose: `interchange♭-fromᴰ`
  (instance sugar, double dependent J — with the J-straightening
  cluster), the square-level displaced repr calculus
  (`repr-lc/-refl/-ap/-∙/↝-repr`ᴰ) and `⋉ᴰ`-line gluing (needs
  `comp-pathp₁-over`), and the total category `∫` — the `split`
  Σ-reshuffle is the one genuine obligation and gets a `Test/`
  spike first (`ProductSpike` precedent; the total spine lives in
  Π-into-Σ, so its contractibility transfer must be assembled with
  `-over` gluers, never projected).

## Cubical engineering facts (hard-won, reusable)

- Type signatures inside an `opaque unfolding` block are checked
  WITHOUT the unfolding; only bodies get it. A displaced statement
  whose *type* needs a sealed path unfolded must be restated over the
  level-0 opaque 2-cell instead: `assoc-eq₁` is a square over
  `T.assoc-eq` with a constant body, under
  `unfolding assoc-σ⋉₀ assoc-σ⋉₁ T.assoc-eq T'.assoc-eq`.
- The fst-wobble: any bridge between two prop-lifts obtained by
  free-filling squares in the contractible fiber has an uncontrolled
  fst-interior, and `C.ob` is untruncated, so it cannot be killed
  after the fact. Displaced statements must ride the *same* level-0
  fiber squares their level-0 mates project — hence the `loop-sq`
  factoring, which makes the base agreement definitional. This is the
  criterion separating the `⋉`-form displacements (free) from the
  canonical-form endgames (leaf-by-leaf gluing along the level-0
  `∙`-trees).

## Design decisions

- Grading over lemma-bridging: when a level-0 identity is a
  wit-calculus projection, its level-1 mirror is *defined* as the same
  projection one level up, never proven equal to an independent
  construction after the fact.
- Naming, settled (Lane): at the displayed-general level, bracket
  names only where an argument fills the bracket; displaced infix
  operators take the `ᴰ` suffix on their base mates' glyphs
  (`_▾ᴰ_`, `_⨾ᴰ_`, `_⋉ᴰ_`, `_↝ᴰ_`, `_$ᴰ_`). At the monoidal
  instance `_↝̂_` keeps the circumflex ("the level-1 lift of");
  `_↝₁_` remains the plain-fiber transport.

## Verification state

All pass (`--safe --erased-cubical`, Agda 2.9.0):
`Cat.Monoidal.Bifunctor` 6.3 s (was 2.5 s — the unitor types now
convert level-0 prop-path towers; the sealed-σ mitigation from
07-19-notation applies if this grows), `Cat.Monoidal.Coherence`
3.4 s warm, full cold cone 17 s including the `Core.Kan` change.
`Cat.Displayed` + `Cat.Displayed.Base` 5.3 s cold for the pair —
the opaque `repr-σᴰ` keeps the identity instantiations cheap.
Changes uncommitted.

## Next steps

1. Pentagon endgame — now unblocked with no `assoc⋉₁-nrm` needed:
   the whiskered `⊗₁-assoc` edges ARE `assoc⋉₁` lines, so the
   `comp-pathp₂`-composites connect to `pentagon⋉₁` directly.
   Remaining: displace the `ap-comp` shuffles and the `assoc⋉₀-nrm`
   triple-J straightenings, per the 07-19-notation plan.
2. Triangle endgame — `⊗₁-triangle` over `⊗₀-triangle`: the displaced
   `face-r`/`face-l`/`face-a` identifications need displaced
   `repr-∙`/`-refl`/`-ap` and `comp-pathp₂` unitl/unitr fillers (the
   com→fil trick mirroring `Path.unitr p i j = cat.fill p refl j (~ i)`),
   assembled leaf-by-leaf like the pentagon's.
3. `⋉₁-coh` / interchange-coherence displacement; then the
   hexagon/braid ports (`old-formulation-curried/Monoidal/`
   `{Twist,Braid,Hexagon}`). Port strategy, per the dissolution
   finding: before bridging two constructions of any displaced
   braided cell, check whether the wit calculus *defines* it — a
   calculus projection at normal witnesses over the level-0 cell,
   the `⊗₁-assoc`/unitor pattern. The curried form's `absorb-coh`
   layer, noted irreducible there, is the first candidate; expect
   part of it to evaporate. The hexagon's need for interchange at
   witness composites is the `⊗₁-interchange♭` decision point —
   `category-axiomsᴰ`'s ♭ field is the principled general shape.
4. `Cat.Displayed` follow-ons: the `∫` spike (`split` +
   `∫-spine-contr` in `Test/` before any module commitment),
   `comp-pathp₁-over` + the `⋉ᴰ`-line gluer, the square-level
   displaced repr calculus, `interchange♭-fromᴰ`. Also decide the
   file split (`Cat.Displayed.Cartesian`?) and whether the moral-
   instance dictionaries should live as prose beside
   `monoidal-axioms₁`.
