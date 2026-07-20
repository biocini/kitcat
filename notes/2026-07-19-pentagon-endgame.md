# Session log — 2026-07-19 — pentagon endgame

Objective: the roadmap's step 1 — from `pentagon⋉₁` to the
canonical `⊗₁-pentagon` over `⊗₀-pentagon`, edges the
`comp-pathp₂`-composites of whiskered `⊗₁-assoc` lines.

Branch: `monoidal-visible-frames`.

## What was done / strongest findings

The endgame closed with **zero new hcomp squares in the monoidal
modules**: every leaf of `⊗₀-pentagon`'s `∙`-tree displaces by
construction, and the glue is `comp-pathp₂` at the family of
pentagon fillers `λ p p' → PathP (λ i → C.hom (p i) (p' i)) A₅ A₁`.
Two instruments made this possible; both are one-construction
moves, and every proof in this session was a first-attempt
typecheck.

- **The nrm-slide replaces the triple-J.** `assoc⋉₀-nrm` was a
  triple-J straightening whose displacement would have needed the
  dependent double-J cluster. Redefinition: slide each witness
  along its own path with an `∧`-connection —
  `nrm-slide₀ U m = U .fst , λ k → U .snd (k ∧ ~ m)` — and apply
  `assoc⋉₀` pointwise. At `m = i0` the slide is the witness itself
  (path-eta + Σ-eta), at `m = i1` the normal form (the witness
  path's typed boundary), so both endpoints are definitional and
  the planned `∙ refl`-redex discharge (`Path.unitr`, from the
  `⋉₀`-vs-nest mismatch) evaporates: the connection collapses any
  compound witness path to `refl` at `m = i1` regardless of shape.
  The displacement is then *forced*: `assoc⋉₁-nrm` is the same
  slide one level up (`nrm-slide₁` on the `⊗₁-wit`
  characterization), landing on `⊗₁-assoc` definitionally because
  `⊗₁-assoc` *is* `assoc⋉₁` at `⊗₁-wit-nrm`s. This is the
  one-construction principle producing a *square*: both edges of
  the straightening are one projection at sliding witnesses.

- **`comp-pathp₂-ap`** (`Core.Path.Base`): the displaced `ap-comp`.
  A `comp-pathp₂` at a reindexed family `λ a b → F (f a) (g b)`
  over base paths equals the `comp-pathp₂` at `F` over the
  `ap`-images, as a square over the two `ap-comp` shuffles. Proof:
  re-run the `com` with its type line taken along `HComposite.coh`
  — the coherence between `ap-comp`'s two fillers — whose
  `m = i0`/`i1` slices are the two `comp-pathp₂` lines
  definitionally (the `hcom` φ-reduction at the cube's ends) and
  whose lid is `ap-comp` itself (typed boundary of the nested
  `HCell`-PathP). This discharges all three `ap fst`-shuffle
  leaves at once, because `⊗₁-wit-∙` assembles its `fst` as
  exactly the reindexed `comp-pathp₂`: the shuffle square's two
  ends are two readings of the same composite.

- **Back-port to `Cat.Coherence`** (the transcription source repays
  its debt): `assoc⋉-nrm`'s triple-J is now the `nrm-slide`
  connection form, the pentagon's leaves are named
  (`step₁`–`step₄`, `whisker₁`–`whisker₃`), and the instance
  module is `pentagon` (the `triangle`-module precedent), staging
  the displayed pentagon, which must ride this tree. The
  elementary transport-only form is preserved verbatim in
  **`Cat.Coherence.Gloss`** — one `J` per witness path component
  — as the port source for a standard-MLTT presentation: with the
  straightening in J-form, every other leaf of the pentagon tree
  is already J-expressible. No agreement cell between the two
  forms is stated (bridging two straightenings is the fst-wobble;
  nothing consumes such a bridge). No gated module imports
  `Cat.Coherence`'s pentagon names, so the restructure is
  consumer-safe.

- **`⊗₁-pentagon`** (`Cat.Monoidal.Coherence`, `pentagon₁`): the
  naturality square of the pentagon — over the unprimed and primed
  `⊗₀-pentagon`s, top edge the glued whiskered-`⊗₁-assoc` triple,
  bottom edge the glued pair. Structure: `pentagon₀` (the named
  level-0 instance module, leaves `whisker₃ ∙ pentagon⋉₀ ∙
  whisker₂ ∙ whisker₁`, with `pentagon⋉₀ = step₁ ∙ step₂ ∙ step₃ ∙
  step₄`), displaced leaf-by-leaf: `whisker̂ᵢ` are `assoc⋉₁-nrm`
  slides (congruence-whiskered by pointwise `comp-pathp₂`),
  `step̂ᵢ` are `comp-pathp₂-ap` squares (reversed where the base
  leaf is a `sym`), `step₃`'s mate is `pentagon⋉₁` verbatim.
  Every interface between consecutive leaves is definitional —
  `fst∘σ̂ᵢⱼ` at normal witnesses *is* the whiskered `⊗₁-assoc`
  line, `fst∘top̂`/`fst∘bot̂` *are* the wit-family composites.

## Cubical engineering facts (hard-won, reusable)

- Sealing `fiber-pentagon` (`opaque`, same rationale as
  `assoc-σ⋉₀`) took `pentagon̂⋉` — the core glue, whose `Fam`
  instances project `fiber-pentagon`'s slices under generic
  interval binders — from 3.8 s to 0.24 s; module total 12.7 s →
  9.2 s. The prediction in 07-19-notation ("`fiber-pentagon` is
  the next candidate") was exact.
- The same seal applied to `loop-sq` does **nothing** for
  `triangle₁.Ŝ` (3.7 s, the module's remaining hot spot — its
  cost is not the `loop-sq` projections; profile before sealing).
  Reverted.
- `HComposite.coh`'s entire boundary is definitional: the
  `m`-faces by `hcom` φ-reduction, the square faces by the typed
  boundary of the nested-PathP `HCell`. This is what lets a `com`
  be re-based along it with no reconciliation.

## Verification state

All pass (`--safe --erased-cubical`, Agda 2.9.0):
`Core.Path.Base` and its full cone — `Cat.{Type,Op,Base,
Coherence,Groupoid,Terminal}`, `Cat.Limits.{Product,Coproduct}`,
`Cat.Morphism.Iso`, `Cat.Functor.Adjoint`, `Cat.Monoidal`,
`Cat.Monoidal.{Bifunctor,Coherence}`, `Cat.Displayed`,
`Cat.Displayed.Base`, `Cat.Coherence.Gloss` (new),
`Test.ProductSpike`.
`Cat.Monoidal.Coherence` 9.2 s cold (`triangle₁.Ŝ` 3.7 s of it,
pre-existing). Changes uncommitted.

## Next steps

1. Triangle endgame — `⊗₁-triangle` over `⊗₀-triangle`: the
   displaced `face-r`/`face-l`/`face-a` need displaced
   `repr-∙`/`-refl`/`-ap` and `comp-pathp₂` unitl/unitr fillers;
   assemble leaf-by-leaf as the pentagon's, with `comp-pathp₂-ap`
   covering the `ap-comp` leaves inside `⊗₀-repr-∙`. Check first
   whether any face dissolves by an nrm-slide before building
   fillers.
2. `⋉₁-coh`/`⊗₀-interchange-natural` displacement (the
   `⊗₁-interchange♭` decision point), then the hexagon/braid
   ports per the 07-19 port strategy.
3. The displayed pentagon (`pentagonᴰ` over `Cat.Coherence`'s
   `pentagon`, now staged): needs `comp-pathp₁-ap` (the
   unary-family sibling — one coh-cube instead of two), the
   `⋉ᴰ`-glue over the deferred `comp-pathp₁-over`, and
   `nrm-slideᴰ`; then the tree transcribes leaf-for-leaf. Watch
   for `assoc-σ⋉`/`fiber-pentagon` needing the opaque seal in
   `Cat.Base`/`Cat.Coherence` once displayed families project
   their slices — profile first, as with `loop-sq`.
4. `Cat.Displayed` follow-ons unchanged (∫ spike,
   square-level displaced repr calculus).
