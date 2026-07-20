# Plan — 2026-07-20 — the interchange displacement

Ruling (Lane): **`⊗₁-interchange♭` becomes the `monoidal-axioms₁`
field**, mirroring the settled level-0 design — flat interchange as
the record field, pointwise as its `nrm`-shadow. This closes the
open question from the 07-19 API note ("decide whether level 1
wants the ♭ shape when the displaced pentagon needs interchange at
witness composites"; the ⋉-form pentagon didn't need it, deferring
the decision to the interchange-coherence displacement — which is
next).

## Why the flat field

- The level-0 experiment (07-14) ran both directions and settled
  it: fields are neutrals; deriving flat from pointwise closes over
  the emb-fibers by two J's and computes on `nrm` instances only
  propositionally (the J lottery). A pointwise level-1 field would
  rebuild that problem one grade up.
- The displacement's statement forces it: `interchange-natural`'s
  proof is the cube `λ j i → interchange♭ (●-coh U V i) W j` —
  interchange applied at a *generic interval point of a witness
  line*. That needs interchange-at-arbitrary-witnesses as a single
  neutral function; the pointwise form cannot state the cube, and a
  derived closure is neither neutral nor definitionally equal to
  the pointwise field at `nrm`s.
- Timing: the only live instance site is the `monoidal` bundle
  itself. The old-formulation `{Twist,Braid,Hexagon,Iso,
  Indiscrete}` are not on the new spine yet, so the field changes
  before instances multiply, and the ports inherit the final shape.

Routing around ♭ (the pentagon precedent) was considered and
rejected without a spike: interchange-coherence is *about* the
`●`/`○` crossing at compound witnesses, and the naturality cube's
generic-point application has no `nrm`-only form.

## The plan

1. **`Cat.Monoidal`: the field swap.** `⊗₁-interchange♭` replaces
   `⊗₁-interchange` as the `monoidal-axioms₁` field: level-1
   witnesses to a `PathP` over the `⊗₀-interchange♭` lines on both
   sides, relating the `▿₁`/`▵₁` composites — the displaced mirror
   of `interchange♭ : is-representable A → is-representable B →
   A ▿ B ≡ A ▵ B`. The exact witness indexing available at the
   axioms record (before `theory₁` exists) is the first thing to
   pin in-session. Pointwise `⊗₁-interchange` keeps its name and
   type as the definitional shadow at `⊗₁`-normal forms — the base
   line collapses by `⊗₀-interchange♭ (⊗₀-nrm x) (⊗₀-nrm y) ≐
   ⊗₀-interchange x y`, so `⊗₁-spine` and all downstream consumers
   are no-ops. `⊗₁-interchange♭-from` (mirror of
   `⊗₀-interchange♭-from`) gives pointwise-only instance builders
   their route back. Re-check the bundle, `Bifunctor`, `Coherence`.

2. **Displace `interchange-coh`.** `●₁-coh` as `is-prop→PathP` at
   the level-1 witness family over the flat line;
   `⊗₁-interchange-natural` as `Path.commutes` on the interchange
   cube; the `ι-mult-r`/`ι-mult-l` statements one grade up. Same
   two-liner shapes as `Cat.Coherence`'s `interchange-coh`, under
   the grade dictionary; lives beside its consumers (default:
   `Cat.Monoidal.Coherence`, free to move if the hexagon wants it
   earlier in the chain).

3. **The hexagon/braid ports** (07-19 strategy) on the resulting
   shape, with the audit's disciplines from the start: sealed
   σ-heads for any new canonical identification a family will
   ride, displacement as `σ[_]`-instances, named faces — bottoms
   *and* sides — and fills whiskered on the argument side wherever
   the tree allows.

## Checks that gate each step

- After step 1: the shadow's agreement is definitional (no `refl`
  bridge, no J) — `⊗₁-interchange φ ψ` must typecheck as
  `⊗₁-interchange♭` at normal forms with no coercion; consumers
  re-check untouched.
- After step 2: every interface in the displaced module is
  definitional (the leaf-for-leaf discipline); cold profile against
  the module totals, per the audit's reading rules.
