# Session log — 2026-07-20 — the refinement audit

Objective: the roadmap's step 1 — the refinement audit over the
existing modules: the two open questions from the displayed-triangle
note (the `Miscellaneous` profile bucket, `pentagon̂●`'s glue shape)
and the remaining ≥200 ms definitions (`unitr-op`, `↝₁-repr`, the
ρ̂/face-σ̂a/σ̂ chains). Ruling standing from the previous session:
getting this layer right comes before hiking up a dimension.

Branch: `monoidal-visible-frames`.

## What was done / strongest findings

- **The Miscellaneous bucket, decomposed.** `Test.MiscFloor-20260720`
  (a trivial module with `Cat.Displayed.Coherence`'s import list)
  cold-checks in ~290 ms — the import floor is deserialization only.
  The rest of the coherence modules' ~2.8 s bucket is their own
  code: `--profile=internal` splits it into signature elaboration
  (~0.7 s), occurs checks (~0.4 s), record positivity (0.48 s for
  `is-2-coherentᴰ`, 0.16 s monoidal), interface serialization
  (~0.25 s), and section application. Nothing hides there that the
  per-definition ranking doesn't already surface; positivity of the
  displayed coherence record is the one notable fixed cost, and
  `--safe` forecloses the pragma.

- **Attribution bills the first forcer.** The audit's decisive
  reading rule, found the hard way: `ρ̂r` profiled at 264 ms in situ
  but 74 ms when reproduced verbatim in a probe. The difference was
  `face-σ̂a`'s inline sides `(λ m → ρ̂l/ρ̂r (~ m))` — an η-wrapped
  reversal of a named line is still an inline face, and its
  re-elaboration is billed to the line it applies. Naming the sides
  dropped `face-σ̂a` 240→37 and `ρ̂r` 264→74 with no change to `ρ̂r`
  itself. Fixing a hotspot also surfaces conserved work under new
  accounts downstream (monoidal `ĉ` <26→215, `⊗₁-pentagon`
  127→265): per-definition numbers rank suspects; only module
  totals over repeated cold runs confirm a fix (totals are stable
  to ~1%; attributions reshuffle freely). Both rules are in the
  styleguide now.

- **`unitr-op` off the seals.** The last `opaque unfolding` block
  retired by the generalize-and-specialize discipline: `repr-op[_]`
  is the op mirror of a witness line generalized over the line —
  `κ` consumed as a neutral family, `rep-op'` preserving `fst`
  definitionally — so `unitr-op` reads both unitors at their sealed
  σ-heads (`repr-op[ Tᵒ.unitr-σ● f ]`, `repr-lc (unitl-σ● f)`)
  with `repr-cast` carrying the op-bridge `wit` between the stated
  witnesses. The `wit` chain is untouched; the `repr-∙`/`repr-refl`
  legs and the unfolding fall away together. 450→186 ms, `repr-op`
  (223 ms) subsumed, `mult→3coh` 118→22 as a side effect;
  `Cat.Coherence` 1.9→1.47 s.

- **The whisker orientation.** `Test.RhoProbe-20260720`'s 2×2
  (absorber × side): `_▿_` plugs its left operand in head position,
  so a Kan filler slid into the left slot of a whisker is an `hcom`
  applied at function type — every conversion pushes the argument
  into the faces. Fill-left 74 ms against fill-right 23 on mirror
  whiskers of the same slide; 450 when the slid path is an ∙-chain
  (`emb-idn-absorb`) rather than a record field (`▾-idn`). Naming
  the filled operand and generalizing the whisker into a combinator
  (`↝ᴰ-fill-●r`, probe-only) both measured null — the cost is the
  instance conversion, not the elaboration site. The triangle
  already sits in the cheap cells: `ρ̂r` rides the neutral field
  left, `ρ̂l` the chain right; 74 ms is `ρ̂r`'s structural floor.

- **`↝-repr` projects the prop-path.** The slide preserves `fst`
  definitionally, so the slid line's shadow is the shadow of the
  slid propositionality path: `sym (repr-lc (λ i → prop i ↝ e))`
  replaces the J-transport at all three grades (base, `⊗₀`, `⊗₁` —
  kept mirrored). `↝₁-repr` 278→169 ms at the two-sided family;
  `Bifunctor` 1.6→1.44 s. Same family as `repr-op[_]`: when the
  conclusion is a `fst`-shadow and the operation preserves `fst`,
  whisker the prop-path and project — never transport.

- **`pentagon̂●` ruled inherent.** The remaining cost is the glue
  seams of the nested `comp-pathp₂` at the two-sided `Fam` —
  naming was measured null last session, the general-combinator
  route is the same null by the RhoProbe result, and no glue shape
  presents itself that isn't a new Kan primitive with no expected
  payoff. It stands as the pentagon's floor at both grades, with
  the monoidal loop boundary (`ĉ`, the `K`-family's stated faces)
  the same class of structural cost.

- **Monoidal side-naming kept on symmetry.** The displayed
  side-naming is a real −145 ms (6,406→6,262 median-of-3); the
  monoidal mirror is measured-neutral (5,829→5,913, redistribution
  only). Kept so `triangle₁` and `triangleᴰ` stay leaf-for-leaf
  identical and because the roadmap's step 2 makes named faces the
  standing discipline for the ports; the honest number is recorded
  here.

## Cubical engineering facts (hard-won, reusable)

- An η-wrapped reversal of a named line is an inline face. The
  named-face norm covers sides, not just bottoms; `refl` sides are
  exempt (small terms).
- A composition that applies its left operand puts left-slot Kan
  fillers in head position; conversion reduces the hcomp at
  function type per face. Prefer the argument slot when a mirror
  choice exists; accept the floor when endpoints force the
  orientation.
- Per-definition profiling attributes conversions to the first
  forcer. A definition's number is not its own cost; module totals
  over repeated cold runs are the only confirmation. Cold totals
  here are ~1%-stable; single definitions swing 3× between runs
  under code changes elsewhere in the module.
- J over a path in a propositional fiber is never needed for
  `fst`-shadow equations when the operation preserves `fst`:
  whisker the prop-path, project, `sym` as needed. The J-form
  re-elaborates the family at the transported index.
- The import floor of a coherence-sized module is ~0.3 s of
  deserialization; `Miscellaneous` beyond that is the module's own
  signatures, occurs checks, record positivity, and serialization.

## Measured, final

`Cat.Coherence` 1,916→**1,467 ms**; `Cat.Displayed.Coherence`
6,406→**6,262 ms** (median of 3, against the same imports);
`Cat.Monoidal.Bifunctor` 1,623→**1,442 ms**;
`Cat.Monoidal.Coherence` **5,913 ms**, neutral. Net ≈ −0.77 s
cold across the four, with zero `opaque unfolding` blocks left in
the library and attribution now honest at the triangle grades.
Remaining ≥150 ms definitions are all ruled structural: the
pentagon glue seams (`pentagon̂●`, `⊗₁-pentagon`,
`fiber-pentagon`), the compound-argument `assoc-σ●` instances
(`σ̂₄₁`/`σ̂₃₂`/`σ̂₅₄`), the monoidal loop boundary (`ĉ`), and
`unitr-op`'s residual op-instantiation (186 ms).

## Verification state

All pass (`--safe --erased-cubical`, Agda 2.9.0): `Cat.Base`,
`Cat.{Op,Terminal,Groupoid,Coherence}`, `Cat.Coherence.Gloss`,
`Cat.Limits.{Terminal,Product,Coproduct,Equalizer,Pullback}`,
`Cat.Morphism.Iso`, `Cat.Functor.{Adjoint,NatTrans}`,
`Cat.Monoidal`, `Cat.Monoidal.{Bifunctor,Coherence}`,
`Cat.Displayed`, `Cat.Displayed.{Base,Coherence}`,
`Test.ProductSpike`, and the probes. `Data.Thin.Category` and
`All.lagda.md` stale as before, queued with the chores. Committed.

## Next steps

1. Roadmap step 2: `●₁-coh`/`⊗₀-interchange-natural` displacement
   (the `⊗₁-interchange♭` decision point), then the hexagon/braid
   ports per the 07-19 strategy — σ-spine, `σ[_]`-instances, and
   named faces (bottoms *and* sides) from the start; fills
   whiskered on the argument side wherever the tree allows.
2. Roadmap step 3: `Cat.Displayed` follow-ons (∫ spike, the
   displaced repr calculus — `repr-lc`/`repr-refl`/`repr-ap`/
   `repr-∙`/`↝-repr` one level up; the prop-path-projection forms
   are the ones to displace).
3. The deferred chores after the module phase: fence tagging, lint
   sweep, `Data.Thin.Category`'s `spine-contr` rename fallout,
   `All.lagda.md` sync.
