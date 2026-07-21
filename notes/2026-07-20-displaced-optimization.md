# Session log — 2026-07-20 — the displaced-layer optimization pass

Objective (ruling, Lane): before any further module work, an
optimization audit of the displaced coherence layer in the mold
of the 07-20 refinement audit. Trigger: `Cat.Monoidal.Hexagon`
cold-checking at 13,250 ms (single run) against its 866 ms
level-0 baseline, `Coherence` at ~6.3 s. Protocol: per-definition
profiles rank suspects, median-of-3 cold module totals are the
only confirmation, every change semantics-preserving, wins and
nulls both recorded.

Branch: `monoidal-visible-frames`.

## Baselines (median-of-3 cold, this machine, this session)

`Hexagon` 13,723 ms · `Coherence` 6,516 ms · `Braid` 493 ·
`Indiscrete` 449 · `Iso` 311 · `Twist` 469 ·
`Core.Path.Base` 735.

## The decisive finding: name the chain, not the leaves

The dominant cost of the displaced hexagon was not the Kan
machinery — it was the *spelling*. The traversal composites
(`ℓ-assoc₁ ∙ ℓ-braid ∙ ℓ-assoc₂`, `μ ∙ r-braid₁ ∙ r-assoc ∙ ρ ∙
r-braid₂`, and their tails) were re-spelled inline in every
ascription that indexes a family by them — the `⊗₁-wit-∙` glue
chain, the `E`/`R`/`S`/`T` ladder, `top̂`/`bot̂`, the canonical
trees — and each spelling is elaborated at its site and compared
by full structural conversion against its neighbours'. Binding
each composite once (level 0: `ℓt`/`ℓc`/`rt₃`/`rt₂`/`rt₁`/`rc`/
`sl`/`sr` in `hexagon-r₀`/`-l₀`; level 1: private aliases onto
the `Q.`-names so cross-level boundaries align by name) lets
every family comparison short-circuit on the name. Applied in
three steps, each confirmed by cold totals:

- the `step-r₂` base subtrees (`uρ`, `vα` per mirror):
  12,586 ms, **−660**;
- the traversal chains at level 1: 9,652 ms, **−2,934**;
- the chains at level 0 plus the cross-level aliases:
  8,628 ms, **−1,024**.

The same move collected in the pentagon (`ℓt`/`ℓc`/`rc` in
`pentagon●₀`, propagated through `pentagon₀`'s public re-export;
`top̂`/`bot̂`/`E₂`–`E₄`/`step̂₂` restated on the names):
`Coherence` 6,516 → **6,060 ms**.

Two smaller wins of the same ascription-respelling class:

- **The μ̂ Θ-chain mids.** `Θ-field`'s RHS, `Θ-assoc`'s LHS/RHS,
  and `Θ-merge`'s LHS re-spelled the two mid `comp-pathp₂`
  composites; naming them (`mid₁`/`mid₂` per mirror) measured
  13,246 against 13,559, **−313**.
- **The η-wrapped reversed side.** Both canonical trees consumed
  `(λ m → left̂ (~ m))` inline; naming it (`left̂⁻`) measured
  −165 — marginal here, kept as the styleguide's existing
  named-side norm.

## Ruled null or worse — reverted, on the record

- **Sealing `fiber-hexagon₁` opaque** (level-0 precedent):
  no change. The displaced fiber square's billed cost is not
  interior unfolding — its only consumer projects `fst` at
  generic points and every boundary is type-directed — so the
  attribution on it is first-forcer conversion of its
  boundaries, which a seal cannot move.
- **Naming the recurring `fst`-shadow lambdas** (`(λ i →
  ℓ̂-assoc₁ i .fst)` and kin, 12 per mirror, type-ascribed):
  measured *worse* (~+250). Recurrence across definitions does
  not upgrade argument positions to the named-face disease when
  the terms are small projections: the expected types are
  elaborated per-site regardless, so the naming saves a
  five-token lambda and pays 24 signatures.
- **Naming the `comp-pathp₂-merge-map` cap faces** in
  `Core.Path.Base`: Path.Base +57 ms, Hexagon unmoved. The four
  links' cost is instance conversion at the use sites, not the
  cap's spelling.
- **The transport-free fiber square.** The square's stated type
  is a nested `PathP`, and each `j`-slice's `i1` fiber is
  `⊗₁-wit` at the stated stations by the boundary rule — so
  `is-prop→PathP` at `PathP-is-contr (⊗₁-wit-contr â₄)` closes
  it with *no transported contractibility at all*. Measured
  ~170 ms worse pooled: the `coe` of a whole `PathP`-space plus
  the `PathP-is-hlevel` subst tower costs more than the
  `∧`-subst `wit-prop` it replaces. The `is-prop→SquareP` idiom
  stands.

## Measured, final (median-of-3 cold)

`Cat.Monoidal.Hexagon` 13,723 → **8,743 ms** (−36%);
`Cat.Monoidal.Coherence` 6,516 → **6,060 ms** (−7%);
`Braid` 484, `Indiscrete` 428, `Iso` 301, `Twist` 466 — all
unchanged within noise; `Core.Path.Base` untouched. Net ≈
−5.4 s cold across the displaced layer. The remaining ≥150 ms
classes are the ones the plan fenced and the audit already ruled
structural one level down: the `⊗₁-wit-∙` glue chain
(`top̂`/`bot̂`/`ŵᵢ`, which must stay transparent for the
reindexed-glue conversions), the `θ̂`/`Θ` merge instances, the
`wit-prop`/`fiber-hexagon₁` interior, and the `Miscellaneous`
bucket (~4 s: signatures, occurs, `braided-coherent` positivity
under `--safe`, serialization, two level-0 section applications
per displaced module).

## Verification state

Full non-WIP library re-checks clean (`--safe
--erased-cubical`, Agda 2.9.0) via `All.lagda.md`; `just lint
changed` clean. `Data.Thin.Category` and the `All.lagda.md`
sync stay queued with the deferred chores. The styleguide gains
the chain-naming norm and the recurrence caveat to the
argument-position rule.

## Next steps

1. The module queue resumes: the `Properties` comparisons ruled
   waiting on this pass.
2. The chain-naming norm is standing discipline for every module
   above the displaced layer — chains named at level 0 from the
   start, displaced modules aliasing them, never re-spelling.
3. Deferred chores unchanged (fence tagging, lint sweep,
   `Data.Thin.Category`, `All.lagda.md` sync).
