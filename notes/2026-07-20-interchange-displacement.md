# Session log — 2026-07-20 — the interchange displacement

Executing `notes/2026-07-20-interchange-plan.md`, steps 1–2. Both
landed; step 3 (the hexagon/braid ports) is scoped at the end.

## What was done

- **The field swap** (`Cat.Monoidal`). The witness indexing the
  plan asked to pin first: `⊗₁-wit`/`⊗₁-wit-nrm` hoist from
  `theory₁` into `tensor-representable₁` — the displaced witness
  space is exactly what the axioms record can quantify over
  (it needs only `⊗₀-emb`/`⊗₁-emb`), and it is
  `is-representable[_]` at the squared base, so the field is
  `interchange♭ᴰ` token-for-token: `⊗₁-interchange♭` takes
  `⊗₁-wit U U' η → ⊗₁-wit V V' ζ` to a `PathP` over the
  `⊗₀-interchange♭ U V` / `⊗₀-interchange♭ U' V'` lines relating
  `η ▿₁ ζ` and `η ▵₁ ζ`. Pointwise `⊗₁-interchange` keeps its
  name and type as the `⊗₁-wit-nrm` shadow; the agreement is
  definitional (`▿₁`/`▵₁` collapse to `▾₁`/`▴₁` against embedded
  factors, the base line by `⊗₀-nrm`), so `⊗₁-spine` and all
  downstream consumers re-checked untouched — first-attempt
  typecheck, no coercion anywhere.
- **The closures move off the spine** (ruling, Lane, in review):
  no pointwise→field adapters in the record modules — an instance
  proves a ♭ field in the field's own shape ("we have the
  opportunity to privilege the one we shoot to build now, and it
  should be the one that's in the record"), and the spine stays
  J-free per the J-retirement arc. The pointwise-to-♭ closures
  are presentation-comparison material — the nontrivial direction
  of a pointwise-field ≃ ♭-field presentation equivalence, their
  only conceivable consumer — and live in new `Cat.Type.Properties`
  and `Cat.Monoidal.Properties` modules: `interchange♭-from`
  (moved out of `Cat.Type.representable`), `⊗₀-interchange♭-from`,
  and `⊗₁-interchange♭-from` (the double dependent J over the
  total fibers — each witness's base lines and characterization
  re-bent as one path in the graph Σ of `⊗₁-composite`, ambient Σ
  pinned via `J {A = …}`; a pair literal never determines its Σ
  family). Zero consumers, by design.
- **`Cat.Groupoid` re-founded.** `ι♭` was `interchange♭-from ι` —
  the one live instance routed through the closure, so its
  derived interchange shadowed its own March equation only up to
  J. The field is now proven in its own shape:
  `sym (λ i → p i ▿ q i) ∙ ι m n ∙ (λ i → p i ▵ q i)` — the March
  equation at the representing paths, conjugated by the `▿`/`▵`
  lines of the witness identifications, the one-sided composites
  in `ι`'s type collapsing to the ternary orders against the
  embedded factors. J-free; the `Core.Transport.J` import retires
  from both `Cat.Type` and `Cat.Groupoid`.
- **`_○₁_`** (`theory₁`): token mirror of `_●₁_` on the
  comp-op/`▵` side, `comp-pathp₂` in the role of `∙`.
- **The displaced interchange-coh** (`Cat.Monoidal.Coherence`):
  `ι-mult-r₀`/`ι-mult-l₀` complete the level-0 transcription of
  `Cat.Coherence.interchange-coh` (statements only — 3-coherence
  hypotheses, well-typed by strict mixed associativity of the
  ternary orders, `(F ▵₀ G) ▿₀ H ≐ F ▵₀ (G ▿₀ H)` and both
  grades' mirrors). One grade up, `ι-mult-r₁`/`ι-mult-l₁` are
  squares of hom-composite lines over the level-0 statements;
  `●₁-coh` is the `is-prop→PathP` at the displaced witness family
  over the flat line (`subst is-contr` along the connection — the
  `⊗₁-wit-σ[_,_]` shape with the composite moving too); and
  `⊗₁-interchange-natural` is `comp-pathp₂-commutes` on the cube
  `λ j i → ⊗₁-interchange♭ (●₁-coh Û V̂ i) Ŵ j` — the plan's
  "Path.commutes on the interchange cube", one grade up.
- **`Core.Kan` gains the displaced commutes**:
  `comp-pathp₂-rfill` (displaced `cat.rfill`) and
  `comp-pathp₂-commutes` (displaced `Path.commutes`) for a binary
  family — the `comp-pathp₂-over` precedent again: mint the
  displaced Kan cell so the consumer stays a two-liner.

## Cubical engineering facts (hard-won, reusable)

- **The displaced `Path.commutes` lands on `comp-pathp₂`
  endpoints definitionally because the `∙`-tower IS an
  hcom-tower.** `pcom` is hcom-based, `cat.fill` is `hfil` of
  `pcom`'s system, and `cat.rfill`'s composite side restricts to
  exactly `pcom refl p q`'s system (`p (~ j)` at `j = i1` is the
  `refl` face by boundary reduction). So a displaced Kan cell is
  built by riding `hfil` of the base cell's restated system,
  wall-for-wall, with each displaced wall a previously-minted
  displaced cell (`comp-pathp₂-commutes`' i0 wall is
  `comp-pathp₂-rfill`, whose composite side is `comp-pathp₂` on
  the nose by its own type-directed boundary). Every lid
  conversion is hcom-vs-hcom at pointwise-equal systems. No
  bridge, no parallel statement shape.
- **Restating a where-local system is free.** The base cell's
  partial element is not exported, but partial elements compare
  pointwise on faces, so an identical restatement in the
  displaced cell converts syntactically.
- **Seal the `●-coh` lines from birth.** The naturality cube's
  type family projects `●₀-coh`/`●₁-coh` at generic interval
  points on both sides, at fourfold-witness arguments — the
  `assoc-σ⋉₀` leak one module over. Unsealed,
  `⊗₁-interchange-natural` billed 4,882 ms; `opaque` on both coh
  lines dropped it to 145 ms (module 10.9 s → 6.2 s, back at
  baseline). Endpoints still reduce by the type-directed rule, so
  the cube and both instances need no unfolding.

## Verification state

Full sweep of every live module passes (`--safe
--erased-cubical`, Agda 2.9.0), excluding only the All.lagda.md
WIP set (open holes, pre-existing), re-run after the Properties
restructure (which rebuilds the whole cone — `Cat.Type` changed).
Cold totals over three runs: `Core.Kan` 0.98 s, `Cat.Type`
0.24 s, `Cat.Groupoid` 0.61 s, `Cat.Monoidal` 1.18 s, `Bifunctor`
1.7 s, `Cat.Monoidal.Coherence` 6.6 s — all at or under their
pre-session baselines (a late uniform ~8% drift across touched
and untouched modules alike reads as ambient machine state; the
per-definition profile is stable). The coherence module's new
definitions bill 145 ms (`⊗₁-interchange-natural`) + 41 ms
(`●₁-coh`), the pentagon/triangle entries unmoved. The field
swap and displacement are committed (`c6a2405`); the Properties
restructure and Groupoid re-founding are not yet.

## Next steps (step 3 of the plan — the ports)

The hexagon/braid ports consume the resulting shape, but they
sit on unported dependencies and open record-shape rulings:

1. `Cat.Monoidal.Indiscrete` port first — the instance that
   builds a `monoidal` from contractible homs; it proves the ♭
   fields directly, in the field's shape — the Groupoid
   re-founding (conjugation by the witness lines) is the model,
   not the Properties closures.
2. The braided record on the new spine: the old `braided` has a
   single field (the braid at the curried tensor); under the
   wit-calculus the braid should enter as a witness-line datum —
   the field-shape question is the same genus as the
   `⊗₁-interchange♭` ruling and wants an explicit ruling.
3. `Hexagon` (416 lines old-form): the braided-coherent record —
   first consumer of `ι-mult-r₁`/`ι-mult-l₁` and
   `⊗₁-interchange-natural`; the old `absorb-coh` irreducibility
   gets re-examined against the naturality recipe.
4. `Twist` last — it needs `Indiscrete` and consumes the
   absorb-coh sides; the reduction theorem is `ap`-algebra and
   should transcribe mechanically.

Audit disciplines from the start, per the plan: sealed σ-heads
for any new canonical identification a family will ride,
displacement as `σ[_]`-instances, named faces (bottoms and
sides), fills whiskered on the argument side wherever the tree
allows.
