# Checkpoint — 2026-07-21 — promotions, the double-loop instance, the flank boundary

Second session of the refoundation mini-programme. Everything below
is machine-checked; the new Core and Cat modules under
`--safe --erased-cubical`, the instance under full `--cubical` per
the Phase 0 ruling.

## Rulings landed (Lane, 2026-07-21)

1. **Melliès is the semantic guide; the kernel is certified against
   it, never an authority.** The chirality convention is pinned from
   `resources/mellies-braided-dialogue`: positive twist =
   trigonometric +2π, θ_I = id. Ruled: **ω = ι⁺ ∙ sym ι⁻ realizes
   the positive twist — it winds +1 at the detection point.**
   CircleTensor conforms (the deformation moved to `ι⁺`; the
   `routes-differ` cancellation retargeted; re-checked). Checkpoint
   item 6's sign chore is closed.
2. **Pull-contr is not generic in a pointed Y.** After currying,
   pointwise cancellation is free for path composition, but the
   quantified collapse needs every `(Ω² Y × Ω² Y)`-family of
   carrier paths coherently constant — connectedness + 1-truncation
   of `Ω² Y`, refutable at `Y = S²` (π₀ = π₃S² = ℤ). Ruled: the
   instance is parametrized by the two circle-shaped collapse
   hypotheses (`flank-collapse`, `slot-faithful`); the sufficient
   condition is documented, and the sole contractibility axiom is
   exactly the part instances find expensive — record-freeze
   evidence.
3. **Naming**: compound PascalCase only in top-level module titles;
   kebab-case inside modules. The exchange machinery landed as
   `Core.Path.Exchange` (single content-named segment), the
   instance as the `Test/DoubleLoopTensor` spike.

## The twist-classification finding

The ruled ideal — both fields carried by the two scheduling
protocols symmetrically — met a geometric fact during
implementation: the record's interchange endpoints preserve factor
order, so every route between them decomposes as the planar
reassociation composed with an integer number of full twists, and
the two-sided crossing protocols (in by one chirality, back by the
other's reverse) land in the even classes: over-and-back-over is
+1 full twist but the over/under *pair* differs by two. With the
orientation ruling demanding ω = the positive generator, the
assignment is forced to `{ι⁺ = the positive full-twist resolution,
ι⁻ = the planar resolution}`. The chirality symmetry survives
inside the junction loop — the full twist is the composite of the
two exchange chiralities, neither privileged — rather than across
the two fields. Consistent with the circle instance
post-conformance.

## What landed

- **Promotions** (checkpoint item 5, executed first): `subst-∙` →
  `Core.Transport.Properties`, proof verbatim — the module imports
  `Core.HCompU` for its `TRANSPPROOF` binding, since the `ap-comp`
  leg transports along a universe hcom; `transport-inv` retired at
  its call site in favor of the existing `transport⁻-transport`
  (`transport⁻ p` is `transport (sym p)` on the nose); `ap-retr` →
  `Core.Path.Base` Cancellation section, generalized from `Circle`;
  `ua-unglue` → `Core.Univalence` beside `ua-β` (it had been
  leaking through the `Circle` namespace); Int discreteness → new
  `Core.Data.Int.Properties` (`DecEq-Int`, `set` by `hedberg`) and
  `Core.Data.Int.Impl.Discrete` (the instance), aggregator
  rewritten to Nat's shape, pragma bumped to `--erased-cubical`;
  the Circle-local `dec-map` deleted in favor of
  `Core.Trait.Decidable.dec-map`. `HData.Circle.Properties` slimmed
  accordingly; full ladder re-checked through `Test.CircleTensor`.
- **`Core.Path.Exchange`**: `Ω²`; the two exchange cells as pure
  interval terms (every stage of the slide is composable on the
  nose — no Kan filling); the conjugation welds by `pcom.unique`
  against fillers given pointwise by the unit laws, the paired
  welds seaming through the shared unit cell — `Path.unitl refl`
  and `Path.unitr refl` agree **definitionally** in this hcom
  calculus, which is what lets Eckmann–Hilton assemble with no new
  cube; `eckmann-hilton⁺`/`eckmann-hilton⁻` (the two crossings),
  `full-twist` (their discrepancy), `full-twist-unit-l/r` by
  inverse cancellation alone (on a unit flank the two exchange
  lines are the same term); `∙-pre-equiv`/`∙-post-equiv`.
- **`Test/DoubleLoopTensor`**: `Emb x (l , r) = l ∙ (x ∙ r)` on
  `∞-groupoid (Ω² Y)`, unit `refl`, under the two collapse
  hypotheses; pull fiber by the CircleTensor chain with
  `Path.assoc` in `mult-assoc`'s slot and the hypotheses in the
  collapse slots; both routes through the junction
  `l ∙ ((m ∙ n) ∙ r)` sharing every leg; **`ω-junction`**: the
  record's ω is the junction-whiskered full twist conjugated into
  position — the derived-framing claim machine-checked;
  **`ω-vanish-l/r`**: ω vanishes on the unit flanks;
  **`routes-differ-from`**: a π₃-nontriviality certificate for the
  full twist forces the fields apart (junction whisker inverted
  through `is-embedding→ap-equiv`); both **unitor agreement types
  inhabited** by composition with the generic flank theorem.
- **`Cat.Monoidal.Properties`, the flank boundary**:
  `ω-vanish-l/r` (per-record types), `flank-vanish→unitr-agreement`
  and `flank-vanish→unitl-agreement` — the unitor chain consumes ι
  only through `⊗₀-emb-comp-op` at unit flanks, so the absorption
  cells rebuild across the field choice by congruence and the two
  σ-lines compare inside the propositional representability fiber
  (prop → set; the comparison line's `fst` is constant); no opaque
  unfolding was needed. **`ω-trace`**: the self-discrepancy slid
  along the pairing and read back through the fiber —
  `x ⊗₀ x ≡ x ⊗₀ x` extracted with no new axioms.

## The two decision questions

(a) **Unitor agreement vs ω-vanishing**: the forward direction is
now a generic theorem, and the double-loop instance inhabits both
agreement types through it — the θ_I ≡ refl normalization (which
Melliès Def. 12 posits as the balanced axiom's unit clause) arrives
in derived form, as conjectured. The record derives, one
interchange at a time, what balanced dialogue categories posit. The
converse (agreement forces vanishing) stays open; its decider is
the circle contrapositive — compute the winding of the derived
unitor discrepancy `θ base` in CircleTensor — queued.

(b) **Balancing**: theorem by fiber projection, not a field, and
not the unitor discrepancy — that candidate is `refl` in this
instance by (a), so it over-normalizes. The surviving canonical
candidate is `ω-trace` — in the instance, the fiber projection of
the whiskered `full-twist x x`, the self-braiding trace.
Nontriviality of `ω-trace` needs the π₃ evidence tier (S²/Hopf,
deliberately off the critical path); the balancing interaction law
waits on the braid-layer redevelopment, pulled by need.

## Deferred and queued

- Grade 1 for the instance: `ι±₁`/`⊗₁-pull-contr` would re-run the
  collapse chain in PathP form for no grade-0 payoff; the right
  future shape is a generic path-groupoid `axioms₁` builder seeded
  by the pointwise `ap₂` observation.
- The weak (Hω-shadow) forms of the vanishing statements and their
  connection to `twist-reduces-to-omega`.
- The circle contrapositive (`Test/CircleUnitorTwist` or a
  CircleTensor addendum).
- The S²/Hopf nontriviality tier; no in-tree Y yet discharges
  `routes-differ-from`'s hypothesis.
- `All.lagda.md` untouched (deferred-chores batch; `check-all`
  still fails on the pre-existing `Cat.Covariant` staleness).
- Names minted this session, for sign-off: `Core.Path.Exchange`'s
  `whisker-r/l`, `exchange`/`exchange-op`, `whisker-*-conj`,
  `eckmann-hilton⁺/⁻`, `full-twist`; the Properties `ω-vanish-l/r`,
  `flank-vanish→unit*-agreement`, `ω-trace`.

## The rack design session

Delivered as `notes/2026-07-21-rack-design.md`, around the pinned
intention (Lane): `Rack A` is a **free HIT indexed on a carrier** —
`List A`'s framed sibling, the eventual type of contexts and
cocontexts — with crossing history as path data, the classical
free rack derived at the components by encode–decode, and the
operation extracted from contractible fibers proven over the HIT.
The note carries the classical target with hand-verified
conventions, the stub's mixed-convention finding (supersession,
not repair — being a HIT was never the fault), the constructor
design space (the crossing cells re-run the two-chirality decision
one level down; the kink must be derived, never a constructor),
the Cat-side rack-theory record as a separate track with the
translation-embedding refutation, and eight open rulings. No rack
code lands until those are settled.
