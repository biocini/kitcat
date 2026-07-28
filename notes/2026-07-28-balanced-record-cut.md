# 2026-07-28: the balanced record cut

Objective: adopt position (D′) in `Cat.Logic`, archive the weak
stratum, and settle the fate of the spikes the cut breaks.

## What was done

1. Three balance spikes ran earlier this day and committed as
   `0065395`: the readback torsor, the (D) base rehearsal, and the
   (D′) profile gate. All three were then promoted from `Test` to
   `Cat.Logic.Gist` as `ReadbackTorsor`, `BalancedBase`, and
   `BalancedProfile`.
2. The weak stratum moved into an archive: `src/Bb/WeakDeductiveSystem` is a
   frozen copy of `Cat.Logic` as it stood before the cut, 16
   modules, fully green, with an archive banner on its `TODO.md`.
   The `Bb.*` namespace row is in the root `CLAUDE.md`.
3. The record cut. `virtual-graph` carries a `readback` field,
   stated through `reflect` at `var`/`covar`.
   `is-deductive-system` is contractible cuts plus invertibility,
   propositional fieldwise. The `stable` field is gone.
4. Consumers adapted: `Display` (its `framed` module now takes the
   two cancellations), `Graph`, and the seven live `Gist` modules.
5. The carrier is explicit in `tower` and `coherence`, per the
   no-principal-argument clause of
   `docs/guidelines/elaboration.md`. The guideline gained a
   paragraph on eta recovery of record parameters.
6. The live tree drops five free-framing `Gist` spikes:
   `AssociatesCountermodel`, `FramedCut`, `FramedGroup`,
   `NeutralUnit`, `TwistFidelity`. Their green form is the
   archive's, and every `docs/` citation of the five now points
   there. Ruling (Lane, 2026-07-28): the live tree carries no red
   modules.

## Findings and decisions

- verified: At (D′) strength each tier centre reads back as the
  other twist, so both cancellations are theorems, and each hand
  is two-sided unital with its own twist as unit. The four unit
  laws are `tower` and `tower.balanced` in `Cat.Logic.Base`.
- verified: Stability is a theorem of the contractible negative
  cut: `axioms→stable`, through `composite⁻-twist` and
  `image-fibers-contr→is-embedding`.
- verified: The strict op-involution survives readback: the leg
  crosses `opⱽ` unchanged and `opⱽ-invol` stays `refl`.
- verified: The (D′) profile gate stays open on the countermodel
  side: two carrier attempts each die on a cut
  (`Gist.BalancedProfile`, `no-cut⁻` and `no-cut⁺`). Readback pins
  every constant reader to its own value, and the mixed composites
  manufacture readers constant at a projection.
- inferred: Interchange does not follow at (D′): the two units
  are offset by the double twist, and no derivation is known. This
  is an absence, not a refutation.
- Failed strategies, with reasons. A `where`-scoped `open` of a
  parameterized module left unsolved metas. The module-parameter
  form checks. An inline prop-combinator chain in a copattern
  clause left unsolved metas. A named lemma with a signature
  checks.
- The recurring inference failure has a root cause: the unifier
  recovers an implicit
  record parameter behind unfolding predicates by
  eta, and that recovery is complete only while every field occurs
  in the predicates' unfolded types. `readback` occurs in none, so
  the cut broke every such signature at once. The fix is the
  existing guideline rule, now applied: the carrier is explicit.

## Verification state

- Checker runs, all recorded by `just check` and `just
  check-tree`: `src/Cat` 69 of 69, `src/Test` 33 of 33, `src/Bb`
  16 of 16. `just lint changed` passes. The prose gate passes on
  all six touched `docs/` files at or under 2.0 per 100 words.
- The obligation inventory is zero: no holes, no postulates, no
  unsafe flags anywhere in the session's modules.
- The retired five are absent, not broken: their content is
  verified in `Bb.WeakDeductiveSystem.Gist`, which the checker
  covers.

## Artifacts

- Library: `src/Cat/Logic/Type.lagda.md`,
  `src/Cat/Logic/Base.lagda.md`, `src/Cat/Logic/Display.lagda.md`,
  `src/Cat/Logic/Gist/{ReadbackTorsor,BalancedBase,
  BalancedProfile,ThunkableSquare}.lagda.md`,
  `src/Bb/WeakDeductiveSystem/` (16 modules).
- Records: `src/Cat/Logic/TODO.md` (the record-cut and retirement
  blocks, the line 5 dossier, the line 9 transfer),
  `docs/guidelines/elaboration.md` (the eta paragraph),
  `docs/gloss.md` and `docs/deductive-systems/` (citations
  re-pointed).
- This log: `notes/2026-07-28-balanced-record-cut.md`.

## Open questions and next steps

1. The (D′) associates profile is open in both directions. The
   oracle is the free balanced word model, which now carries both
   line 9 and the profile. Next session starts there.
2. `docs/gloss.md` has no entries yet for the new theorems
   (`axioms→stable`, the four unit laws, the cancellations). Ledger
   chore.
3. The archive imports the live `Cat.Graph.Refl`. A future change
   there can break the frozen tree. Risk, accepted for now.
4. The handedness swap remains a separate pass, unstarted. The
   `Mag` rebuild remains pending.
