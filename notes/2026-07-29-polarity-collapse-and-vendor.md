# 2026-07-29: the polarity collapse, three reviews, and the vendor pass

Objective: measure whether `positive`/`negative` objects can be a
non-degenerate, distinguishing notion in `Cat.Logic`'s deductive-system
framework. Act on what the measurement found, and promote the result.

## What was done

1. **`Cat.Logic.Gist.PolarityHLevel`.** Transcribed `positive`/
   `negative` over `tower`, no truncation. Measured their h-level at
   two existing models. Circle model: structure. Inhabited, not a
   proposition, not contractible. Two witnesses, one winding apart.
   Word model: property, and empty. Both refuted, via
   `linear-refuted`/`thunkable-refuted`.
2. **`Cat.Logic.Gist.PolarityTwist`.** Reduced polarity to a two-edge
   check on the two twists. `thunkable`/`linear` close under both
   cuts, unconditionally, over the bare tower. Two of the four
   closures are one-sided. At full deductive-system strength, one
   linear or thunkable twist decides the whole object's polarity, with
   no generation hypothesis needed (`full.positive-of-twist⁺`,
   `full.negative-of-twist⁻`). Open: a stable, composable carrier that
   is neither invertible nor generated.
3. **`Cat.Logic.Gist.PolarityCollapse`.** The headline result. Proved
   `linear (twist⁺ x) ⟺ thunkable (twist⁻ x)` at every object of every
   full deductive system, hence `positive x ⟺ negative x` always. No
   deductive system has an object that is positive and not negative,
   or the reverse. A distinguishing model is impossible at balanced
   strength. This explains items 1 and 2 retroactively: the circle
   (both hold) and the word model (neither holds) are the only two
   ways the iff can be satisfied.
4. **Three adversarial reviews**, one per spike, Opus, dispatched
   strictly one at a time. Found the mathematics sound throughout. No
   gaming, no undisclosed vacuousness, every central proof
   independently re-derived and confirmed. Found one wrong citation
   (Critical) and several overclaiming or underclaiming prose defects
   (Major). Catalogued in `outputs/polarity-collapse-chain-review.md`.
5. **`Cat.Logic.Gist.OperatorCarrier`.** Reformulated a full deductive
   system as a wild category plus one endo-operator (`presentation`).
   Proved the forward direction, deductive system to presentation, by
   assembly. The backward direction reconstructs `reflect` and all
   four tier fibers with no hypothesis, forcing every fiber's edge. One
   obligation stayed open: `readback-square`, the record-level identity
   of the two graphs.
6. **`Cat.Logic.Gist.ReadbackShift`.** Settled `readback-square` at the
   circle model, for both of `ReadbackTorsor`'s candidate readbacks.
   Proved, not refuted. `is-deductive-system` never mentions readback,
   so it is free structure. The presentation's fields mostly return on
   the nose under a readback shift; two shift by one winding, and the
   shift carries through to the square itself. At this model the
   square reduces to the mixed associator's triviality at the axiom.
   The argument is model-specific: it spends the circle's commutative
   loop space and the degeneracy of `mult-assoc` at `base`. The general
   case stays open.
7. **Promotion.** All five modules moved from `Test.SpikeXxx` to
   `Cat.Logic.Gist.Xxx` via `just mv`, in dependency order, each rename
   checked before the next. The review's fix list landed during the
   move: the citation corrected, two disclosed-but-unchecked gaps made
   machine-checked, the duplicate `split-refuted`/`split-refuted-dual`
   pair replaced by two sharper lemmas, a bundled
   `is-deductive-system`-level corollary added, naming and overclaiming
   prose fixed. Two findings were deliberately deferred, not dropped:
   deduplicating `positive`/`negative` across
   `PolarityHLevel`/`PolarityTwist`, and simplifying
   `PolarityCollapse`'s proof scaffolding. Both are recorded as open
   debt in the ledger.
8. **Staleness diagnosis.** Read the "Lines of investigation" list
   against the collapse result. Lines 6 (shifts as representability)
   and 7 (the reflection theorem, the capstone target: a deductive
   system's polarized, balanced core is a duploid) are blocked by a
   proved theorem, not merely undone. Balance is exactly the strength
   at which polarized collapses, so no polarized-and-balanced core
   exists to build a duploid from. Item 4's "subcategories" plan closes
   the same way. Items 1, 2, 3, 5, 8, and 9 stand unaffected in their
   own content. Item 5's own text already named "a depolarization
   theorem" as the expected shape of this outcome. Recorded, not
   decided: item 4's earlier RULED note rejected primitive polarity on
   a clause now known false. Reopening that ruling is Lane's call.

## Findings and decisions

- verified: h-level of `positive`/`negative` at the circle (structure)
  and word (empty property) models, `Cat.Logic.Gist.PolarityHLevel`.
- verified: closure of `thunkable`/`linear` under both cuts, and the
  one-edge theorem at full strength, `Cat.Logic.Gist.PolarityTwist`.
  An independent reviewer hand-re-derived the argument and confirmed
  the two one-sided closures are genuinely one-sided: the discarded
  hypothesis's negation is separately provable by an adversarial
  probe.
- verified: `positive x ⟺ negative x` at every object of every full
  deductive system, `Cat.Logic.Gist.PolarityCollapse`. An independent
  reviewer hand-traced the argument in full against the exact library
  lemma types (`assoc⁺`, `assoc⁻`, `mixed-assoc`, `unitr⁺`, `unitl⁻`,
  `pair⁻`, `pair⁺`, `unitl⁺`, `unitr⁻`) and found no gap.
- verified: `readback-square` holds at the circle model, at both
  candidate readbacks, `Cat.Logic.Gist.ReadbackShift`. The two most
  central lemmas (`retune-axioms`'s soundness, and `mixed-base`'s
  reduction to `refl`) were independently hand-checked outside the
  review batch.
- blocked: `readback-square` in general, and `round-system` for a
  presentation without hom sets. It needs the same cancellation
  without a commutative loop space and without a cut witness that
  degenerates at the axiom. No instrument in the library currently
  supplies either.
- open: a stable, composable, non-invertible, non-generated carrier.
  The one place a polarity-distinguishing model could still exist.
  Untouched by any result this session.
- Citation defect, found and fixed. `positive`/`negative`'s source is
  Clairambault and Munch-Maccagnoni, *Duploid situations in concurrent
  games* (GaLoP XII, 2017), `resources/mmmm-classical-notions/article.tex:1694-1700`.
  Not Definition 1 of `resources/munch-maccagnoni-duploids`, which
  states polarity as *primitive* data, a partition map, never derived
  from `linear`/`thunkable`. The wrong citation had already spread
  into `TODO.md`, `CHANGELOG.md`, and a planning artifact before the
  review caught it. All three are fixed.
- Failed strategy, with reason. The fourth spike (a
  polarity-distinguishing model, before the collapse proved none
  exists) was first dispatched to Fable. It ran 54 minutes with zero
  tool calls, then failed on hitting its weekly usage limit: about 4%
  of budget spent, no artifact produced. Retried with the identical
  brief on Opus, with the dispatch instruction rewritten to demand a
  concrete file artifact and a checker run within the first few tool
  calls. Opus completed in about 48 minutes with steady tool use.
  Later that session (once the target turned out to be unsatisfiable),
  every remaining open-ended construction spike went to Opus, not
  Fable. Recorded as a standing memory,
  `fable-open-ended-construction-risk`, kept in the assistant's memory
  store rather than this repository.

## Verification state

- Checker runs, all recorded by direct `just check`, not relayed from
  a subagent without independent confirmation. All five promoted
  modules check individually. `just check-tree src/Cat/Logic/Gist`
  checks, 14 modules. The whole-library `just check-tree` is clean
  except six pre-existing failures unrelated to this work
  (`Core.Coherence.Paths`, `Core.Path.Coherence`, `Data.Thin.Category`,
  `Data.Thin.Cover`, `Data.Thin.Properties`, `Data.Thin.Separated`). A
  stale `Cat.Type` import and unrelated unsolved metas cause them.
  None of the affected files were touched this session.
- `just lint changed`: clean.
- Obligation inventory: zero holes, zero postulates, zero unsafe
  markers across all five modules, confirmed by direct grep rather
  than by trusting each module's own closing prose.
- Prose: the `writing` skill's linter scored all five modules and both
  new ledger blocks under the 2.0-violations-per-100-words gate.
- No stale `Test.SpikeXxx` reference remains anywhere in `src/`,
  confirmed by `rg` after the vendor pass.

## Artifacts

- Library: `src/Cat/Logic/Gist/{PolarityHLevel,PolarityTwist,
  PolarityCollapse,OperatorCarrier,ReadbackShift}.lagda.md`.
- Review: `outputs/polarity-collapse-chain-review.md`, plan
  `outputs/.plans/polarity-collapse-chain-review.md`, evidence
  `outputs/.drafts/polarity-collapse-chain-review-evidence.md`.
- Plans: `outputs/.plans/{polarity-hlevel,polarity-twist-condition,
  polarity-distinguishing-model,category-operator-presentation,
  readback-square,vendor-polarity-gists}.md`.
- Ledger: `src/Cat/Logic/TODO.md`. Five `## Settled: ...` blocks, one
  per gist, and one `## Stale in light of the polarity collapse`
  diagnosis block, with pointers added to investigation items 4
  through 7.
- Changelog: six dated entries in `CHANGELOG.md`, one per gist plus
  the vendor pass. This session's log is the seventh, and closes the
  set.
- Memory (assistant-side, not tracked in this repository):
  `fable-open-ended-construction-risk.md`.
- This log: `notes/2026-07-29-polarity-collapse-and-vendor.md`.

## Open questions and next steps

1. The below-invertibility case: stable, composable, neither
   invertible nor generated. The only carrier shape left where a
   polarity-distinguishing model could still exist. Untouched. If a
   reformulation works at a weaker stratum than full balance, test
   this case there first.
2. `readback-square` in general is open, and now has a named
   obstruction rather than an unattempted status: a cancellation
   argument that leans on neither a commutative loop space nor an
   axiom-degenerate cut witness. No such instrument exists yet.
3. Two deferred fixes from the review sit as recorded debt, not
   forgotten: `positive`/`negative`'s duplication across
   `PolarityHLevel`/`PolarityTwist` (the natural future home is beside
   `thunkable`/`linear` in `Cat.Logic.Base`), and
   `PolarityCollapse`'s provably unnecessary `centre` scaffolding.
4. Lane's framing at session close: `Cat.Logic` is headed for a freeze
   into `Bb` and a fresh reformulation, on the strength of the
   polarity-collapse finding. This session did the diagnostic
   groundwork, which investigation lines survive, which don't, and
   why, and made no move toward the freeze itself. The next session's
   first decision: reopen the RULED note on primitive polarity
   (Munch-Maccagnoni's own Definition 1 states it primitively) now
   that the derived route through lines 6 and 7 is closed, or look for
   room below invertibility first, per item 1 above.
5. The six pre-existing whole-library check-tree failures are
   unexamined beyond confirming they predate and are untouched by this
   session. A future session should look at them before they
   accumulate further.
