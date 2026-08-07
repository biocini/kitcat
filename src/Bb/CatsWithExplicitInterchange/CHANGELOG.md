# Changelog — Bb.CatsWithExplicitInterchange

Every alteration and addition to this tree after it entered the
archive. **Newest entry first.** The tree is frozen green, so an
entry names the checker run that says so.

---

## 2026-08-06 — README citation re-pointed after the plan set was cut

**Documentation only, no module changed.** The composite-rx refactor
narrowed to `Core.Kan`, `Core.Composite`, and `Core.Rx`, and its
per-stage documents merged into
`docs/composite-rx-refactor/stages.md`. `README.md` cited
`stage-4-cat-rebuild.md`, which no longer exists. The sentence now
names the rebuild by its owner, `docs/roadmap.md` project 1, and
keeps the decision D8 reference and the
`docs/composite-rx-refactor/evidence.md` census pointer. The dropped
sentence about decision D5 went with the decision, which the cut
retired.

No `.lagda.md` file changed, so the tree's green state is unaffected.

## 2026-07-28 — the Magmoid suite extracted to Bb.UnitalMagmoids

**The extraction, `verified`.** The twelve `Magmoid` modules
(`Base`, `Coh`, `Eqv`, `Het`, `Iso`, `Magmoid`, `Map`, `Nat`,
`Neutral`, `Neutral.Eq`, `Prod`, `Unit`) moved to a new tree,
`Bb.UnitalMagmoids`, and the empty `Magmoid` directory was removed.
The suite carries a Yoneda-embedding formulation of magmoids,
distinct from the composite-witness category development this tree
keeps. Nothing outside the `Magmoid` directory imported it, apart
from `Bb.index`, so the move needed no consumer to update.
`just check-tree src/Bb`: 98 of 98 modules typecheck. `just check
Bb.index` is green.

Forty-nine modules remain in this tree. `README.md` drops its
`Magmoid` sentence and states the new count.
`docs/composite-rx-refactor/stage-4-cat-rebuild.md` now names
`Bb.UnitalMagmoids.*` for the magmoid-era material, in place of the
stale `CatData` label. `just lint changed` is clean.

Next: the tree still waits on Stage 4 of the composite-rx refactor.

## 2026-07-28 — twelve Test witnesses vendored into a new Gist subtree

**The vendoring, `verified`.** Twelve `Test` spikes and probes for
this stratum joined the tree as `Gist` modules:

- `AnchorPin`, `CircleTensor`, `CircleUnitorTwist`, `DoubleLoopTensor`,
  `OpTwist`, `ReadbackTwist`, `SliceAnchor`.
- `CodepExtractAgree` (from `CodepExtractAgree-20260713-171000`),
  `FaceProbe` (from `FaceProbe-20260720`), `MiscFloor` (from
  `MiscFloor-20260720`), `RhoProbe` (from `RhoProbe-20260720`): the
  date suffix dropped.
- `Product`, from `ProductSpike`.

Sixty-one modules in the tree now. `just check-tree
src/Bb/CatsWithExplicitInterchange`: 61 of 61 typecheck.

**Citations re-pointed.** `docs/gloss.md`'s T21 entry named
`Gloss.ExtractAgreeIndependence`. That citation now names
`Bb.CatsWithExplicitInterchange.Gist.CodepExtractAgree`, where the
result lives. `docs/composite-rx-refactor/evidence.md` and
`decisions.md` re-point their `DoubleLoopTensor` and `MiscFloor`
citations to the same tree.

**The index.** `Bb.index` gained the tree's twelve new imports,
alongside the pre-existing forty-nine. `just check Bb.index`
green.

**Verification.** `just check-tree src/Test`: 9 of 9 remaining
modules typecheck. `just lint changed` clean.

Next: nothing planned for this addition. The tree still waits on
Stage 4 of the composite-rx refactor, as before.

## 2026-07-28 — one over-width code line rewrapped

`Magmoid/Eqv.lagda.md:127` split at argument boundaries under the
100-column limit. Layout only. `verified`:
`just check Bb.CatsWithExplicitInterchange.Magmoid.Eqv` green,
`just lint changed` clean.

## 2026-07-28 — the tree moved from Cat.Depreciated, and the archive process started

**The move, `verified`.** All 49 modules moved from
`Cat.Depreciated` to `Bb.CatsWithExplicitInterchange`, module
declarations and internal imports rewritten to the new prefix.
`just check-tree src/Bb`: 86 of 86 modules typecheck, this tree
among them. The citations in `docs/composite-rx-refactor/`
(`README.md`, `decisions.md`, `evidence.md`,
`stage-2-discipline.md`, `stage-4-cat-rebuild.md`,
`stage-5-coherence.md`) were re-pointed at the move.

**The archive process, applied.** `README.md` written to the
common format of `src/Bb/CLAUDE.md`. This file opened. The tree
had no `TODO.md`, so nothing needed conversion. `Bb.index` gained
the tree's 49 imports and checks clean.

**Known and untouched:** 38 width residuals under `just lint
changed`, in 12 modules of this tree, carried in from the move.
Lane holds them.

Next: the tree waits on Stage 4 of the composite-rx refactor.
That stage ports it onto the deductive system and retires it.
