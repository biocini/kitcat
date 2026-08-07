# TODO — Bb

Open work spanning more than one tree in this namespace, or not
yet assigned to any tree's own ledger. Per-tree open items belong
in that tree's own `TODO.md` where one is permitted
(`src/Bb/CLAUDE.md`'s one exception is `Bb.VirtualGraphs`); this
file is for work above the single-tree level.

- [ ] Retire `Bb.OneTwist`, `Bb.VgCategoryShape`, and
  `Bb.WeakDeductiveSystem`'s proved content, now that all three are
  fully vendored into `Bb.VirtualGraphs`. Confirmed fully vendored
  with zero live dependents outside `Test/` (now itself retired, see
  the root `CHANGELOG.md`'s 2026-08-06 spike-retirement entry) and
  the archive's own `Bb/index.lagda.md`
  (`outputs/virtual-graphs-surface-onetwist.md`,
  `outputs/virtual-graphs-surface-vgcategoryshape.md`,
  `outputs/virtual-graphs-surface-weakdeductivesystem.md`).
  `Cat.Logic` is explicitly NOT a candidate: it is the live carrier
  `docs/roadmap.md` cites for the deductive-system program, not
  archive scaffolding, and vendoring its content elsewhere does not
  change that. Execution, once approved:
  - `Bb.OneTwist`: delete `Base.lagda.md`, `Cancel.lagda.md`,
    `Models.lagda.md`. Update `README.md`/`CHANGELOG.md` to record
    the retirement and name the destination modules (`Extraction`,
    `Bool.Klein`, `Groupoid.Path`, `Group.Abelian`). Drop the three
    `Bb.OneTwist.*` imports from `src/Bb/index.lagda.md`.
  - `Bb.VgCategoryShape`: delete `Base.lagda.md`, `Type.lagda.md`,
    `Unit.lagda.md`, `Parity.lagda.md` (the one gap this tree held,
    `same-reflection`, is already ported —
    `src/Bb/VirtualGraphs/Bool/Heap.lagda.md`). **Keep
    `README.md`** — it is the live "Mag rebuild" program of record,
    cited from `docs/roadmap.md:38` and
    `src/Cat/Logic/TODO.md:10,139,901,935`; update its stale
    references to the deleted modules rather than deleting the
    file. Drop the four `Bb.VgCategoryShape.*` imports from
    `src/Bb/index.lagda.md`.
  - `Bb.WeakDeductiveSystem`: delete `Base.lagda.md`,
    `Display.lagda.md`, `Graph.lagda.md`, `Type.lagda.md`, and all
    twelve `Gist/*.lagda.md` modules (sixteen files total). Six are
    the surface audit's **FULLY VENDORED** files
    (`Base`→`Tower`/`Stability`/`Framing`/`Pentagon`,
    `Gist.NeutralUnit`→`Interchange`, `Gist.TwistFidelity`→
    `Interchange`, `Gist.AssociatesCountermodel`→`Bool.Readers`,
    `Gist.FramedCut`→`Groupoid.Path`, `Gist.FramedGroup`→
    `Group.Abelian`); the other ten are **COVERED BY OVERLAP** via
    the same-named live `Cat.Logic`/`Cat.Logic.Gist` module each is
    the pre-(D′)-cut ancestor of (`Type`, `Graph`, `Display`,
    `Gist.FramedInterchange`, `Gist.BalancedBase`,
    `Gist.BalancedProfile`, `Gist.ReflectFiber`, `Gist.RxDict`,
    `Gist.ThunkableSquare`, `Gist.ReadbackTorsor`) — see the surface
    audit for the destination of each. Update `README.md`/
    `CHANGELOG.md` to record the retirement rather than deleting
    them, per `src/Bb/CLAUDE.md`'s "a README/CHANGELOG in every
    tree." Drop the sixteen `Bb.WeakDeductiveSystem.*` imports from
    `src/Bb/index.lagda.md` (`src/Bb/index.lagda.md:168-183`).
  - Verification ladder: `gtimeout 300 just check-tree src/Bb`;
    `just check Bb.index`; an `rg` sweep confirming no other live
    reference to the deleted paths remains (dated `notes/` entries
    and CHANGELOG history excepted, per the standing convention of
    banner-noting a dated record rather than rewriting it).
