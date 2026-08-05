# TODO — Bb

Open work spanning more than one tree in this namespace, or not
yet assigned to any tree's own ledger. Per-tree open items belong
in that tree's own `TODO.md` where one is permitted
(`src/Bb/CLAUDE.md`'s one exception is `Bb.VirtualGraphs`); this
file is for work above the single-tree level.

- [ ] Write `src/Bb/VirtualGraphs/HISTORY.md`: a chronological
  digest of the whole virtual-graph/deductive-system development
  arc, spliced from every historical source across the codebase,
  as the tree's sole historic artifact — its `README.md` and
  `CHANGELOG.md` stay matter-of-fact per the archive contract, all
  narrative belongs in `HISTORY.md` alone. Every beat of the
  narrative must be cross-referenced to where its content now
  lives in the settled tree (name the current module, not just
  describe the history). Sources: `notes/*.md` touching virtual
  graphs or deductive systems, 2026-07-20 through 2026-08-05;
  `src/Cat/Logic/TODO.md`, `.../gloss.md`, `.../lemmata.md`;
  `docs/deductive-systems/`; `docs/composite-rx-refactor/`; and
  the `README.md`/`CHANGELOG.md` of `Bb.WeakDeductiveSystem`,
  `Bb.OneTwist`, `Bb.VgCategoryShape`, `Bb.NaiveVirtualGraph`, and
  `Bb.VirtualGraphs` itself (`Bb/VirtualGraphs/CHANGELOG.md` is
  the fullest single provenance record and the anchor for cross-
  referencing). Large reading budget needed — best run as a
  dedicated agent (process/documentation design, `CLAUDE.md`'s
  Delegation table puts this at the Opus tier).

- [ ] Retire `Bb.OneTwist` and `Bb.VgCategoryShape`'s proved
  content, now that it is fully vendored into `Bb.VirtualGraphs`.
  Both confirmed fully vendored with zero live dependents
  (`outputs/virtual-graphs-surface-onetwist.md`,
  `outputs/virtual-graphs-surface-vgcategoryshape.md`). `Cat.Logic`
  and `Bb.WeakDeductiveSystem` are explicitly NOT candidates — both
  have live `src/Test/Spike*.lagda.md` dependents and must not be
  touched. Execution, once approved:
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
  - Verification ladder: `gtimeout 300 just check-tree src/Bb`;
    `just check Bb.index`; an `rg` sweep confirming no other live
    reference to the deleted paths remains (dated `notes/` entries
    and CHANGELOG history excepted, per the standing convention of
    banner-noting a dated record rather than rewriting it).
