# TODO

Repo-level maintenance tasks. Module-level items live in their
module's ledger, and the research program lives in
`docs/roadmap.md`.

- [ ] Prose-debt sweep. The `writing` skill outranks local
  pattern. Known debt: em-dash headings in the changelogs, the
  `docs/guidelines/` bodies, the module TODO ledgers. Sweep with
  the skill's `prose-lint.py`, largest scores first.
- [ ] Move the remaining standing plans into `docs/plans/`, per its
  README. Three candidates, each cited from `docs/roadmap.md` and so
  each needing a citation sweep with the move:
  `notes/2026-07-20-lb-certification-program.md` (4 inbound),
  `notes/2026-07-20-ribbon-arc.md` (3 inbound), and
  `docs/composite-rx-refactor/` (8 inbound, four of them in frozen
  `Bb` trees, so each needs a `CHANGELOG.md` entry). After the move,
  `notes/` holds dated session records only.
- [ ] The documentation restructuring, a program in three steps:
  split the theorem ledger into per-namespace `lemmata.md` and
  `gloss.md`, triage `docs/deductive-systems/` into
  `src/Cat/Logic/gloss.md`, and sweep the `src/` citations out of
  seven `docs/guidelines/` files. The map is
  `docs/plans/documentation-restructuring.md`. It carries the
  standard, the verified inventory, and the gates. `just lint
  citations` is the gate that keeps the result from rotting. This
  item supersedes the guideline-citation sweep and both `gloss.md`
  items below.
- [ ] `Data.Thin`: close the open interaction metas in
  `Category`, `Cover`, `Properties`, `Separated`. Pre-existing
  debt, visible since `just check-tree` swept the whole tree.
- [ ] `Core.Coherence.Paths`: close its open interaction metas.
  Pre-existing debt, same sweep.
- [ ] `Core.Path.Coherence`: a `ModuleDoesntExport` warning fails
  under `-Werror`. Pre-existing debt, same sweep.
- [x] `docs/gloss.md`: entries for the record-cut theorems and the
  profile verdict. Landed as T32 to T35.
- [ ] `bin/lint` changed mode: per-file single-pathspec diffs
  lose rename pairing, so a renamed file scans as wholly added.
  Teach it one rename-aware whole-tree diff.
- [ ] `Bb.UnitalMagmoids.Prod` disables its embedding proof. A
  working proof exists at
  `reference/february26-ternary-cat/Data/Prod.lagda.md`. Ruling
  needed: does a frozen archive accept the upgrade?
- [ ] Rule on `reference/magmoid-formulation/Data`, the
  pre-Yoneda fork point: its own `Bb` tree, or it stays in
  `reference/`.
- [x] The two duploid source audits, statement-level. They gate
  every ledger citation that leans on those sources. Done
  2026-07-28: `outputs/duploids-statement-audit.md`, `Statements
  verified:` fields written to both `resources/mmmm-classical-notions/README.md`
  and `resources/munch-maccagnoni-duploids/README.md`.
- [ ] Correct the Rx promotion plan notes per the 2026-07-24
  audit (stage arithmetic, the cut-line reason, the Tier-1
  boundary). Gates the Core reformation (roadmap project 2).
- [ ] The frontmatter bulk sweep: convert the header-less Core
  files and the old-prose-header files to the YAML convention
  (docs/guidelines/module-anatomy.md), then flip the `bin/lint`
  canary to require presence.
- [ ] Remove globally-redundant per-module flags.
- [ ] The ternary-first conformance sweep over Core's legacy
  `∙`-chains.
- [ ] The WIP-module probe sections (`Core.Path.Composition` and
  siblings) move to `Test/`, then distribute per spike zero.
- [ ] The conservativity battery re-migration.
- [x] `docs/gloss.md` audit: the `Gloss.*` names are phantoms, as
  the T21 precedent suggested. All seven were deleted with the
  namespace in `cb96805` and are readable at `60410b7`. Thirteen of
  the ledger's 22 cited paths dangle; `just lint citations` reports
  them. Disposition is the restructuring item above.
