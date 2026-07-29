# TODO

Repo-level maintenance tasks. Module-level items live in their
module's ledger, and the research program lives in
`docs/roadmap.md`.

- [ ] Prose-debt sweep. The `writing` skill outranks local
  pattern. Known debt: em-dash headings in the changelogs, the
  `docs/guidelines/` bodies, the module TODO ledgers. Sweep with
  the skill's `prose-lint.py`, largest scores first.
- [ ] Guideline `src/` citations. The guideline register
  (`docs/guidelines/CLAUDE.md`) bars live-tree locations, and
  `module-anatomy.md` cites a `src/Core` pragma site. Sweep the
  guidelines for `src/` references and restate each example in
  the abstract.
- [ ] `Data.Thin`: close the open interaction metas in
  `Category`, `Cover`, `Properties`, `Separated`. Pre-existing
  debt, visible since `just check-tree` swept the whole tree.
- [ ] `Core.Coherence.Paths`: close its open interaction metas.
  Pre-existing debt, same sweep.
- [ ] `Core.Path.Coherence`: a `ModuleDoesntExport` warning fails
  under `-Werror`. Pre-existing debt, same sweep.
- [ ] `justfile`: the `check-all` comment still calls the
  `Cat.Depreciated` relocation unresolved. It is resolved. Decide
  the aggregator's fate at the same time.
- [ ] `docs/gloss.md`: entries for the record-cut theorems
  (`axioms→stable`, the four unit laws, the cancellations) and
  for the (D′) profile verdict at the free balanced point.
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
- [ ] `docs/gloss.md` audit: T22 and T23 cite `Gloss.*` names.
  Verify those modules exist in the checked tree. The T21
  precedent says they may be phantoms of the retired promotion
  scheme.
