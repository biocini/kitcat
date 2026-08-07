# Changelog — Bb.UnitalMagmoids

Every alteration and addition to this tree after it entered the
archive. **Newest entry first.** The tree is frozen green, so an
entry names the checker run that says so.

---

## 2026-08-06 — README citation re-pointed after the plan set was cut

**Documentation only, no module changed.** The composite-rx refactor
narrowed to `Core.Kan`, `Core.Composite`, and `Core.Rx`, and its
per-stage documents merged into
`docs/composite-rx-refactor/stages.md`. `README.md`'s provenance
paragraph cited `stage-4-cat-rebuild.md`, which no longer exists. It
now names the plan directory instead. The claim is unchanged: that
plan named this material under the stale `CatData` label, and the
citation names this tree now.

No `.lagda.md` file changed, so the tree's green state is unaffected.

## 2026-07-28 — the suite extracted from Bb.CatsWithExplicitInterchange.Magmoid

**The extraction, `verified`.** Twelve modules moved from
`Bb.CatsWithExplicitInterchange.Magmoid` to `Bb.UnitalMagmoids`:
`Base`, `Coh`, `Eqv`, `Het`, `Iso`, `Magmoid`, `Map`, `Nat`,
`Neutral`, `Neutral.Eq`, `Prod`, and `Unit`. Module declarations and
internal imports were rewritten to the new prefix. `just check-tree
src/Bb`: 98 of 98 modules typecheck. `just check Bb.index` is
green.

**Why it moved.** The archive's own index was the only reference to
the suite from outside its own directory. The suite also carries a
distinct formulation, composition derived from a Yoneda embedding,
apart from the composite-witness category development the rest of
`Bb.CatsWithExplicitInterchange` holds.

**Citations re-pointed.**
`docs/composite-rx-refactor/stage-4-cat-rebuild.md` now names
`Bb.UnitalMagmoids.*` for the magmoid-era material. That citation
used to name `Bb.CatsWithExplicitInterchange.CatData.*`, a label
that never matched a real module path.

**The index.** `Bb.index` gained a new "Unital magmoids" section
holding the twelve imports. Those imports left the "Cats with
explicit interchange" section.

**CatsWithExplicitInterchange.** Its `README.md` and `CHANGELOG.md`
record the new count, forty-nine modules, and the extraction.

**Verification.** `just lint changed` is clean.

Next: nothing planned. The tree is a standalone archive.
