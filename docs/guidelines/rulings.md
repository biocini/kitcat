# Rulings

Ruled by Lane, 2026-07-14: the `.lagda.md` opener is a YAML
frontmatter block. Required core: `author`, `date` (`YYYY-MM`),
`contents`. Unknown keys pass, synopsis prose is optional, and the
block is uniform across tracked `src/` (timestamped `Test/` scratch
exempt). This supersedes the 2026-07-13 "author/date headers
standard" ruling (the two-plain-lines format). See the Opener norm
above. The canary is `just lint frontmatter`, and the tree-wide
conversion sweep is docs/roadmap.md target 6.

Ruled by Lane, 2026-07-13 (now stated as norms above, with
conformance sweeps scheduled in docs/roadmap.md Housekeeping):

- no globally-redundant per-module flags
- `u v w` for `Level`, with `ℓ` reserved for `I → Level`
- the ternary-first conformance sweep over Core's legacy `∙`-chains
  is GO
- the WIP-module probe sections migrate to `Test/` per Public
  Module Style
- implicit universe parameters are earned by inference (the
  category-structure correction)

Still open (Core splits, flagged rather than legislated):

1. Fixity before vs after the definition (or bless both).

Provenance: distilled from the 2026-07-13 `Core.*` norms survey.
The survey graded every convention NORM/TENDENCY/INCONSISTENCY at
file:line, with re-runnable sweep counts. The survey itself is not
in the tree. The conventions it produced are these documents.
