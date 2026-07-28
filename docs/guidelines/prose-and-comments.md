# Prose and comments

- **Prose documents the adjacent block**: what it states, the idea,
  the constraint the code cannot show. Make references at the point
  of use ("following Rijke §13", credit comments in the house forms
  per docs/provenance.md "Code citations"). Never process
  narration. (This is Public Module Style, as practiced.)
- **Comment register**: constraints and credit only. No
  `Note:/Key:/Important:/TODO` labels. Core has zero.
- **Probes and holes belong in `Test/`**, never in a public module.
  A WIP module's probe sections move out on promotion (the
  remaining `Core.Path.Composition` probes are scheduled cleanup,
  not precedent).

## Register

House prose follows ASD-STE100 Simplified Technical English. The
normative statement is the `writing` skill
(`.claude/skills/writing/SKILL.md`). Scope and mode:

- STE-flavored is the default for module prose, docs, notes,
  session logs, and reports.
- Strict mode applies to procedures, step lists, and error text.
- Mathematical terms and quoted formal statements are exempt from
  the dictionary rules. The sentence and punctuation rules still
  apply around them.
- The `writing` skill bundles its linter, which measures
  conformance in violations per 100 words. That linter is the only
  prose gate: run it on each changed `docs/` file, which must score
  at or under 2.0.
