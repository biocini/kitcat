# Prose and comments

- **Prose documents the adjacent block** — what it states, the
  idea, the constraint the code can't show — with references made
  at the point of use ("following Rijke §13"; credit comments in
  the house forms per docs/provenance.md "Code citations"). Never
  process narration. (This is Public Module Style, as practiced.)
- **Comment register**: constraints and credit only; no
  `Note:/Key:/Important:/TODO` labels — Core has zero.
- **Probes and holes belong in `Test/`**, never in a public module;
  a WIP module's probe sections move out on promotion (the
  remaining `Core.Path.Composition` probes are scheduled cleanup,
  not precedent).
