# Guidelines

Agda development knowledge and kitcat conventions, by topic. Root
`CLAUDE.md` carries the hard rules and wins on any conflict; these
documents say how the library practices them, with exemplar citations at
`file:line`.

Read what the task calls for, not the set. Most work needs one or two.

## Writing a module

| | |
| --- | --- |
| [module-anatomy.md](module-anatomy.md) | Opener and frontmatter, the pragma stratum, import order, aggregator shapes |
| [naming.md](naming.md) | Kebab-case and capitalization by role, `source→target` conversions, law vocabulary, namespace modules, variable letters |
| [prose-and-comments.md](prose-and-comments.md) | What prose documents, the comment register, where probes belong |
| [api-surface.md](api-surface.md) | What earns a public name, shared telescopes, instances, width, Unicode |

## Writing proofs

| | |
| --- | --- |
| [definitions-and-proofs.md](definitions-and-proofs.md) | Fixity, `INLINE`/`DISPLAY`, copatterns, `λ where`, cubical-native proofs, lemma extraction, signature layout |
| [records.md](records.md) | `no-eta-equality`, field order, the exit row, derived members |

## Designing signatures

| | |
| --- | --- |
| [elaboration.md](elaboration.md) | Implicit vs explicit: the three recovery tiers, levels, edge endpoints, and the probes that decide a case |

Read this before adding a parameterized module or an edge-indexed API.
The question it answers — can a use site recover this argument — is
cheap to test and expensive to get wrong, because a wrong answer
surfaces as a metavariable at someone else's call site rather than as an
error at the mistake.

## Making it fast

| | |
| --- | --- |
| [profiling.md](profiling.md) | How to measure: `just profile`, the cold-run discipline, how to read an attribution |
| [performance.md](performance.md) | What the measurements taught: sealing, naming ascribed faces and chains, Kan fillers in head position, what measured null |

Profiling comes first. Every norm in `performance.md` was derived from
measurement, several plausible optimizations measured null or worse, and
the norms are not to be applied on suspicion.

## Standing decisions

| | |
| --- | --- |
| [rulings.md](rulings.md) | Dated rulings and the splits deliberately left open |

Where Core itself splits, the split is flagged there — do not invent a
rule from a split.

## Evidence

The style documents record a norms survey of the `Core.*` tree
(2026-07-13; 31 of 134 files read in full, tree-wide sweeps for every
count) that graded each convention NORM/TENDENCY/INCONSISTENCY at
`file:line`. They are the highest-value conventions for new work, not an
exhaustive census.

`performance.md`'s norms are profile-verified, with the measurements in
`notes/2026-07-20-displayed-triangle.md` and
`notes/2026-07-20-displaced-optimization.md`. `elaboration.md`'s claims
are probe-verified, with the probes and the per-base endpoint table in
`notes/2026-07-24-refl-inference-policy.md`.
