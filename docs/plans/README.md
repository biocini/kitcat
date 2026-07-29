# Plans

Standing plans. A plan here outlives the session that wrote it. It
carries gates, and a later session reads it cold.

A plan belongs here when a later session must pick it up. It has
gates, it names what blocks it, and something cites it. Git tracks
this directory, so a fresh clone sees the plan.

A plan does **not** belong here when one workflow run consumes it. A
brief for a single subagent dispatch is scratch. Those live in
`outputs/.plans/`, which git ignores. Discard them once the run
ends.

The other registers, for contrast:

| Location | Holds |
| --- | --- |
| `docs/plans/` | Standing programs with gates |
| `docs/guidelines/` | Standards, stated abstractly, no live-tree reference |
| `docs/roadmap.md` | The research projects and their order |
| `<namespace>/gloss.md` | Commentary on a construction, beside its code |
| `<namespace>/lemmata.md` | Statements: theorem, location, status, date |
| `notes/` | Dated session records |
| `outputs/.plans/` | Ephemeral run briefs, gitignored |

Name a plan for its subject, not its date. A plan is revised in place
as its gates clear. Session history belongs in `notes/`.

Write the gate into the plan. A plan that does not say what blocks it
invites a session to start work that cannot finish.
