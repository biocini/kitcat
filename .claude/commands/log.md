---
description: Write a durable session log with completed work, findings, open questions, and next steps.
disable-model-invocation: true
---

Write a session log for the current research and formalization work.

Requirements:

- Summarize what was done in this session.
- Capture the strongest findings or decisions — including discharged
  obligations, failed proof strategies (with reasons), and encoding decisions.
- List open questions, unresolved risks, and concrete next steps.
- Reference any important artifacts: files in `notes/`, `outputs/`,
  `outputs/.plans/`, and `papers/`, and any modules delivered into the
  library tree (with paths).
- Record verification state honestly with the claim-level labels (`verified`,
  `unverified`, `blocked`, `inferred`): which checker runs happened, what the
  obligation inventory is.
- If any external claims matter, include direct source anchors (URLs, theorem
  numbers).
- Derive a slug per euler.md §File naming, and save the log to
  `notes/<date>-<slug>.md` so concurrent sessions never collide.
- Append a matching entry to `CHANGELOG.md` (newest first): a concise summary
  of the session in the notebook's idiom — what changed, what checked, what
  failed, claim-level labels, commits — ending with a link to the session log
  this run just wrote. The changelog entry and the session log are one
  deliverable; never write one without the other.
