---
description: Write a durable session log with completed work, findings, open questions, and next steps.
section: Project & Session
topLevelCli: true
---
## Tool Discipline (Read First)

Tool names are literal. Use only tools visible in the current tool set.

- To ask the user a question, write plain chat text and wait for the next user
  message, unless a visible user-question tool exists. Do not invent one.
- If a tool returns `Tool not found`, do not retry the same invalid call. Map
  to a canonical visible tool and valid arguments, or record the capability as
  blocked.

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
- Derive a short slug from the session's main objective, and save the log to
  `notes/<date>-<slug>.md` so concurrent sessions never collide.
