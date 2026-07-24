---
description: Inspect visible research/formalization run state, scheduled follow-ups when available, and durable artifacts on disk.
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

Inspect active research and formalization work for this project.

Requirements:

- Use the visible process/background-job tool to list runs only when one is
  visible and the user is asking about run state; otherwise record
  `Process state: BLOCKED - process tool not available`.
- Use scheduling tooling only when it is visible; otherwise record
  `Schedule state: BLOCKED - scheduling tool not available`.
- Inspect durable state on disk:
  - `outputs/.plans/` — active and completed run plans
  - `outputs/.prove/` — proof-loop session files (`prove.md`, `prove.jsonl`,
    `prove.sh`): current metric, iterations used, last decision
  - `outputs/` — watch baselines, reports, audits, and provenance sidecars
  - `notes/` — session logs
  - `CHANGELOG.md` — the lab notebook's most recent entries
- Summarize:
  - active background processes if a process tool is visible
  - queued or recurring research watches if scheduling tooling is visible
  - durable watch/prove/formalize artifacts found on disk
  - failures or stale runs that need attention (a prove loop whose last
    iteration predates newer library edits is stale — say so)
  - the next concrete command the user should run if they want logs or
    detailed status
- Be concise and operational.
