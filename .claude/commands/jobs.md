---
description: Inspect visible research/formalization run state, scheduled follow-ups when available, and durable artifacts on disk.
disable-model-invocation: true
---

Inspect active research and formalization work for this project.

Requirements:

- List background runs with the session's task tooling (TaskList/TaskOutput,
  background Bash jobs) when the user is asking about run state; if none is
  available, record `Process state: BLOCKED - process tool not available`.
- List scheduled follow-ups with the session's scheduling tooling (CronList)
  when it is available; otherwise record
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
