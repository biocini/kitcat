---
name: log
description: Write a durable end-of-session log for work in this Cubical Agda library — completed work, strongest findings and decisions, modules touched, spikes and their fates, theorem-ledger changes, preserved failures, a process review with workflow-revision proposals, open questions, and next steps. Use when asked to log the session, save session notes, write up what was done, record progress, or close out a working session. Produces an append-only log in notes/session-logs/ plus a dated entry at the top of CHANGELOG.md.
---

Run `/log` — the slash command expands the full workflow in the
active session; do not read a prompt-template path from the skill
directory. Master prompt: `.agents/prompts/log.md`.
