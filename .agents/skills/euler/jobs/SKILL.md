---
name: jobs
description: Inspect visible research and formalization run state, scheduled follow-ups when available, and durable artifacts on disk. Use when the user asks what's running, wants proof-loop status, or wants a rundown of active research state.
---

# Jobs

Run the `/jobs` workflow. The slash command expands the full workflow instructions in the active session; do not try to read a relative prompt-template path from the installed skill directory.

Shows visible process/scheduler state when those tools are installed, plus durable watch/prove/formalize artifacts on disk. If process or scheduling tools are unavailable, the workflow reports that capability as blocked instead of claiming background state exists.
