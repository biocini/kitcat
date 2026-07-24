---
name: watch
description: Create a research watch baseline for a mathematical topic or mechanization area, and optionally schedule follow-up checks when scheduling tools are visible. Use when the user asks to monitor a field, track new papers or mechanizations, watch an upstream library, or set up alerts.
---

# Watch

Run the `/watch` workflow. The slash command expands the full workflow instructions in the active session; do not try to read a relative prompt-template path from the installed skill directory.

Output: baseline survey in `outputs/`, plus a scheduled follow-up only when a scheduling tool is visible. If scheduling is unavailable, the workflow records that block instead of claiming a recurring watch exists.
