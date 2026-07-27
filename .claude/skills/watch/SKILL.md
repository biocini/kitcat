---
name: watch
description: Create a research watch baseline for a mathematical topic or mechanization area, and optionally schedule follow-up checks when scheduling tools are visible. Use when the user asks to monitor a field, track new papers or mechanizations, watch an upstream library, or set up alerts.
argument-hint: <topic>
---

# Watch

Run the watch workflow: read `.claude/commands/watch.md` and follow it as the active instructions for: $ARGUMENTS

Output: baseline survey in `outputs/`, plus a scheduled follow-up only when a scheduling tool is available. If scheduling is unavailable, the workflow records that block instead of claiming a recurring watch exists.
