---
name: summarize
description: Summarize a mathematical source — paper, textbook chapter, lecture notes, or mechanization file — without context rot. Use when the user asks to summarize, digest, or get the gist of a specific document, especially long ones. Uses tiered RLM reading with on-disk checkpointing.
---

# Summarize

Run the `/summarize` workflow. The slash command expands the full workflow instructions in the active session; do not try to read a relative prompt-template path from the installed skill directory.

Agents used: `researcher` (Tier 3 only)

Output: structured summary at `outputs/<slug>-summary.md` with theorem/section anchors preserved.
