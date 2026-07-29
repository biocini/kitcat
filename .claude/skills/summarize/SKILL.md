---
name: summarize
description: Summarize a mathematical source — paper, textbook chapter, lecture notes, or mechanization file — without context rot. This skill should be used when the user asks to summarize, digest, or get the gist of a specific document, especially long ones. Uses tiered RLM reading with on-disk checkpointing.
argument-hint: <source> [--window-size <chars>] [--overlap <chars>] [--tier1-threshold <chars>] [--tier2-threshold <chars>]
---

# Summarize

Run the summarize workflow: read `.claude/commands/summarize.md` and follow it as the active instructions for: $ARGUMENTS

Agents used: `researcher` (Tier 3 only)

Output: structured summary at `outputs/<slug>-summary.md` with theorem/section anchors preserved.
