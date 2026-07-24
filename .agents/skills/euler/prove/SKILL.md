---
name: prove
description: Bounded proof loop that tries hypotheses, measures with the proof checker as oracle, keeps what checks, and records what fails. Use when the user asks to close sorries/obligations iteratively, make a module build, prove a specific lemma, minimize axiom usage, or run a proof-strategy experiment loop.
---

# Prove

Run the `/prove` workflow. The slash command expands the full workflow instructions in the active session; do not try to read a relative prompt-template path from the installed skill directory.

Requires a toolchain block; the loop refuses to run without an executable check command, since the checker is the only oracle.

Session files: `prove.md`, `prove.sh`, `prove.jsonl`

Output: iteration log with keep/revert decisions and a failed-strategy journal; outcome summary with honest status labels.
