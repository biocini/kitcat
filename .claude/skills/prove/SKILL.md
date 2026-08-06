---
name: prove
description: Bounded proof loop that tries hypotheses, measures with the proof checker as oracle, keeps what checks, and records what fails. This skill should be used when the user asks to close sorries/obligations iteratively, make a module build, prove a specific lemma, minimize axiom usage, or run a proof-strategy experiment loop.
argument-hint: <goal>
---

# Prove

Run the prove workflow: read `.euler/euler.md` (the suite contract) and `.claude/commands/prove.md`, and follow both as the active instructions for: $ARGUMENTS

Requires a toolchain block; the loop refuses to run without an executable check command, since the checker is the only oracle.

Session files: `prove.md`, `prove.sh`, `prove.jsonl`

Output: iteration log with keep/revert decisions and a failed-strategy journal; outcome summary with honest status labels.
