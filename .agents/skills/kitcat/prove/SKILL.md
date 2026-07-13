---
name: prove
description: Run the canonical Agda pipeline for a construction, bug fix, or refactor in the kitcat library — analyzer prepares (structural analysis + proof strategy), coder implements, then analyzer reviews for accuracy and reviewer runs the mechanical gate. Use to implement or fix Agda when the roster is present, mechanize a lemma end to end, or take a construction from strategy to a committed-ready module. Orchestrates the existing agent-roles; keeps Lane's GO gates as prose stops.
---

Run `/prove` — the slash command expands the full workflow in the
active session; do not read a prompt-template path from the skill
directory. Master prompt: `.agents/prompts/prove.md`.
