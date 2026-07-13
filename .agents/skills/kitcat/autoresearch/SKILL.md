---
name: autoresearch
description: Run a bounded proof-optimization loop over an Agda module or spike. Pick a metric — typecheck success, wall-clock time, or a countable proxy (warnings, holes, axiom count, LOC, import count) — record a baseline, then iterate one change at a time, keeping what improves the metric and reverting what does not. Use when asked to optimize a proof, shrink an axiom set or import list, reduce warnings or holes, speed up typechecking, or run an experiment or optimization loop. Produces a ledgered run in notes/plans/ and a baseline-vs-final summary in notes/research/ with a provenance sidecar.
---

Run `/autoresearch` — the slash command expands the full workflow in the
active session; do not read a prompt-template path from the skill
directory. Master prompt: `.agents/prompts/autoresearch.md`.
