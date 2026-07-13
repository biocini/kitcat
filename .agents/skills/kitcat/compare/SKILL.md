---
name: compare
description: Build a source-comparison matrix over papers, pages, or formalizations that treat the same concept in type theory, category theory, univalent mathematics, or programming language foundations. Use when asked to compare definitional variants, competing formulations of the same categorical structure, formalization approaches, or claims across sources — the natural kitcat use is comparing definitional variants across the literature before mechanizing one. Produces a matrix (source, key claim or definitional choice, evidence type in proof-status vocabulary, caveats, confidence) in notes/research/ with a provenance sidecar.
---

Run `/compare` — the slash command expands the full workflow in the
active session; do not read a prompt-template path from the skill
directory. Master prompt: `.agents/prompts/compare.md`.
