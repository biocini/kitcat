---
name: recipe
description: Find ranked, implementable proof strategies for a theorem or formalization goal from literature, prior mechanizations, and the local library. Use when the user wants to know how to prove something, which induction principle or encoding to use, what prerequisites a proof needs, or whether a formalization is feasible in this library.
---

# Recipe

Run the `/recipe` workflow. The slash command expands the full workflow instructions in the active session; do not try to read a relative prompt-template path from the installed skill directory.

Agents used: `researcher`, optionally `verifier`

Output: ranked recipe brief in `outputs/` with prerequisite inventory (located or missing), prior mechanizations, implementation plan, and source provenance.
