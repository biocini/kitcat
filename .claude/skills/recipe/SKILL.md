---
name: recipe
description: Find ranked, implementable proof strategies for a theorem or formalization goal from literature, prior mechanizations, and the local library. Use when the user wants to know how to prove something, which induction principle or encoding to use, what prerequisites a proof needs, or whether a formalization is feasible in this library.
argument-hint: <theorem-or-goal>
---

# Recipe

Run the recipe workflow: read `.claude/commands/recipe.md` and follow it as the active instructions for: $ARGUMENTS

Agents used: `researcher`, optionally `verifier`

Output: ranked recipe brief in `outputs/` with prerequisite inventory (located or missing), prior mechanizations, implementation plan, and source provenance.
