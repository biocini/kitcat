---
name: audit
description: Audit a formalization against its informal source. Use when the user asks to check a mechanization's faithfulness, find statement-level mismatches or definition gaming, inventory sorries/axioms/unsafe flags, or verify that a library development reproduces what a paper claims.
---

# Audit

Run the `/audit` workflow. The slash command expands the full workflow instructions in the active session; do not try to read a relative prompt-template path from the installed skill directory.

Agents used: `researcher`, optionally `verifier`

Output: audit report in `outputs/` with a correspondence table (informal anchor ↔ file:line ↔ fidelity status), mechanical inventory, and a `.provenance.md` sidecar.
