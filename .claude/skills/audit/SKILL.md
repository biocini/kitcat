---
name: audit
description: Audit a formalization against its informal source. This skill should be used when the user asks to check a mechanization's faithfulness, find statement-level mismatches or definition gaming, inventory sorries/axioms/unsafe flags, or verify that a library development reproduces what a paper claims.
argument-hint: <formalization-and-source>
---

# Audit

Run the audit workflow: read `.euler/euler.md` (the suite contract) and `.claude/commands/audit.md`, and follow both as the active instructions for: $ARGUMENTS

Agents used: `researcher`, optionally `verifier`

Output: audit report in `outputs/` with a correspondence table (informal anchor ↔ file:line ↔ fidelity status), mechanical inventory, and a `.provenance.md` sidecar.
