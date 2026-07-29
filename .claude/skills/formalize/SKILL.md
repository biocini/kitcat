---
name: formalize
description: Formalize an informal theorem, paper, or chapter into the proof library with kernel-checked delivery. This skill should be used when the user asks to formalize a result, mechanize a proof, port a paper's mathematics into the library, or produce a verified development with provenance.
argument-hint: <target>
---

# Formalize

Run the formalize workflow: read `.claude/commands/formalize.md` and follow it as the active instructions for: $ARGUMENTS

Requires a toolchain block (`.euler/TOOLCHAIN.md`, or a `## Toolchain` section in the project `CLAUDE.md`); the workflow asks the user for one when missing and never invents check commands.

Agents used: `researcher`, `verifier`, `reviewer`

Output: formalized code in the library tree per `lib-layout`, plus a formalization report in `outputs/` with a `.provenance.md` sidecar recording checker runs and the obligation inventory.
