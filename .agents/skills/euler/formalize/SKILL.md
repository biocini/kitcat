---
name: formalize
description: Formalize an informal theorem, paper, or chapter into the proof library with kernel-checked delivery. Use when the user asks to formalize a result, mechanize a proof, port a paper's mathematics into the library, or produce a verified development with provenance.
---

# Formalize

Run the `/formalize` workflow. The slash command expands the full workflow instructions in the active session; do not try to read a relative prompt-template path from the installed skill directory.

Requires a toolchain block (`TOOLCHAIN.md` at project root or a `## Toolchain` section in the project `AGENTS.md`); the workflow asks the user for one when missing and never invents check commands.

Agents used: `researcher`, `verifier`, `reviewer`

Output: formalized code in the library tree per `lib-layout`, plus a formalization report in `outputs/` with a `.provenance.md` sidecar recording checker runs and the obligation inventory.
