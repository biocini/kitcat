---
name: mechanize
description: Mechanize a paper's theorem, definition, or construction in Cubical Agda. Use when asked to formalize a published result, mechanize a proof, port a construction from a paper into the library, verify a claimed theorem by typechecking, or build a formalization plan for a source. Extracts the claims, builds a per-claim proof ledger, gates on an explicit execution-mode choice (plan-only, spike, or full module), and reports outcomes against pre-registered success criteria with a provenance sidecar.
---

Run `/mechanize` — the slash command expands the full workflow in the
active session; do not read a prompt-template path from the skill
directory. Master prompt: `.agents/prompts/mechanize.md`.
