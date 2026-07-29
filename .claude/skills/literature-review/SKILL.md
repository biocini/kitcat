---
name: literature-review
description: Run a literature review on a mathematical topic, author, lab, or mechanization corpus. This skill should be used when the user asks for a lit review, paper survey, state of the art, academic landscape summary, or a review of what a library or group has formalized.
argument-hint: <topic-or-author-or-corpus>
---

# Literature Review

Run the lit workflow: read `.claude/commands/lit.md` and follow it as the active instructions for: $ARGUMENTS

Agents used: `researcher`, `verifier`, `reviewer`

Output: literature review in `outputs/` with `.provenance.md` sidecar.
