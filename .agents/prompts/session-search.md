---
name: session-search
description: Recover prior work and decisions from this repository's session history — rulings, plans, proof attempts, where a thread left off. Use when asked what was decided earlier, what happened in a previous session, where work left off, or to find an earlier discussion, formulation, or failed attempt. Read-only; returns quoted excerpts with source paths and dates and writes nothing.
argument-hint: <what-to-recover>
args: <what-to-recover>
section: Project & Session
---

# Session Search

Recover prior work and decisions matching: $ARGUMENTS

Read `.agents/CLAUDE.md` and `.agents/skills/kitcat/HARNESS.md`
first: the contract binds the cross-agent conventions this skill
defers to; HARNESS maps every capability named below to the tools
in your harness.

This is an execution request, not a request to explain the workflow.

## Order of consultation

1. **Curated surfaces first**, with the file-read and file-search
   capabilities. These were written deliberately; a hit here
   outranks a raw transcript hit for the same fact.
   - `docs/roadmap.md` — the standing targets and their gates.
   - `CHANGELOG.md` — the lab notebook: what landed, what was
     verified, what failed, newest first.
   - `notes/session-logs/` — dated session logs, one file per session; the
     latest entry records where work left off and the next-step
     preview.
   - `notes/plans/` — run plans with task ledgers and
     verification logs.
   - `docs/gloss.md` — the theorem ledger: what is proven, at
     what status.
   - `notes/research/` — research finals, intermediates, and
     provenance sidecars.
2. **Raw transcripts second**, via the session-recovery
   capability. Transcript stores and their record schemas differ
   per harness; HARNESS names the store, the search route, and any
   interactive search available in the harness you are running in.
   Search the store for the query terms, then open the matching
   transcript to read the hit in context before quoting it.

When no session-recovery route is visible, report
`session-recovery: BLOCKED — no visible tool` in your reply, state
the manual search command a human could run over their transcript
store, and deliver what the curated surfaces yielded.

## Reporting rules (binding)

- Every recovered claim is quoted with its source path and, where
  the artifact carries one, its date. A transcript hit cites the
  transcript file.
- A recollection that cannot be traced to an artifact on disk is
  reported as unverifiable — stated as such, never asserted as
  recovered fact.
- Recovered claims keep their original epistemic status: a
  transcript saying something was proven is not VERIFIED — only a
  claim machine-checked in this repository is; name the module or
  Gloss certificate.
- This skill is read-only: it writes nothing anywhere — no notes,
  no logs, no plan files. Findings are delivered in the reply, and
  anything worth persisting is proposed to the user, never written
  as a side effect.
