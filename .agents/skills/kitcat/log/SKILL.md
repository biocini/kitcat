---
name: log
description: Write a durable end-of-session log for work in this Cubical Agda library — completed work, strongest findings and decisions, modules touched, spikes and their fates, theorem-ledger changes, preserved failures, open questions, and next steps. Use when asked to log the session, save session notes, write up what was done, record progress, or close out a working session. Produces an append-only log in notes/session-logs/ plus a dated entry at the top of CHANGELOG.md.
argument-hint: [focus-or-slug]
args: [focus-or-slug]
section: Project & Session
topLevelCli: true
---

# Session Log

Write the end-of-session log for: $ARGUMENTS (optional focus or
slug hint; may be empty).

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness.

Derive a short slug from the session's main thread (lowercase,
hyphens, no filler words, at most 5 words); when $ARGUMENTS supplies
one, use it. This run writes exactly two things: the log
`notes/session-logs/<YYYY-MM-DD>-<slug>.md`, and one dated entry
appended at the TOP of `CHANGELOG.md` (newest first). The division
of labor: the changelog records what happened — what landed, what
was verified, what failed, what it superseded; the latest session
log records where things stand — state, open questions, and the
next-step preview.

This is an execution request, not a request to explain the workflow.
Begin by gathering evidence, not with prose about the protocol.

The log directory is append-only history: one file per session,
never overwrite or edit a prior log. If the target filename already
exists — a second session in one day — choose a distinct slug rather
than reuse the file. Continuity lives in the log chain itself and
in `docs/roadmap.md`: read the previous entry and the roadmap so
the log records movement against the last next-step preview and
the standing targets. Close every entry with a next-step preview —
the following session opens on it.

## Gather

Reconstruct the session from repository evidence, not memory alone;
scope "this session" as the commit range since the previous
`notes/session-logs/` entry, falling back to uncommitted state when no prior
log anchors it:

- With the shell capability, take git status, diff, and recent log
  to enumerate modules touched, commits made, and uncommitted work.
- With the file-search capability, list spikes created this session
  under `src/Test/` and determine each one's fate: promoted,
  refuted, abandoned, or still open.
- Diff `docs/gloss.md` for ledger entries added or upgraded
  (✅ / 🧪 / 📐 / ⚠️), and check `src/Gloss/` for new certificates.
- Sweep the session's plan ledgers for failed attempts preserved
  there and abandoned hypotheses.
- Collect pointers to run artifacts the session produced:
  `notes/plans/`, `notes/research/`, `notes/watches/`.
- When the visible conversation no longer contains the session's
  earlier work, use the session-recovery capability to recover it.
  A capability with no visible tool is recorded in the log as
  BLOCKED with the manual command a human could run; never simulate
  it or claim its result — log what is actually visible.

## Contents

The log opens with a header block: a title line
`# Session log — <descriptive title>` (name the branch when it
matters), a **Date** line, a **Scope** paragraph — the session's
arc in a few sentences: what was pursued, what was built, where it
happened — and a bold **Status** line honest to verification (e.g.
"designed + verified-sound, not built"). Then it records, in this
order:

1. **Work completed** — what was done, at the level of modules and
   results, not keystrokes, presented as the session's arc: each
   investigation step with its course corrections and declined
   directions pinned, with reasons; and movement against the
   previous log entry's next-step preview and `docs/roadmap.md`'s
   targets.
2. **Strongest findings and decisions** — each load-bearing claim
   labeled: VERIFIED only for claims machine-checked in this
   repository (name the module or Gloss certificate); claims taken
   from literature are CONJECTURED, typically written `CONJECTURED,
   SOURCE-CHECKED against <ref>`; SOURCE-CHECKED only when the cited
   document was opened and states the claim. External claims that
   matter carry direct stable URLs or DOIs.
3. **Modules touched** — created, edited, renamed, or deleted, with
   typecheck status where known.
4. **Spikes** — each `src/Test/` spike created this session, with
   its fate.
5. **Theorem ledger** — `docs/gloss.md` entries added or upgraded,
   with their status markers.
6. **Failures preserved** — attempts preserved in plan ledgers,
   each with one line on why the approach failed.
7. **Proposals** — candidate `resources/` entries, spikes worth
   running, ledger entries to pursue. Proposals are recorded here,
   never executed as a side effect of logging.
8. **Meta-process notes worth carrying** — lessons about how the
   work went that a future session should apply: probe patterns
   that produced superficial verdicts and what fixed them, briefs
   that misfired, disciplines that paid off. Omit the section when
   the session genuinely produced none.
9. **Open questions and risks** — including MAJOR verification
   findings (below) and anything two consecutive failures forced to
   a full stop.
10. **Next steps** — concrete, ordered, resumable by a fresh
    session.
11. **Artifacts** — paths to the run artifacts collected above, plus
    blocked capabilities and degraded delegations from this session,
    each with what was done instead.

## Verify and deliver

Before saving, run an adversarial pass over the draft: claims
labeled stronger than their evidence, spike fates asserted without
checking the file, ledger statuses that disagree with
`docs/gloss.md`, novelty language without a recorded search, and
sections surviving from earlier drafts that the final evidence no
longer supports. Grade findings FATAL / MAJOR / MINOR. Fix FATAL
findings before delivery and run one more pass after the fixes;
move MAJOR findings into Open Questions; accept MINOR.

Save the log to `notes/session-logs/<YYYY-MM-DD>-<slug>.md`. Then
append the changelog entry at the TOP of `CHANGELOG.md` (creating
the file with its header when absent): a dated `## <YYYY-MM-DD> —
<title>` section, concise and newest-first, stating what landed,
what was verified (with honest markers: verified / unverified /
blocked / inferred), what failed, and what it superseded, linking
the session log and any documents the session enshrined. No
sidecar: the log is itself the provenance artifact, which is why
blocked capabilities, degraded delegations, and verification status
live in its body. End by verifying on disk that both files exist
before stopping; never stop at an unsaved draft.
