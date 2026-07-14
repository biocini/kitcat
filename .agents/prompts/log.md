---
name: log
description: Write a durable end-of-session log for work in this Cubical Agda library — completed work, strongest findings and decisions, modules touched, spikes and their fates, theorem-ledger changes, preserved failures, a process review with workflow-revision proposals, open questions, and next steps. Use when asked to log the session, save session notes, write up what was done, record progress, or close out a working session. Produces an append-only log in notes/session-logs/ plus a dated entry at the top of CHANGELOG.md.
argument-hint: [focus-or-slug]
args: [focus-or-slug]
section: Project & Session
topLevelCli: true
---

# Session Log

Write the end-of-session log for: $ARGUMENTS (optional focus or
slug hint; may be empty).

Read `.agents/CLAUDE.md` (the cross-agent contract) and
`.agents/skills/kitcat/HARNESS.md` first; the former carries the
cross-agent conventions this workflow defers to, the latter maps
every capability named below to the tools in your harness.

Derive a run slug from the session's main thread per the contract;
when $ARGUMENTS supplies one, use it. This run's durable output is
exactly two things: the log
`notes/session-logs/<YYYY-MM-DD>-<slug>.md`, and one dated entry
appended at the TOP of `CHANGELOG.md` (newest first); the
process-review stage below adds one working-memory report beside
them, and the roadmap reconciliation stage edits `docs/roadmap.md`
only when one of its header's triggers fired. The division
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

## Roadmap reconciliation

With the session gathered, sweep its outcomes against
`docs/roadmap.md`'s targets and test the roadmap's own update
triggers — landed, added, re-gated — per its header, which owns
the trigger list and the not-per-session cadence. Where a trigger
fired and the update is mechanical — a landed target's status, a
ruled re-gate whose wording Lane fixed in-session — apply it to
`docs/roadmap.md` as part of this run. Where it requires judgment
— a re-ordering, new-target wording Lane has not phrased — apply
nothing and carry it to the close report for Lane's discretion,
beside the promotion decision block and the Process review
proposals. No trigger fired: the log records one line ("roadmap:
no triggers") and the roadmap is untouched — the check is
per-session, the edit is trigger-gated.

## Contents

The log opens with a header block: a title line
`# Session log — <descriptive title>` (name the branch when it
matters), a **Date** line, a **Scope** paragraph — the session's
arc in a few sentences: what was pursued, what was built, where it
happened — and a bold **Status** line honest to verification (e.g.
"designed + verified-sound, not built"). Then come the sections:
the list below is name-keyed and order-canonical — its order IS
the canonical section order, each section renders in the log as a
plain named `##` heading (unnumbered), and every cross-reference,
in this workflow and in the log's own prose, cites a section by
name, never by number, so inserting a section costs one list line
(prior logs keep their old numbered headings untouched —
append-only):

- **Work completed** — what was done, at the level of modules and
  results, not keystrokes, presented as the session's arc: each
  investigation step with its course corrections and declined
  directions pinned, with reasons; movement against the previous
  log entry's next-step preview and `docs/roadmap.md`'s targets;
  and the roadmap reconciliation's outcome — the updates applied,
  the items carried to Lane, or the one line "roadmap: no
  triggers".
- **Strongest findings and decisions** — each load-bearing claim
  labeled per the contract's epistemic lexicon (VERIFIED names the
  module or Gloss certificate). External claims that matter carry
  direct stable URLs or DOIs.
- **Modules touched** — created, edited, renamed, or deleted, with
  typecheck status where known.
- **Spikes** — each `src/Test/` spike created this session, with
  its fate.
- **Theorem ledger** — `docs/gloss.md` entries added or upgraded,
  with their status markers; plus the held list — promotions
  awaiting Lane's ruling, this session's and any prior one still
  unruled, carried here until ruled per the contract's promotion
  decision block.
- **Failures preserved** — attempts preserved in plan ledgers,
  each with why the approach failed AND its salvage: the reusable
  machinery the attempt produced and what the wall points at, so a
  future session builds on it rather than re-deriving (the θ-core
  arc's "do not re-derive; build on" heading is the model). A
  preserved failure that names no salvage is under-recorded.
- **Proposals** — candidate `resources/` entries, spikes worth
  running, ledger entries to pursue. Proposals are recorded here,
  never executed as a side effect of logging.
- **Meta-process notes worth carrying** — lessons about how the
  work went that a future session should apply: probe patterns
  that produced superficial verdicts and what fixed them, briefs
  that misfired, disciplines that paid off. Omit the section when
  the session genuinely produced none.
- **Process review** — the session's friction points from the
  process-review stage below, each with its file/moment evidence
  and its mapping: a workflow revision/addition proposal (named
  surface, named change) or a named weakness in an existing
  system, every proposal tagged **ratify-now** (with the exact
  task) or **next-session** (with the open question). Recorded for
  Lane's discretion, never applied by this run.
- **Open questions and risks** — including MAJOR verification
  findings (below) and anything two consecutive failures forced
  to a full stop.
- **Next steps** — concrete, ordered, resumable by a fresh
  session.
- **Artifacts** — paths to the run artifacts collected above, plus
  blocked capabilities and degraded delegations from this session,
  each with what was done instead.

## Process review

With the log drafted, save the draft at its target path so the
reviewer reads it from disk, then dispatch the `process-reviewer`
with a self-contained brief per the contract: the session's dated
plan ledgers under `notes/plans/` (with any shakedown or friction
notes they carry) and the drafted log body, whose Scope and Status
stand in for the changelog entry — that entry is written only
after this stage; include a CHANGELOG delta only when the session
already touched `CHANGELOG.md`. Name the report path
`notes/research/<YYYY-MM-DD>-<slug>-process-review.md`. When the
agent is absent in your harness, run the review lead-owned under
its same contract and record the delegation as degraded per the
contract. Fold the report into the log's Process review section —
friction points, mappings, and tags intact. The proposals are
surfaced to Lane's discretion at close: each awaits ratification as
an immediate task or as next-session work; the log run applies none
of them.

## Verify and deliver

Before saving, run the verify protocol per the contract over the
draft (the draft is self-reviewed in direct mode; the
process-review dispatch is this run's only delegation and adds no
verifier pass). The adversarial sweep for this workflow: claims
labeled stronger than their evidence, spike fates asserted without
checking the file, ledger statuses that disagree with
`docs/gloss.md`, roadmap edits applied without a fired trigger,
novelty language without a recorded search,
process-review proposals worded as if already ratified, and
sections surviving from earlier drafts that the final evidence no
longer supports.

Before writing the log, confirm every load-bearing result proven
this session is in its canonical home: a `docs/gloss.md` entry
held in exact bijection with a frozen `Gloss.*` certificate (per
`src/Gloss/CLAUDE.md`), or the committed module. A result living
only in a `src/Test/` spike, a plan ledger, or the chat is
enshrined NOW, and the log records only the pointer — the T-number
and the module — never the proof. The one exception is a promotion
Lane holds: its tracked, committed evidence stands per the
methodology's P3 held-promotion clause, and the log carries it in
the held list rather than promoting it unruled. If you re-derived
something this session that an earlier session already worked out,
that is the signal to persist it before logging.

Run the memory-hygiene sweep per the contract's memory-is-links
convention: EXTERNALIZE every memory content that is not yet in
its stipulated canonical home (the contract names the home per
content kind), then rewrite the memory layer so it holds only
links into the context layer — never content paragraphs, never a
shadow store. A ruling, design, or state summary surviving in
memory as content at session exit is a hygiene defect the sweep
must clear, not merely flag.

Save the log to `notes/session-logs/<YYYY-MM-DD>-<slug>.md`. Then
append the changelog entry at the TOP of `CHANGELOG.md` (creating
the file with its header when absent): a dated `## <YYYY-MM-DD> —
<title>` section, concise and newest-first, stating what landed,
what was verified (with honest markers: verified / unverified /
blocked / inferred), what failed, and what it superseded, linking
the session log and any documents the session enshrined. No
sidecar: the log is itself the provenance artifact, which is why
blocked capabilities, degraded delegations, and verification status
live in its body. The close report surfaces the Process review
proposals to Lane's discretion explicitly — each with its
ratify-now or next-session tag, each awaiting Lane's ruling as an
immediate task or as next-session work; none is applied by this
run. It names the Theorem ledger section's held list beside them —
every promotion still awaiting Lane's ruling, never silently
dropped — and the judgment-requiring roadmap items the
reconciliation stage carried, each awaiting Lane's wording or
ordering call. End by verifying on disk that both files exist
before stopping; never stop at an unsaved draft.
