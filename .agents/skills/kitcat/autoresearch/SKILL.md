---
name: autoresearch
description: Run a bounded proof-optimization loop over an Agda module or spike. Pick a metric — typecheck success, wall-clock time, or a countable proxy (warnings, holes, axiom count, LOC, import count) — record a baseline, then iterate one change at a time, keeping what improves the metric and reverting what does not. Use when asked to optimize a proof, shrink an axiom set or import list, reduce warnings or holes, speed up typechecking, or run an experiment or optimization loop. Produces a ledgered run in notes/plans/ and a baseline-vs-final summary in notes/research/ with a provenance sidecar.
argument-hint: <target-and-goal>
args: <target-and-goal>
section: Research Workflows
topLevelCli: true
---

# Autoresearch

Run a bounded proof-optimization loop for: $ARGUMENTS

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness.

Derive a short slug from the target and goal (lowercase, hyphens,
no filler words, at most 5 words). Every file this run writes uses
that slug.

This is an execution request, not a request to explain the
workflow. Begin with the gather step, not with prose about the
protocol.

## Scope guard

A run writes only: `notes/plans/`, `notes/research/`,
spike files under `src/Test/`, and — solely when the user has
authorized full-module mode — the one declared target module.
Nothing else is edited, created, or deleted. Metric improvements
obtained by weakening checks are invalid: no `-W` suppression
flags, no postulates, no unsafe pragmas, no hom truncation. A kept
change on a target module must typecheck with zero warnings (exit
42 is failure) whatever the metric says.

## Workflow

1. **Gather** — If `notes/plans/<slug>.md` already exists, ask the
   user (user-question capability) whether to resume or start
   fresh; on resume, read the plan ledger tail before touching
   anything. The argument `off`
   stops the active loop, keeps all artifacts, and goes straight to
   Verify and Deliver with the data so far; `clear` — after user
   confirmation via the user-question capability — deletes the
   prior run's plan and spike files, nothing else, and starts
   fresh. Otherwise collect, asking for whatever
   the arguments do not settle:
   - The target: a module (dot-path) or a spike to be created under
     `src/Test/`.
   - The metric: `just check <Mod>` success (optionally
     wall-clocked via the shell capability), or a countable proxy —
     warnings, holes, axiom count, LOC, import count — computed
     with the file-search and shell capabilities. Record the exact
     measurement command, unit, and direction of improvement.
   - The iteration budget (offer 20 as the default) and, if the
     user has one, a stopping value for the metric.
   - The mode: spike mode (default — all changes live in one
     timestamped spike file `src/Test/<Name>-<timestamp>.lagda.md`)
     or full-module mode (edits the target module directly;
     requires explicit user authorization and a choice of current
     branch or a new one — no branches or commits beyond what the
     user approves here).
2. **Plan and confirm** — Write `notes/plans/<slug>.md`: the
   target, mode, measurement command, metric unit and direction,
   iteration budget, stopping value if any, candidate hypotheses to
   try, and an empty iteration ledger. Present the plan compactly
   (target, metric, command, mode, budget) and require explicit
   confirmation via the user-question capability before running
   anything. For non-routine proof strategy — h-levels, coherence,
   transport chains, equivalences — dispatch the
   `analyzer` agent for a strategy memo first; when that
   agent is absent, reason lead-owned and record the delegation as
   degraded. Memo claims are CONJECTURED until machine-checked.
3. **Baseline** — Before any change, run the measurement command
   with the shell capability and record the baseline value, the
   exact command, and the date in the ledger. A baseline that
   cannot be measured stops the run: report what failed and wait
   for direction.
4. **Loop** — Each iteration, up to the budget:
   - State one hypothesis and make exactly one change — in the
     spike file, or in the target module in full-module mode.
     Iteration edits may be dispatched to the `coder`
     agent with a self-contained brief; when absent, edit
     lead-owned and record the delegation as degraded.
   - Measure with the recorded command. Never substitute a
     different command mid-run; changing the metric is a new run.
   - Decide: keep the change if the metric improved, revert
     otherwise. Ties revert unless the user set a different rule at
     confirmation. Before reverting a failed attempt, preserve its
     text in the plan ledger entry.
     Restore the spike to its last-kept state before the next
     measurement; a comment block below an explicit
     abandoned-attempts marker may hold the failed text instead,
     only when it cannot affect typechecking or the measurement. A
     dispatched coder's brief states this preservation rule.
   - Log the iteration in the plan ledger: number, hypothesis,
     change location, metric value, decision (kept or reverted),
     and evidence (command output summary). Every iteration is
     logged; none is silently skipped.
   - The plan ledger is the run's only progress record; keep its
     entries current at each milestone.
   - Stop early on: the stopping value reached; the user saying
     stop; or two consecutive failures of the same approach — that
     is a full stop: state what you know, what you don't, and what
     you tried, then wait for direction. Never stack fixes on a
     broken approach.
5. **Verify** — Run an adversarial pass over the ledger and draft
   summary: ledger entries missing metric values, kept changes
   without a recorded passing measurement, target-module changes
   kept without a zero-warning typecheck, metric gains from
   weakened checks, claims stronger than their evidence, and
   sections surviving from earlier drafts that the final evidence
   no longer supports. Dispatch the `reviewer` agent
   for kept target-module changes when present; otherwise
   self-review. Grade findings FATAL / MAJOR / MINOR; fix FATAL
   before delivery and run one more pass after the fixes; note
   MAJOR in Open Questions; accept MINOR.
6. **Deliver** — Save the summary to `notes/research/<slug>.md`:
   baseline vs final metric values, the iteration ledger (or a
   pointer to the plan file plus the kept/reverted counts), the
   kept-change list with file locations, abandoned hypotheses with
   reasons, and Open Questions. A kept change is VERIFIED only when
   its measurement ran in this repository (name the module and
   command); untested hypotheses remain CONJECTURED. Results worth
   the theorem ledger or a `resources/` entry are proposals in the
   summary and sidecar, never executed as a side effect. Write the
   sidecar `notes/research/<slug>.provenance.md` recording: date
   and who requested the run; the measurement command and
   environment (branch, mode); iterations attempted vs kept vs
   reverted, with reasons; sources consulted vs accepted vs
   rejected with vetting status ("none" when the run consulted no
   literature); intermediate files (plan, spike, session log) with
   producers (agent, or lead-owned degraded); blocked capabilities
   and degraded delegations with what was done instead; and
   verification status — PASS, PASS WITH NOTES (MAJOR findings
   remain in Open Questions), or BLOCKED (name the check that
   could not run). Verify on disk that both files exist before
   stopping; never stop at an intermediate draft.

## Honesty rules (binding)

- A metric value exists only if its command ran and its output was
  captured; a measurement that did not run is never estimated,
  extrapolated, or reported as a value.
- A capability with no visible tool is reported BLOCKED in the plan
  and sidecar with the manual command a human could run instead;
  never simulate a capability or claim its result.
- Failed attempts are part of the deliverable: every reverted
  iteration appears in the ledger with its text preserved before
  reverting.
- Improvement language states the measured delta against the
  recorded baseline — never "optimal" or "fastest possible".
