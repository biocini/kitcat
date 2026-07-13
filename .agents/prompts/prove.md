---
name: prove
description: Run the canonical Agda pipeline for a construction, bug fix, or refactor in the kitcat library — analyzer prepares (structural analysis + proof strategy), coder implements, then analyzer reviews for accuracy and reviewer runs the mechanical gate. Use to implement or fix Agda when the roster is present, mechanize a lemma end to end, or take a construction from strategy to a committed-ready module. Orchestrates the existing agent-roles; keeps Lane's GO gates as prose stops.
argument-hint: <target-or-goal>
args: <target-or-goal>
section: Project & Session
topLevelCli: true
---

# Prove

Run the Agda pipeline for: $ARGUMENTS

Read `.agents/CLAUDE.md` (the cross-agent contract),
`.agents/methodology.md` (the working discipline), and
`.agents/skills/kitcat/HARNESS.md` first. This orchestrates the
existing roster by dispatch; it invents no capability. It is the
symmetric bracket of the methodology: **analyzer prepares → coder
implements → analyzer reviews for accuracy + reviewer runs the
mechanical gate.** Every dispatch is a self-contained brief; when a
named agent is absent in the harness, run that stage lead-owned and
record the delegation as degraded.

Derive a run slug per the contract and open `notes/plans/<YYYY-MM-DD>-<slug>.md`
as the run ledger: failed proof attempts are preserved there before
reverting, wall salvage is registered under a "do not re-derive;
build on" heading, and degraded delegations are recorded there.

**Spike mode.** When the run's target is itself a spike, the
coder's deliverable IS the verdict set; the accuracy review still
runs in full; the mechanical gate scopes to the tier — the
typecheck at zero warnings is the pin, and timestamped `Test/`
scratch is lint-exempt by name per root `CLAUDE.md`'s Test rules;
the close delivers verdicts and promotions HELD for Lane's ruling,
not a committed-ready module.

## 1. Prepare — the `analyzer`

Dispatch the `analyzer` with the target. It delivers: the structural
placement (namespace, the narrowest providing modules, duplication
check against what exists), and — for any non-trivial proof
(h-levels or truncation, equivalence, coherence or naturality,
transport chains, fiber arguments, univalence) — the proof strategy
as a fully type-annotated sketch, with each load-bearing CONJECTURED
claim marked and the spike it needs named. Routine proofs (ap, sym,
simple paths) skip the strategy half.

**GO gate.** Summarize the analyzer's plan and the spikes it calls
for. Do not implement until Lane confirms the approach (or the
target is a routine fix the analyzer cleared as needing no
strategy). A design pre-registered with kill criteria and ratified
by Lane in a prior session satisfies this gate on arrival; the
gate then applies to material deviations the analyzer proposes.
With Lane absent, a deviation proceeds only when it is itself
spike-pinned with the pre-registered kill criteria intact and is
reported beside the verdicts; a deviation that changes what the
checks decide is a full stop.

## 2. Implement — the `coder`

Dispatch the `coder` with a self-contained brief built from the
analyzer's output (placement, the annotated sketch, the target
file). The coder pins any open fork with a spike first — the spike
typechecks the fork against the real foundation, returning a verdict
in {DERIVED, STUCK, PARTIAL}; the typecheck is the pin, prose is
not. Definitional reductions the proof leans on are re-asserted as
`killcheck-<name> = refl`. On a genuine two-strikes wall the coder
keeps the spike with `-- STUCK:` comments and its salvage, reverts,
invents no axiom, and escalates. Constraints:
`--safe --erased-cubical --no-guardedness`, no postulates, no
external libraries, never truncate homs; the run never commits.

**GO gate.** Report what landed and its typecheck status. If a spike
was the mode, report its verdict and hold for Lane's GO before a
full-module implementation.

## 3. Review — the `analyzer` (accuracy) and the `reviewer` (gate)

After the implementation typechecks, the accuracy review and the
mechanical gate follow the contract's Delegation ordering: they run
in sequence, never in the same parallel dispatch — the `analyzer`'s
accuracy pass (the adversarial pass) runs first and sharpens what
the `reviewer`'s mechanical gate (the review pass) then judges. The
sequence, in order, per `.agents/CLAUDE.md`'s Delegation section:

- The `analyzer` reviews for **accuracy**: does it prove what the
  strategy specified, by the route specified, resting on the lemmas
  it claims; are the h-level and coherence obligations discharged,
  not assumed; did the definitional reductions actually fire.
- Between the two, the conditional **citation review**: when the
  implementation added or changed credit comments — the coder's
  completion report flags this — dispatch the `verifier` per the
  contract's code-citation review clause; a change with no new or
  altered credits dispatches no review.
- The `reviewer` runs the **mechanical gate**: re-runs `just check`
  (exit 42 is failure, zero warnings) and `just lint` on every
  touched module rather than trusting the coder's word, plus
  hard-rule conformance, the certificate↔ledger bijection, and
  credit comments — the reviewer's brief carries the analyzer's
  memo, whose credit obligations are the baseline for the
  completeness half of that check. Blocking findings are fixed and
  re-reviewed.

## 4. Close

Report the outcome: modules touched with typecheck status, any
`docs/gloss.md` entry or `Gloss.*` certificate the result graduates
into (same-session, per the methodology), spikes and their fates,
and any wall preserved with its salvage. Commit nothing — Lane
commits. Two consecutive failures on the same goal is a full stop:
state what is known, what was tried, what is needed.
