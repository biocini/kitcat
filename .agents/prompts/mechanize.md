---
name: mechanize
description: Mechanize a paper's theorem, definition, or construction in Cubical Agda. Use when asked to formalize a published result, mechanize a proof, port a construction from a paper into the library, verify a claimed theorem by typechecking, or build a formalization plan for a source. Extracts the claims, builds a per-claim proof ledger, gates on an explicit execution-mode choice (plan-only, spike, or full module), and reports outcomes against pre-registered success criteria with a provenance sidecar.
argument-hint: <paper-or-theorem>
args: <paper-or-theorem>
section: Research Workflows
topLevelCli: true
---

# Mechanize

Mechanize in Cubical Agda: $ARGUMENTS

Read `.agents/CLAUDE.md` (the cross-agent contract) and
`.agents/skills/kitcat/HARNESS.md` first: the contract states the
shared conventions (the epistemic lexicon, degraded delegation),
and HARNESS.md maps every capability named below to the tools in
your harness.

Derive a run slug from the target per the contract; every file this
run writes uses that slug.

This is an execution request, not a request to explain the workflow.
Begin with the plan artifact, not with prose about the protocol. The
one deliberate stop is the mode gate in step 3.

## Sources

Primary venues: arXiv (math.CT, cs.LO, math.LO, math.AT), nLab,
1lab, TypeTopology, author pages, and proof-assistant library
documentation. Before searching outward, consult what the
repository has already vetted or proven: `resources/` (vetted source
entries — when one covers the target source, cite it by entry and
extract from it first), `docs/gloss.md` (the theorem ledger),
`docs/roadmap.md` (standing targets), and the latest `notes/session-logs/`
entry (where work left off). Known prior context is a starting point, not something to
rediscover: a target already proven here is reported VERIFIED with
its module named, not re-mechanized.

## Workflow

1. **Extract** — Write `notes/plans/<slug>.md`: the target claims,
   key questions, a task ledger, a verification log, and a
   placeholder for the success criteria that step 2 will fix. Then
   pull from the source — with the paper-search and url-fetch
   capabilities, or from the covering `resources/` entry when one
   exists — the definitions, theorem statements, hypotheses, and
   proof strategy, into `notes/research/<slug>-extraction.md`.
   Label every extracted claim per the contract lexicon —
   CONJECTURED for everything harvested, `[unvetted]` for
   automated-search references until promoted. Mark every planned
   question `done`, `blocked`, or `superseded` — never silently
   skip one.

2. **Detail** — Build the per-claim ledger in
   `notes/research/<slug>-ledger.md`. For each mechanization target:
   its exact hypotheses as the source states them; its dependencies
   on the other targets; the prerequisite lemmas, each marked
   VERIFIED (already machine-checked here — name the module or Gloss
   certificate) or CONJECTURED (to be proven); the intended proof
   method; and its module placement. Dispatch the `analyzer`
   agent for placement, dependency, and duplication analysis when
   present; `just stats` and the file-search capability over
   import lines give live inventories.
   Consult the `analyzer` agent for proof strategy whenever
   a target involves h-levels or truncation, equivalence
   constructions, coherence or naturality, transport or substitution
   chains, fiber arguments, or univalence — routine proofs need no
   consultation. Require explicit type annotations on every
   intermediate goal in any sketch the consultation produces.
   Implementation gates on a spike for every load-bearing
   CONJECTURED claim. Close this step by fixing the success criteria
   in the plan artifact — for each target, the exact check that
   decides it (typically `just check <Mod>` at zero warnings; exit
   42 is failure) — before any execution mode is chosen.

3. **Gate** — Stop. Ask via the user-question capability which
   execution mode to run, and execute nothing before the choice:
   - **Plan-only** — deliver the ledger and plan; write no Agda.
   - **Spike** — exploratory Agda in
     `src/Test/<Name>-<timestamp>.lagda.md`; spikes need not
     typecheck cleanly and are never imported by All. The spike
     pins the open fork by typechecking that fork against the real
     foundation — never a mock; the surrounding exploration need
     not typecheck cleanly, but the fork's typecheck is the
     verdict, prose is not. Dispatch it with an oracle-shaped
     contract: a verdict in {DERIVED, STUCK, PARTIAL}, which route
     closed, and the exact goal-verbatim residue if stuck.
   - **Full module** — a real library module: `just new <Mod>`,
     `just sync --fix`, zero-warnings typecheck, lint, reviewer
     pass.
   When the user-question capability is blocked, ask in plain chat
   and wait; never default to an execution mode.

4. **Execute** — per the chosen mode. Implementation is delegated to
   the `coder` agent with a self-contained brief built
   from the ledger (hypotheses, prerequisite lemmas with modules,
   annotated sketch, target file); when that agent is absent, work
   lead-owned and record the delegation as degraded. Constraints in
   both executing modes: `--safe --erased-cubical
   --no-guardedness`, no postulates, no external libraries, never
   truncate homs; the run never commits. Two consecutive failures on
   the same goal is a full stop: record what is known, what was
   tried, and what is missing in the plan ledger, and return to the
   user for direction. Preserve every failed proof attempt's text
   in the plan ledger, then revert — never stack fixes on a
   broken approach. On a genuine two-strikes wall, keep the
   timestamped `src/Test/` spike (do not delete it) with
   `-- STUCK:` comments — the verbatim goal type at the hole plus
   what was tried — record the salvage (the reusable machinery and
   what the wall points at) under a "do not re-derive; build on"
   heading, revert the real modules, and invent no auxiliary
   axioms. In full-module mode, each definitional reduction the
   proof leans on is re-asserted beside it as a present-tense
   `killcheck-<name> = refl`, so a reduction that stops firing
   fails `just check`; a dead route is banked as a WALL
   transcribing its refl-probe goal. After the success criteria
   pass, run `just lint` and `just check <Mod>` on every touched
   module, and dispatch the
   `reviewer` agent (lead-owned degraded when absent).
   Append to the plan ledger `notes/plans/<slug>.md` after
   meaningful progress, after failed attempts, and before stopping:
   active objective, what changed, what was checked, next step. The
   ledger is append-only and the resumability mechanism — on
   resume, read its tail first. (`notes/session-logs/` belongs
   exclusively to the session-close log.)

5. **Verify** — Run an adversarial pass over the draft report:
   status labels stronger than their evidence (a target is
   mechanized only if its pre-registered check actually passed —
   never on "should typecheck"), extraction claims the source does
   not state, hypotheses silently strengthened or dropped between
   ledger and implementation, single-source critical claims, novelty
   language without a recorded search, and sections surviving from
   earlier drafts that the final evidence no longer supports. Grade
   findings FATAL / MAJOR / MINOR. Fix FATAL findings before
   delivery and run one more pass after the fixes; note MAJOR
   findings in Open Questions; accept MINOR.

6. **Report** — Save the final report to `notes/research/<slug>.md`:
   each target's outcome against its pre-registered success
   criterion (VERIFIED with module named, or CONJECTURED with what
   remains), the spike or module paths produced, failures logged,
   the source references for each target (paper URL or DOI, or the
   covering `resources/` entry, plus any formalization-repository
   URLs consulted), and Open Questions. Propose `docs/gloss.md`
   candidate entries in the provenance sidecar — 📐 (rigorous
   argument, not mechanized)
   or ⚠️ (partially conjectured), upgraded only by machine-checking,
   never entered unilaterally: in every mode, ledger entries are
   proposals in the report and sidecar, applied at commit time on
   the user's word, with statuses honest to what was checked. Write
   the sidecar per the contract, adding the mechanize-specific
   field: the chosen execution mode. Verify on disk that the report
   and sidecar exist before stopping; never stop at an intermediate
   draft.

## Scope

This run writes `notes/plans/` and `notes/research/` always;
`src/Test/` in spike mode; `src/` beyond `src/Test/` only in
full-module mode; and nothing else. Spikes,
ledger entries, and `resources/` entries outside the chosen mode are
proposals recorded in artifacts, never executed as a side effect.

## Honesty rules (binding)

Epistemic labels, `[unvetted]` handling, and novelty language
follow the contract lexicon. Mechanize-specific rules:

- A target is called mechanized only when its pre-registered check
  passed in this repository; VERIFIED then names the module or
  Gloss certificate, and a target that merely "should typecheck"
  stays CONJECTURED.
- Blocked capabilities and failed checks are reported BLOCKED in
  the sidecar with the manual command a human could run; a missing
  check is never smoothed over, and a capability is never
  simulated.
