---
name: formulation-survey
description: Survey and rank candidate formulations or proof strategies for a target concept or theorem by mechanization feasibility in this library. Use when asked to compare formulations, choose between definitions, pick a proof strategy, assess whether a result is mechanizable, or plan how to formalize a concept. Produces a ranked brief with a single recommendation, prerequisite inventory, and implementation plan in notes/research/ with a provenance sidecar.
argument-hint: <concept-or-theorem>
args: <concept-or-theorem>
section: Research Workflows
topLevelCli: true
---

# Formulation Survey

Run a formulation survey for: $ARGUMENTS

Read `.agents/CLAUDE.md` and `.agents/skills/kitcat/HARNESS.md`
first: the contract binds the cross-agent conventions this skill
defers to; HARNESS maps every capability named below to the tools
in your harness.

Derive a run slug from the target per the contract.

This is an execution request, not a request to explain the workflow.
Begin with the plan artifact, not with prose about the protocol.

A survey run writes only under `notes/` — no spikes, no `docs/` or
`src/` edits. Spikes and ledger entries are proposals recorded in
the artifacts, never executed as a side effect; a `resources/`
entry is likewise proposal-only for any source no load-bearing
claim rests on. The one carve-out is ingest-on-firsthand-need: a
citation the survey relies on that rests on an unvendored source
triggers the `ingest` dispatch, which vendors a directed
PROVISIONAL entry per the contract.

## Sources

Primary venues for this repository's domain: arXiv (math.CT, cs.LO,
math.LO, math.AT), nLab, 1lab, TypeTopology, author and lab pages,
and proof-assistant library documentation (Agda, cubical, mathlib).
Before searching outward, consult what the repository has already
vetted or proven: `resources/` (cite by entry when one covers a
source) and `docs/gloss.md` (the theorem ledger). A prior compare
run's matrix on this target — its final at the contract's slug
path under `notes/research/` — is a primary input when present:
adopt its rows rather than re-deriving them. Known prior
context is a starting point, not something to rediscover.

Every candidate is judged against this library's constraints:
`--safe --erased-cubical --no-guardedness`, zero warnings, no
postulates, no external library imports, and never truncate homs
(wild categories by design). A formulation that structurally
requires violating one of these is INCOMPATIBLE regardless of how
well-sourced it is.

## Workflow

1. **Plan** — Write `notes/plans/<YYYY-MM-DD>-<slug>.md`: the target stated
   precisely, why it is wanted, candidate source types, the
   feasibility constraints above, expected candidates, a task
   ledger, and a verification log. Summarize the plan briefly to
   the user and continue immediately; ask for confirmation only if
   the user explicitly requested plan review. Keep later ledger
   edits small; if an edit fails or would embed a large block,
   rewrite the full plan file instead, then continue through to
   final artifact and provenance verification.
2. **Gather** — For a sweep wide enough to benefit from delegated
   triage, dispatch the `researcher` agent with a
   self-contained brief; its evidence notes go to
   `notes/research/<YYYY-MM-DD>-<slug>-research-*.md`, never inline. When that
   agent is absent in your harness, gather lead-owned and record
   the delegation as degraded. For narrow targets, search directly
   with the paper-search, web-search, and url-fetch capabilities —
   at least three distinct query angles before drafting, preferring
   sources with stable URLs or DOIs. Mark every planned question
   `done`, `blocked`, or `superseded` — never silently skip one.
3. **Extract formulations** — A candidate earns its row because
   some source actually proves or mechanizes a result with it,
   never because it is easy to state; an expository definition with
   no theorem attached is background, not a candidate. Link each
   proved result to the exact formulation that produced it: the
   source, the definitional choices (universe placement, h-level
   assumptions, strict versus weak structure, data versus property,
   coherence tower depth), the proof strategy, and the
   prerequisites it assumes. A useful row is specific enough that a
   coder could start from it without reopening the paper.
4. **Prerequisite inventory** — Check every prerequisite lemma of
   each candidate against this repository with the file-search and
   shell capabilities (`just stats`, import-line searches,
   `docs/gloss.md`, the `Gloss.*` certificates). A prerequisite machine-checked here
   is VERIFIED — name the module or Gloss certificate; one asserted
   only in literature, or not directly located, stays CONJECTURED —
   never imply a lemma exists here without locating it. Dispatch
   the `analyzer` agent for the gap and placement analysis
   when present; otherwise do it lead-owned and record the
   delegation as degraded.
5. **Mechanization grounding** — Find existing mechanizations of
   each candidate elsewhere (1lab, TypeTopology, mathlib, the
   cubical library) with the url-fetch capability; record exact
   module paths and definition names, and confirm the cited module
   actually contains the cited construction — an unopened module is
   `[unvetted]`. These are reference patterns only: this library
   imports nothing external. Then assess each candidate's expected
   obstructions: coherence towers, h-level walls, universe issues,
   erasure compatibility under `--erased-cubical`, and wild-hom
   compatibility (any step that truncates homs is disqualifying).
   Consult the `analyzer` agent for non-trivial
   obstruction assessment when present — its claims stay
   CONJECTURED until machine-checked; when absent, assess the
   obstructions lead-owned and record the delegation as degraded.
6. **Synthesize** — Write the working draft to
   `notes/research/<YYYY-MM-DD>-<slug>-draft.md`, then promote a concise ranked
   brief to `notes/research/<YYYY-MM-DD>-<slug>.md`; synthesis is never
   delegated. Rank by mechanization feasibility in this library,
   not by source prestige or generality. Grade each candidate READY
   (all prerequisites VERIFIED here), SPIKE-GATED (CONJECTURED
   prerequisites remain; implementation gates on a spike),
   OBSTRUCTED (a named obstruction with no known route around it),
   or INCOMPATIBLE (violates a library constraint; name it).
   Include diagrams or comparison tables only when source-supported
   and decision-changing.
7. **Verify** — Check the top-ranked candidate's sources with the
   url-fetch capability: each URL resolves and the document states
   the formulation and result it is cited for — record that as
   SOURCE-CHECKED, and record each `[unvetted]` promotion (who, or
   which entry) in the sidecar. When a load-bearing claim rests on
   a source not yet vendored, ingest per the contract: dispatch the
   `ingest` agent for a directed PROVISIONAL entry (lead-owned
   degraded when absent); the claim bears load once the entry's
   statement audit is recorded, per the contract. Then run the verify protocol per the contract
   over the draft; the adversarial sweep for this workflow:
   unsupported claims, logical gaps, single-source
   critical claims, overstated confidence, feasibility verdicts or
   status labels stronger than their evidence, prerequisites
   claimed present without a named module, novelty language without
   a recorded search, and sections surviving from earlier drafts
   that the final evidence no longer supports.
8. **Deliver** — Save the final brief to `notes/research/<YYYY-MM-DD>-<slug>.md`
   and write its provenance sidecar
   `notes/research/<YYYY-MM-DD>-<slug>.provenance.md` per the contract. Verify
   on disk that both files exist before stopping; never stop at an
   intermediate draft.

## Required final shape

The final brief must include:

- **Recommendation:** the one formulation to mechanize first and
  why — grounded in the ranking, not asserted.
- **Ranked formulation table:** one row per candidate with source
  (and its vetting status), the exact definitional choices,
  prerequisite lemmas with the module where each exists here or an
  explicit gap marker, expected obstructions, existing
  mechanizations elsewhere (module paths; reference only), and the
  feasibility verdict.
- **Prerequisite inventory:** every lemma the recommended path
  needs, each VERIFIED with its module named or CONJECTURED with
  the spike that would discharge it.
- **Implementation plan:** the minimal path — a spike at
  `src/Test/<Name>-<timestamp>.lagda.md` discharging each
  CONJECTURED prerequisite, then the module (placement per the
  namespace conventions, created with `just new`). This plan is a
  proposal recorded in the brief; the survey run executes none of
  it. Execution belongs to the pipeline: run the recommendation
  through `/mechanize` (or `/prove` for a single lemma), which
  adopts this brief's prerequisite inventory.
- **Known gaps:** missing prerequisites, unassessed obstructions,
  sources that could not be checked, statements whose intended
  generality is unclear.
- **Sources:** URLs for every paper, library module, and doc page
  used.

## Honesty rules (binding)

- No reference supports a claim unless the cited document was
  opened and says what it is cited for; a reference surfaced by
  automated search remains `[unvetted]`, supporting no load-bearing
  claim, until it sheds per the contract's epistemic lexicon.
- Never claim a formulation mechanizes cleanly here unless the
  mechanization exists and is VERIFIED.
- Novelty language is "we are not aware of prior work", accompanied
  by the searches actually performed — never "new" or "first".
- Blocked capabilities and failed checks are reported as BLOCKED in
  the provenance sidecar with the manual command a human could run;
  a missing check is never smoothed over.
