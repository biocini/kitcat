---
name: compare
description: Build a source-comparison matrix over papers, pages, or formalizations that treat the same concept in type theory, category theory, univalent mathematics, or programming language foundations. Use when asked to compare definitional variants, competing formulations of the same categorical structure, formalization approaches, or claims across sources — the natural kitcat use is comparing definitional variants across the literature before mechanizing one. Produces a matrix (source, key claim or definitional choice, evidence type in proof-status vocabulary, caveats, confidence) in notes/research/ with a provenance sidecar.
argument-hint: <topic-or-formulation>
args: <topic>
section: Research Workflows
topLevelCli: true
---

# Source Comparison

Compare sources for: $ARGUMENTS

Read `.agents/CLAUDE.md` and `.agents/skills/kitcat/HARNESS.md`
first: the contract binds the cross-agent conventions this skill
defers to; HARNESS maps every capability named below to the tools
in your harness.

Derive a run slug from the comparison topic per the contract.

This is an execution request, not a request to explain the workflow.
Begin with the plan artifact, not with prose about the protocol.

A comparison run writes only `notes/plans/` and `notes/research/` —
no spikes, no `docs/` or `src/` edits. Mechanization
recommendations, `docs/gloss.md` entries, and candidate
`resources/` entries are proposals, recorded in the artifact and
sidecar — never executed as a side effect.

## Sources

Primary venues for this repository's domain: arXiv (math.CT, cs.LO,
math.LO, math.AT), nLab, 1lab, TypeTopology, author and lab pages,
and proof-assistant library documentation (Agda, cubical, mathlib).
Before searching outward, consult what the repository has already
vetted or settled: `resources/` (vetted source entries — cite these
by entry when they cover a source) and `docs/gloss.md` (the theorem
ledger). Name formulations consistently across the matrix — never
compare under drifting names.
When this repository's own formalization is one of the compared
sources, cite the module or Gloss certificate directly; that row is
the only place VERIFIED evidence can appear.

## Workflow

1. **Plan** — Write `notes/plans/<slug>.md`: the sources to
   compare, the comparison dimensions, the expected output
   structure, a task ledger, and a verification log. Summarize the
   plan briefly to the user and continue immediately; ask for
   confirmation only if the user explicitly requested plan review.
   Keep later ledger edits small; if an edit fails or would embed a
   large block, rewrite the full plan file instead, then continue
   through to final artifact and provenance verification.
2. **Gather** — When the comparison set is broad enough to benefit
   from delegated triage, dispatch the `researcher` agent
   with a self-contained brief; its evidence notes go to
   `notes/research/<slug>-research-*.md`, never inline. When that
   agent is absent in your harness, gather lead-owned and record
   the delegation as degraded. For a narrow, named set of sources,
   fetch them directly with the paper-search, web-search, and
   url-fetch capabilities. Prefer sources with stable URLs or DOIs.
   Mark every planned source and dimension `done`, `blocked`, or
   `superseded` — never silently skip one.
3. **Build the matrix** — Write the comparison yourself; synthesis
   is never delegated. One row per source, columns: source; key
   claim or definitional choice; evidence type; caveats;
   confidence. The evidence-type column uses this repository's
   proof-status vocabulary: ✅ machine-checked and committed / 🧪
   machine-checked evidence in `Gloss.*` / 📐 rigorous argument,
   not mechanized / ⚠️ partially conjectured — plus SOURCE-CHECKED
   marking what the opened document itself states. ✅/🧪 apply only
   to claims machine-checked in this repository (name the module or
   Gloss certificate); a mechanization living elsewhere is recorded
   as `mechanized elsewhere, SOURCE-CHECKED against <ref>`, never
   as VERIFIED. After the matrix, separate agreement, disagreement,
   and uncertainty into explicit sections — a definitional choice
   the sources genuinely diverge on is a finding, not a footnote.
   Include diagrams or supplementary tables only when
   source-supported and decision-changing; prefer a plain table
   when a diagram cannot be rendered. Where useful, propose
   concrete next steps for this repository: which variant to
   mechanize and why, spike candidates, results to pursue toward
   `docs/gloss.md` entries, `resources/` entries worth vetting —
   proposals only.
4. **Cite** — Add inline citations and check every source with the
   url-fetch capability: the URL resolves, and the document states
   what it is cited for. Label every claim per the contract lexicon
   (`docs/provenance.md` binding); an `[unvetted]` reference
   supports no matrix row's evidence-type label until it is
   confirmed.
5. **Verify** — Run an adversarial pass over the cited draft: rows
   whose evidence-type label is stronger than the opened source
   supports, disagreements flattened into false consensus,
   single-source claims presented as settled, caveats or confidence
   ratings without recorded grounds, status labels stronger than
   their evidence, and sections surviving from earlier drafts that
   the final evidence no longer supports. Dispatch the
   `verifier` agent when present — it re-checks the
   citations and runs this adversarial pass; otherwise self-review
   and record the delegation as degraded. Grade findings FATAL /
   MAJOR / MINOR. Fix FATAL findings before
   delivery and run one more pass after the fixes; note MAJOR
   findings in Open Questions; accept MINOR.
6. **Deliver** — Save exactly one comparison to
   `notes/research/<slug>-comparison.md`, ending with a Sources
   section giving a direct URL or DOI for every source used, and
   write its provenance sidecar
   `notes/research/<slug>-comparison.provenance.md` per the
   contract. Verify on disk that both files exist before stopping;
   never stop at an intermediate draft.

## Honesty rules (binding)

- No matrix row carries a claim unless the cited document was
  opened and says what it is cited for; and a reference surfaced by
  automated search remains `[unvetted]` — supporting no
  load-bearing claim — until a human or a `resources/` entry
  confirms it.
- Evidence-type labels never exceed their evidence: ✅/🧪 name a
  module or Gloss certificate in this repository, or they do not
  appear.
- Novelty language is "we are not aware of prior work", accompanied
  by the searches actually performed — never "new" or "first".
- Blocked capabilities and failed checks are reported as BLOCKED in
  the provenance sidecar; a missing check is never smoothed over.
