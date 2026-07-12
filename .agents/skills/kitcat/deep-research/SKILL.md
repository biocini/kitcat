---
name: deep-research
description: Run a deep, source-heavy research investigation on a mathematical question in type theory, category theory, univalent mathematics, or programming language foundations. Use when asked for deep research, a comprehensive analysis, an in-depth report, a multi-source investigation, or the state of a question (e.g. directed univalence, duploid semantics). Produces a cited research brief in notes/research/ with a provenance sidecar, after an explicit plan-confirmation gate.
argument-hint: <question-or-topic>
args: <question-or-topic>
section: Research Workflows
topLevelCli: true
---

# Deep Research

Run deep research for: $ARGUMENTS

Read `.agents/CLAUDE.md` and `.agents/skills/kitcat/HARNESS.md`
first: the contract binds the cross-agent conventions this skill
defers to; HARNESS maps every capability named below to the tools
in your harness.

Derive a run slug from the topic per the contract.

This is an execution request, not a request to explain the workflow.
Begin with the plan artifact, not with prose about the protocol.

## Required artifacts

After the plan is approved, every run must leave these files on
disk, even in degraded or blocked mode:

- `notes/plans/<slug>.md` — the plan (also the run artifact; the
  plan file itself is the persistence of the plan)
- `notes/research/<slug>-draft.md`
- `notes/research/<slug>-cited.md`
- `notes/research/<slug>.md` — the final brief
- `notes/research/<slug>.provenance.md`

If a capability fails after plan approval, continue in degraded
mode and still write a blocked or partial final brief and its
sidecar, with `Verification: BLOCKED` when verification could not
run. Never end chat-only after plan approval.

A deep-research run writes only under `notes/` — no spikes, no
`docs/` or `src/` edits. Next steps for the repository
(mechanization spikes, `docs/gloss.md` entries, `resources/`
entries worth vetting) are proposals recorded in the brief and
sidecar, never executed as a side effect.

## Sources

Primary venues for this repository's domain: arXiv (math.CT, cs.LO,
math.LO, math.AT), nLab, 1lab, TypeTopology, author and lab pages,
and proof-assistant library documentation (Agda, cubical, mathlib).
Before searching outward, consult what the repository has already
vetted or proven: `resources/` (vetted source entries — cite these
by entry when they cover a source) and `docs/gloss.md` (the theorem
ledger). Known prior context is a starting point, not something to
rediscover.

Prefer paper metadata, abstracts, HTML pages, and official docs.
Do not fetch PDFs in this workflow: when only a PDF exists, cite
its URL from search metadata and mark full-text extraction as
blocked — deep PDF extraction is the `eli5` skill's tiered
machinery; run that skill separately when a source demands it.

## Workflow

1. **Plan** — Write `notes/plans/<slug>.md`: key questions,
   evidence needed, the scale decision, a task ledger, a
   verification log, and a decision log. Record the scale decision
   (see step 2 for the criteria) before assigning owners. Then
   stop: summarize the plan briefly and ask, with the user-question
   capability, whether to proceed. Gather nothing — no searches, no
   fetches, no dispatches, no drafting, no citing, no delivery —
   until the user confirms. If the user
   requests changes, update the plan file first, then ask again.
   Keep later ledger edits small; if an edit fails or would embed a
   large block, rewrite the full plan file instead, then continue
   through to final artifact and provenance verification.
2. **Scale** — Direct search handles a single fact, a narrow
   question, or any "what is X" explainer: answerable in roughly
   3–10 tool calls, no dispatches. Never inflate an explainer into
   a multi-agent survey; dispatch only when the user explicitly
   asks for comprehensive coverage or the topic genuinely
   decomposes. When it does, dispatch the `researcher`
   agent with the subagent-dispatch capability: 2 for a direct
   comparison of 2–3 formulations or programs, 3–4 for a broad
   survey, 4–6 for a complex multi-domain sweep. When that agent is
   absent in your harness, gather lead-owned and record the
   delegation as degraded.
3. **Gather** — Direct mode: search yourself with the paper-search,
   web-search, and url-fetch capabilities, using at least three
   distinct query angles (definition/history, precise statement or
   construction, current status and formalizations) before
   drafting; record the exact search terms and notes in
   `notes/research/<slug>-research-direct.md`. Dispatch mode: write
   a self-contained brief per researcher
   (`notes/plans/<slug>-T1.md`, `-T2.md`, …), keep each dispatch
   payload small and pointed at its brief file, and collect
   evidence notes in `notes/research/<slug>-research-*.md`, never
   inline. Brief the researchers in capability terms, not tool
   names; a researcher whose fetch fails continues from metadata
   and abstracts and marks the source blocked. After gathering,
   update the plan's ledger and verification log; mark every
   planned question `done`, `blocked`, or `superseded` — never
   silently skip one. If gathering failed, record exactly what
   failed and proceed with a blocked or partial draft.
4. **Draft** — Write the brief yourself; synthesis is never
   delegated. Save `notes/research/<slug>-draft.md` with an
   executive summary, findings organized by question, consensus vs
   disagreements, evidence-backed caveats, and open questions. No
   invented sources, results, figures, or tables. Before citing,
   sweep the draft: every critical claim maps to a source URL,
   research note, or `resources/` entry; remove or downgrade
   unsupported claims; mark inferences as inferences.
5. **Cite** — Rewrite the draft to `notes/research/<slug>-cited.md`
   with inline citations and a Sources section, and check every
   source with the url-fetch capability: the URL resolves, and the
   document states what it is cited for. Label every claim per the
   contract lexicon (`docs/provenance.md` binding).
6. **Verify** — Run an adversarial pass over the cited draft:
   unsupported claims, logical gaps, single-source critical claims,
   overstated confidence, status labels stronger than their
   evidence, novelty language without a recorded search, and
   sections surviving from earlier drafts that the final evidence
   no longer supports. Dispatch the `verifier` agent when
   present — it re-checks the citations and runs this adversarial
   pass; otherwise self-review. Record findings in
   `notes/research/<slug>-verification.md`, graded FATAL / MAJOR /
   MINOR. Fix FATAL findings before delivery and run one more pass
   after the fixes; note MAJOR findings in Open Questions; accept
   MINOR. Apply 1–3 simple corrections as small localized edits;
   for section rewrites or more than 3 substantive fixes, write a
   corrected full file to `notes/research/<slug>-revised.md`
   instead. Prove every applied fix on disk with the file-search or
   shell capability — the old wording gone, the replacement
   present — before recording it as fixed; a failed edit is
   recorded as a failure, retried smaller or as a full rewrite,
   and verified again.
7. **Deliver** — Copy the final candidate (`-revised.md` if it
   exists, else `-cited.md`) to `notes/research/<slug>.md` and
   write its provenance sidecar
   `notes/research/<slug>.provenance.md` per the contract. Verify
   on disk that all required artifacts exist before stopping; never
   stop at an intermediate draft. The final response is brief: the
   final file, the sidecar, and any blocked checks.

## Honesty rules (binding)

- No reference supports a claim unless the cited document was opened
  and says what it is cited for; and a reference surfaced by
  automated search remains `[unvetted]` — supporting no load-bearing
  claim — until a human or a `resources/` entry confirms it.
- Novelty language is "we are not aware of prior work", accompanied
  by the searches actually performed — never "new" or "first".
- Blocked capabilities and failed checks are reported as BLOCKED in
  the provenance sidecar; a missing check is never smoothed over.
- Provenance may say an issue was fixed only after the post-edit
  on-disk verification passed.
