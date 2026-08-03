---
description: Run a literature review on a mathematical topic, author, lab, or mechanization corpus using primary-source synthesis.
argument-hint: <topic-or-author-or-corpus>
disable-model-invocation: true
---

Investigate the following topic, author, or corpus as a literature review: $ARGUMENTS

Derive a slug per euler.md §File naming. Use this slug for all files in this
run.

## Workflow

1. **Plan** — Outline the scope: key questions, source types to search
   (papers, textbooks, lecture notes, mechanization libraries), time period,
   expected sections, and a small task ledger plus verification log. When the
   input appears to name an author, lab, institution, or existing
   mechanization corpus (a library, an archive, a group's repository), run the
   review as a **corpus review**: resolve the identity first, collect the
   reachable publication/development list, then map the trajectory across that
   corpus. Write the plan to `outputs/.plans/<slug>.md`. Continue after the plan
   per euler.md §Invocation semantics.
   - When updating the plan ledger later, keep edits small and valid. If an
     edit fails with a parse error or the replacement would require embedding
     a large markdown block, rewrite the full corrected plan file instead,
     then continue to final artifact/provenance verification.
2. **Gather** — Use the `researcher` subagent when the sweep is wide enough to
   benefit from delegated triage before synthesis. For narrow topics, search
   directly. Researcher outputs go to `outputs/.drafts/<slug>-research-*.md`.
   For corpus reviews, the lead agent owns identity resolution and writes
   `outputs/.drafts/<slug>-research-corpus.md` with reachable titles, years,
   venues (or library modules), URLs/DOIs, and gaps before delegating
   trajectory synthesis.
   Prefer author pages, arXiv/OpenReview/Semantic Scholar pages, library
   indices and READMEs, and search results that expose stable source anchors.
   Do not silently skip assigned questions; mark them `done`, `blocked`, or
   `superseded`.
3. **Synthesize** — Separate consensus, disagreements, and open questions.
   Flag non-equivalent formulations of "the same" result across sources
   (different hypotheses, constructive vs. classical, weakened conclusions) —
   do not merge them silently. For corpus reviews, also identify 3-5 research
   trajectories and the 3-5 works that most changed the corpus's direction;
   rank them by contrastive originality, methodology strength, and
   relationship to prior art rather than by prestige alone. When useful,
   propose concrete next formalization targets or follow-up reading. Use
   Mermaid diagrams for taxonomies, concept dependencies, or trajectory maps
   when the structure is source-supported and changes the reader's research
   decision. Generate charts only when a chart tool is visible and the data
   is source-backed; otherwise include a chart specification or comparison
   table. Write the synthesis draft to
   `outputs/.drafts/<slug>-report-draft.md`. Keep the output to research
   evidence, source coverage, and next
   research decisions; do not create non-research operational artifacts from a
   literature review run.
4. **Cite** — Spawn the `verifier` agent to add inline citations to
   `outputs/.drafts/<slug>-report-draft.md` and verify
   every anchor (URLs resolve, theorem/page anchors support the quoted
   statements, `file:line` references show the quoted declarations), writing
   the cited draft to `outputs/.drafts/<slug>-verified.md`. For
   narrow lead-owned reviews, do this pass yourself.
5. **Verify** — Spawn the `reviewer` agent to check the cited draft at
   `outputs/.drafts/<slug>-verified.md` for
   unsupported claims, logical gaps, zombie sections, non-equivalent
   formulations treated as identical, and single-source critical findings. Fix
   FATAL issues before delivering. Note MAJOR issues in Open Questions. If
   FATAL issues were found, run one more verification pass after the fixes.
   Reviewer output goes to `outputs/.drafts/<slug>-review.md`.
6. **Deliver** — Save the final literature review to `outputs/<slug>.md`.
   Write a provenance record alongside it as `outputs/<slug>.provenance.md`
   listing: date, sources consulted vs. accepted vs. rejected, verification
   status, and intermediate research files used; for corpus reviews, include
   the corpus-log path and unresolved corpus gaps. Before you stop, verify on
   disk that both files exist; do not stop at an intermediate cited draft
   alone.
