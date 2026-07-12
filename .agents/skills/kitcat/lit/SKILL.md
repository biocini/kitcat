---
name: lit
description: Run a literature review on a topic, author, or research program in type theory, category theory, univalent mathematics, or programming language foundations. Use when asked for a lit review, paper survey, state of the art, academic landscape, survey of formalizations, or who-has-worked-on-X. Produces a cited review in notes/research/ with a provenance sidecar.
argument-hint: <topic-or-author>
args: <topic-or-author>
section: Research Workflows
topLevelCli: true
---

# Literature Review

Run a literature review for: $ARGUMENTS

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness.

Derive a short slug from the topic (lowercase, hyphens, no filler
words, at most 5 words). Every file this run writes uses that slug.

This is an execution request, not a request to explain the workflow.
Begin with the plan artifact, not with prose about the protocol.

## Sources

Primary venues for this repository's domain: arXiv (math.CT, cs.LO,
math.LO, math.AT), nLab, 1lab, TypeTopology, author and lab pages,
and proof-assistant library documentation (Agda, cubical, mathlib).
Before searching outward, consult what the repository has already
vetted or proven: `resources/` (vetted source entries — cite these
by entry when they cover a source) and `docs/gloss.md` (the theorem
ledger). Known prior context is a starting point, not something to
rediscover.

## Workflow

1. **Plan** — Write `notes/plans/<slug>.md`: key questions, source
   types to search, time period, expected sections, a task ledger,
   and a verification log. When the input names an author, lab, or
   research program, run the review as a publication-corpus review:
   resolve the identity first, collect the reachable publication
   list into `notes/research/<slug>-publications.md` (titles, years,
   venues, URLs/DOIs, and gaps), then map the research trajectory
   across that corpus. Summarize the plan briefly to the user and
   continue immediately; ask for confirmation only if the user
   explicitly requested plan review. Keep later ledger edits small;
   if an edit fails or would embed a large block, rewrite the full
   plan file instead, then continue through to final artifact and
   provenance verification.
2. **Gather** — For a sweep wide enough to benefit from delegated
   triage, dispatch the `researcher` agent with a
   self-contained brief; its evidence notes go to
   `notes/research/<slug>-research-*.md`, never inline. When that
   agent is absent in your harness, gather lead-owned and record the
   delegation as degraded. For narrow topics, search directly with
   the paper-search, web-search, and url-fetch capabilities, using
   at least three distinct query angles before drafting. Prefer sources with stable
   URLs or DOIs. Mark every planned question `done`, `blocked`, or
   `superseded` — never silently skip one.
3. **Synthesize** — Write the review yourself; synthesis is never
   delegated. Separate consensus, disagreements, and open questions.
   For publication-corpus reviews, identify 3–5 research
   trajectories and the 3–5 papers that most changed the corpus
   direction, ranked by contrastive originality, methodological
   strength, and relationship to prior art rather than author
   prestige. Where useful, propose concrete next steps for this
   repository: mechanization spikes, formulation comparisons,
   results to pursue toward `docs/gloss.md` entries, `resources/`
   entries worth vetting. Next steps are proposals only: a review
   run writes nothing outside `notes/` — no spikes, no `docs/` or
   `src/` edits. Include diagrams or comparison tables only when
   source-supported and decision-changing.
4. **Cite** — Add inline citations and check every source with the
   url-fetch capability: the URL resolves, and the document states
   what it is cited for — record that as SOURCE-CHECKED. Epistemic
   labels are strict: VERIFIED applies only to claims machine-checked
   in this repository (name the module or Gloss certificate); every
   mathematical claim harvested from literature is CONJECTURED,
   typically written `CONJECTURED, SOURCE-CHECKED against <ref>`.
   References surfaced by automated search are `[unvetted]` and
   never support a load-bearing claim; a reference sheds
   `[unvetted]` only when a human confirms the opened document or a
   `resources/` entry covers it — record each promotion (who, or
   which entry) in the sidecar.
5. **Verify** — Run an adversarial pass over the cited draft:
   unsupported claims, logical gaps, single-source critical claims,
   overstated confidence, status labels stronger than their
   evidence, novelty language without a recorded search, and
   sections surviving from earlier drafts that the final evidence no
   longer supports. Dispatch the `verifier` agent when
   present — it re-checks the citations and runs this adversarial
   pass; otherwise self-review. Grade findings FATAL / MAJOR /
   MINOR. Fix FATAL findings before delivery and run one more pass
   after the fixes; note MAJOR findings in Open Questions; accept
   MINOR.
6. **Deliver** — Save the final review to `notes/research/<slug>.md`
   and its provenance sidecar to
   `notes/research/<slug>.provenance.md` recording: date and who
   requested the review; sources consulted vs accepted vs rejected
   (with reasons), each accepted source with its vetting status
   (`[unvetted]` / SOURCE-CHECKED / `resources/` entry); the
   intermediate research files used, each with its producer (which
   agent, or lead-owned degraded); blocked capabilities and degraded
   delegations, each with what was done instead; verification
   status — PASS (clean final pass), PASS WITH NOTES (MAJOR findings
   remain in Open Questions), or BLOCKED (a required check could not
   run; name it); and — for corpus reviews — the publication log
   path and unresolved corpus gaps. Sources worth permanent vetting
   are proposed in the sidecar as candidate `resources/` entries,
   not created unilaterally. Verify on disk that both files exist
   before stopping; never stop at an intermediate draft.

## Honesty rules (binding)

- No reference supports a claim unless the cited document was opened
  and says what it is cited for; and a reference surfaced by
  automated search remains `[unvetted]` — supporting no load-bearing
  claim — until a human or a `resources/` entry confirms it.
- Novelty language is "we are not aware of prior work", accompanied
  by the searches actually performed — never "new" or "first".
- Blocked capabilities and failed checks are reported as BLOCKED in
  the provenance sidecar; a missing check is never smoothed over.
