---
description: Run a thorough, source-heavy investigation on a mathematics/PL topic and produce a durable research brief with precise anchors and inline citations.
argument-hint: <topic>
disable-model-invocation: true
---

Run deep research for: $ARGUMENTS

This is an execution request, not a request to explain or implement the
workflow instructions. Execute the workflow. Do not answer by describing the
protocol, do not explain these instructions, and do not restate the protocol.
Your first actions should be tool calls that create directories and write the
plan artifact.

## Required Artifacts

Derive a short slug from the topic: lowercase, hyphenated, no filler words, at
most 5 words.

Every run must leave these files on disk:

- `outputs/.plans/<slug>.md`
- `outputs/.drafts/<slug>-report-draft.md`
- `outputs/.drafts/<slug>-verified.md`
- `outputs/.drafts/<slug>-review.md`
- `outputs/<slug>.md` (or `papers/<slug>.md` for paper-style drafts)
- `<slug>.provenance.md` (next to the final output)

After the user approves the plan, if any capability fails, continue in
degraded mode and still write a blocked or partial final output and provenance
sidecar. Never end with chat-only output after plan approval. Never end with
only an explanation in chat after plan approval. Use `Verification: BLOCKED`
when verification could not be completed.

## Step 1: Plan

Create `outputs/.plans/<slug>.md` immediately. The plan must include:

- Key questions
- Evidence needed
- Scale decision
- Task ledger
- Verification log
- Decision log

Make the scale decision before assigning owners in the plan. If the topic is a
narrow "what is X" explainer, the plan must use lead-owned direct search tasks
only; do not allocate researcher subagents in the task ledger.

After writing the plan, stop and ask for explicit confirmation before
gathering evidence. Summarize the plan briefly and ask via AskUserQuestion
whether to proceed with the deep research plan or change it first.

Do not run searches, fetch sources, spawn subagents, draft, cite, review, or
deliver final artifacts until the user confirms. If the user requests changes,
update `outputs/.plans/<slug>.md` first, then ask for confirmation again.

## Step 2: Scale

Use direct search for:

- Single fact or narrow question, including "what is X" explainers
- Work you can answer with 3-10 tool calls

For "what is X" explainer topics, you MUST NOT spawn researcher subagents
unless the user explicitly asks for comprehensive coverage, current landscape,
or mechanization status across assistants. Do not inflate a simple explainer
into a multi-agent survey.

Use subagents only when decomposition clearly helps:

- Direct comparison of 2-3 items (definitions, encodings, mechanizations): 2
  `researcher` subagents
- Broad survey or multi-faceted topic: 3-4 `researcher` subagents
- Complex multi-domain research (e.g. spanning type theory, category theory,
  and a mechanization corpus): 4-6 `researcher` subagents

## Step 3: Gather Evidence

Anchor discipline for this domain: every claim from an informal source needs
its precise location (theorem/lemma/definition number and page, or section);
every claim about a mechanization needs its file path (and line, when
available) or URL. Prior mechanizations — in any proof assistant — are
first-class sources, not afterthoughts.

Avoid crash-prone PDF parsing in this workflow. Do not fetch `.pdf` URLs
unless the user explicitly asks for PDF extraction. Prefer paper metadata,
abstracts, HTML pages (arXiv HTML, journal pages, library docs), and web
snippets. If only a PDF exists, cite the PDF URL from search metadata and mark
full-text PDF parsing as blocked instead of fetching it.

If direct search was chosen:

- Skip researcher spawning entirely.
- Search and fetch sources yourself.
- Use multiple search terms/angles before drafting. Minimum: 3 distinct
  queries for direct-mode research, covering definition/history,
  mechanism/construction, and current usage/mechanization status when
  relevant.
- Record the exact search terms used in
  `outputs/.drafts/<slug>-research-direct.md`.
- Write notes to `outputs/.drafts/<slug>-research-direct.md`.
- Continue to synthesis.

If subagents were chosen:

- Write a per-researcher brief first, such as `outputs/.plans/<slug>-T1.md`.
- Keep subagent call payloads small; put multi-paragraph instructions in the
  on-disk brief, not in the call.
- Dispatch the researchers in parallel: one message, one Agent call per
  researcher, each with `subagent_type: "researcher"`. A failed researcher
  does not abort the others; record the failure and continue.
- Prefer broad guidance such as "use paper search and web search"; if a paper
  fetch fails, the researcher must continue from metadata, abstracts, and web
  sources and mark full-text parsing as blocked.

Example prompts:

- "Read `outputs/.plans/<slug>-T1.md` and write
  `outputs/.drafts/<slug>-research-literature.md`."
- "Read `outputs/.plans/<slug>-T2.md` and write
  `outputs/.drafts/<slug>-research-mechanizations.md`."

After evidence gathering, update the plan ledger and verification log. If
research failed, record exactly what failed and proceed with a blocked or
partial draft.

## Step 4: Draft

Write the report yourself. Do not delegate synthesis. (The `writer` subagent
serves standalone write-up workflows, not this report.)

Save to `outputs/.drafts/<slug>-report-draft.md`.

Include:

- Executive summary
- Findings organized by question/theme
- Evidence-backed caveats and disagreements (including conflicting
  definitions or non-equivalent formulations across sources — flag them
  explicitly; in this field, "the same theorem" often differs in hypotheses
  across texts)
- Open questions
- No invented sources, results, theorems, or mechanizations

Before citation, sweep the draft:

- Every critical claim, theorem statement, or construction must map to a
  source anchor or research note.
- Remove or downgrade unsupported claims.
- Mark inferences as inferences.

## Step 5: Cite

If direct search/no researcher subagents was chosen:

- Do citation yourself.
- Verify reachable HTML/doc URLs with available fetch/search tools.
- Copy or rewrite `outputs/.drafts/<slug>-report-draft.md` to
  `outputs/.drafts/<slug>-verified.md` with inline citations and a Sources
  section.
- Do not spawn the `verifier` subagent for simple direct-search runs.

If researcher subagents were used, run the `verifier` agent after the draft
exists. This step is mandatory and must complete before any reviewer runs. Do
not run the `verifier` and `reviewer` in the same parallel dispatch.

Dispatch it as an Agent call with `subagent_type: "verifier"` and this prompt:

> Add inline citations to `outputs/.drafts/<slug>-report-draft.md` using the
> research files as source material. Verify every anchor: URLs resolve,
> theorem/page anchors support the quoted statements, file:line references
> show the quoted declarations. Write the complete cited brief to
> `outputs/.drafts/<slug>-verified.md`.

After the verifier returns, verify on disk that
`outputs/.drafts/<slug>-verified.md` exists. If the verifier wrote elsewhere,
find the cited file and move or copy it to
`outputs/.drafts/<slug>-verified.md`.

## Step 6: Review

If direct search/no researcher subagents was chosen:

- Review the verified draft yourself.
- Write `outputs/.drafts/<slug>-review.md` with FATAL / MAJOR / MINOR findings
  and the checks performed.
- Fix FATAL issues before delivery.
- Do not spawn the `reviewer` subagent for simple direct-search runs.

If researcher subagents were used, only after
`outputs/.drafts/<slug>-verified.md` exists, run the `reviewer` agent against
it.

Dispatch it as an Agent call with `subagent_type: "reviewer"` and this prompt:

> Verify `outputs/.drafts/<slug>-verified.md`. Flag unsupported claims,
> logical gaps, single-source critical claims, non-equivalent formulations
> treated as identical, and overstated confidence. This is a verification
> pass, not a peer review. Write the review to
> `outputs/.drafts/<slug>-review.md`.

If the reviewer flags FATAL issues, fix them before delivery and run one more
review pass. Note MAJOR issues in Open Questions. Accept MINOR issues.

When applying reviewer fixes, do not issue one giant edit with many
replacements. Use small localized edits only for 1-3 simple corrections. For
section rewrites or more than 3 substantive fixes, read the verified draft and
write a corrected full file to `outputs/.drafts/<slug>-revised.md` instead.

After applying fixes, run an explicit on-disk verification before saying the
fixes landed. Use `rg`, `grep`, `diff`, `wc`, or a targeted read to prove the
old unsupported wording is gone and the replacement wording exists. If an edit
or write fails, do not describe the fix as applied; record the failure in the
plan/provenance, retry with a smaller edit or a full corrected file, and
verify again. Provenance may only say an issue was fixed when this post-edit
verification passed.

The final candidate is `outputs/.drafts/<slug>-revised.md` if it exists;
otherwise it is `outputs/.drafts/<slug>-verified.md`.

## Step 7: Deliver

Copy the final candidate to `outputs/<slug>.md`, or to
`papers/<slug>.md` for paper-style drafts.

Write provenance next to the final output as `<slug>.provenance.md`:

```markdown
# Provenance: [topic]

- **Date:** [date]
- **Rounds:** [number of research rounds]
- **Sources consulted:** [count and/or list]
- **Sources accepted:** [count and/or list]
- **Sources rejected:** [dead, unverifiable, or removed]
- **Verification:** [PASS / PASS WITH NOTES / BLOCKED]
- **Plan:** outputs/.plans/<slug>.md
- **Research files:** [files used]
```

Before responding, verify on disk that all required artifacts exist. If
verification could not be completed, set `Verification: BLOCKED` or
`PASS WITH NOTES` and list the missing checks.

Before responding, also verify that any fixes claimed in the provenance are
reflected in the final candidate (`rg`/`grep` for removed and replacement
wording). Do not claim "all patches applied", "all checks pass", or "fixed"
unless these commands or reads succeed.

Final response should be brief: link the final file, provenance file, and any
blocked checks.
