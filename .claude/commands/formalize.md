---
description: Formalize an informal theorem, paper, or chapter into the proof library — plan the informal→formal mapping, discharge obligations against the kernel, verify, and review.
argument-hint: <target>
disable-model-invocation: true
---

Formalize the following target into the proof library: $ARGUMENTS

This is an execution request (euler.md §Invocation semantics). Your first
actions should be tool calls that resolve the toolchain block, create
directories, and write the plan artifact.

Derive a slug per euler.md §File naming.

## Required Artifacts

Every run must leave these files on disk:

- `outputs/.plans/<slug>.md`
- `outputs/.drafts/<slug>-research-*.md` (source extraction, library survey)
- `outputs/.drafts/<slug>-report-draft.md`
- `outputs/.drafts/<slug>-verified.md`
- `outputs/.drafts/<slug>-review.md`
- `outputs/<slug>.md`
- `outputs/<slug>.provenance.md`

Plus the formalized code itself, committed to the library tree per the
toolchain block's `lib-layout`.

After the user approves the plan, if any capability fails, continue in
degraded mode and still write a blocked or partial final output and provenance
sidecar. Never end with chat-only output after plan approval. Use
`Verification: BLOCKED` when verification could not be completed.

## Step 0: Resolve the toolchain block

Resolve the toolchain block per euler.md §Toolchain contract before anything
else.

- If found, adopt its `check`, `check-file`, `sorry-token`, `unsafe-markers`,
  `lib-layout`, and `search-dirs` verbatim. Never weaken the check command's
  flags. If the block defines `probe`, run it now as the environment sanity
  check and record the outcome.
- If absent, record the resolved answers in `outputs/.plans/<slug>.md` as the
  toolchain block for this run. Do not proceed without them.
- If the check command cannot execute (missing binary, broken environment),
  record `Toolchain: BLOCKED` and continue in plan/statements-only mode: you
  may draft definitions and statements, but every mechanical claim is
  `BLOCKED` and Step 4 reduces to drafting code without any verification
  claims.

Log the resolved block once: `[toolchain] check='...' sorry='...' lib=...`

## Step 1: Plan

Create `outputs/.plans/<slug>.md` immediately. The plan must include:

- **Target** — the informal artifact: paper/textbook/chapter/theorem, with
  checkable anchors (title, section/theorem numbers, pages, URL).
- **Key questions** — what exactly is being formalized, in what generality,
  and what is explicitly out of scope.
- **Informal→formal mapping table** — one row per informal item: informal
  name + anchor, kind (definition / lemma / theorem / corollary), target
  declaration name, target module, status (`exists` with `file:line` /
  `missing` / `to-prove` / `done` with `file:line`). This table is the spine
  of the run; keep it current as work proceeds.
- **Dependency inventory** — prerequisites the library must provide; each
  marked `located` (with `file:line`) or `missing` after the library survey.
- **Encoding decisions** — representation choices and their fidelity risks.
- **Delivery criteria** — what "done" means for this run: e.g. zero open
  obligations in delivered files, or zero in stated theorems with scaffolding
  obligations enumerated and labeled.
- **Scale decision** — direct work vs. subagent split (decided in Step 2,
  recorded here before the task ledger assigns owners).
- **Task ledger, verification log, decision log.**

After writing the plan, stop and ask for explicit confirmation before
gathering evidence or writing code. Summarize the plan briefly and ask via
AskUserQuestion whether to proceed with the formalization plan or change it
first.

Do not run searches, spawn subagents, write library code, verify, or deliver
until the user confirms. If the user requests changes, update the plan first,
then ask again. Statement translation is the highest-risk step of any
formalization — the mapping table deserves this gate.

## Step 2: Scale

Decide the scale now and record it in the plan's scale-decision field before
the task ledger assigns owners. Call count alone is not the test (euler.md
§Delegation rules) — a single lemma read from a short, self-contained
source stays lead-owned; the same lemma read from a long paper or spread
across many declarations does not, regardless of call count.

Use lead-owned direct work when the source and library survey will stay
small and bounded in your own context — typically a single lemma or
definition, or a short self-contained chain.

Use subagents when decomposition clearly helps, an independent read of
the source is worth more than its cost, or the source/survey would
otherwise bloat your own context:

- One section or a cluster of related lemmas: 1-2 `researcher` subagents
  (source extraction, library survey).
- A full paper or chapter: 2-4 `researcher` subagents partitioned by
  source region and library subsystem.

Do not inflate a single-theorem target into a multi-agent survey when
none of these apply.

## Step 3: Gather

If direct work was chosen:

- Read the informal source yourself; extract definitions, statements, proof
  sketches, and side conditions with anchors into
  `outputs/.drafts/<slug>-research-source.md`.
- Survey the library yourself for the dependency inventory.

If subagents were chosen:

- Write a per-researcher brief first, such as `outputs/.plans/<slug>-T1.md`.
- Keep subagent call payloads small; put multi-paragraph instructions in the
  on-disk brief, not in the call.
- Dispatch researchers in parallel: one message, one Agent call per
  researcher, each with `subagent_type: "researcher"`. A failed researcher
  does not abort the others; record the failure and continue.
- Typical split: one researcher extracts the informal content (statements,
  proofs, side conditions, anchors) into
  `outputs/.drafts/<slug>-research-source.md`; another surveys the library
  (existing declarations with `file:line`, conventions, gaps) into
  `outputs/.drafts/<slug>-research-library.md`.

After gathering, update the plan's mapping table and dependency inventory:
every prerequisite is now `located` or `missing`. Missing prerequisites become
explicit lemmas to prove (added to the mapping table) or scope changes
(recorded in the decision log).

## Step 4: Formalize

Work through the mapping table in dependency order. All code lands in the
library tree per `lib-layout`.

The loop, per obligation:

1. **Edit** — write or revise the definition/statement/proof.
2. **Check** — run `check-file` (or `check`) exactly as the toolchain block
   specifies, via shell. Record the command and outcome in the plan's
   verification log.
3. **Decide** — keep, revise, or revert. Record failed approaches in the
   decision log with the reason (wrong induction principle, needed
   generalization, missing lemma, encoding mismatch). The failed-strategy
   journal is a deliverable, not noise.
4. **Update** — mark the mapping-table row and the obligation count.

Rules of the loop:

- Scaffolding obligations (sorry tokens) are allowed mid-run but every one
  must appear in the plan's obligation inventory. An untracked hole is a
  process failure.
- Never claim a file or proof checks without a recorded run in the
  verification log.
- Keep iterations small enough that `check-file` stays fast; prefer per-file
  checks during the loop and a full `check` at milestones.
- Respect the host library's conventions — consult the toolchain block's
  `style-guide` field (law + exemplar) if present, alongside whatever the
  library survey found; if `style-guide` is absent, rely on the survey
  alone.
- If the user chose an isolated environment (branch, worktree, container),
  all edits and check runs happen there.

## Step 5: Draft the report

Write the report yourself. Do not delegate synthesis — the lead owns the
account of what was formalized and what the checker established. (The
`writer` subagent exists for standalone write-up workflows, not for this
report.)

Save to `outputs/.drafts/<slug>-report-draft.md`.

Include:

- Summary of what was formalized, with the informal anchors.
- The informal→formal mapping table, updated to truth.
- Encoding decisions and fidelity notes.
- The obligation inventory as of now, with locations.
- The failed-strategy journal from the decision log.
- Open questions and known limitations.

Before verification, sweep the draft:

- Every critical claim — a statement's content, an obligation count, a build
  outcome — must map to a source anchor, a `file:line`, or a recorded checker
  run in the verification log.
- Remove or downgrade unsupported claims.
- Mark inferences as inferences.

## Step 6: Verify

Mandatory before any reviewer run (euler.md §Delegation rules).

If the run was lead-owned and small, you may perform the verifier pass
yourself; otherwise dispatch the `verifier` agent (Agent call,
`subagent_type: "verifier"`) with this prompt:

> Verify `outputs/.drafts/<slug>-report-draft.md` against the research files
> and the library. Source layer: anchor every informal claim. Kernel layer:
> run the toolchain block's check command, audit obligation and unsafe
> markers in the delivered files, and transcription-check every quoted
> statement. Write the complete verified report to
> `outputs/.drafts/<slug>-verified.md`.

Whether done directly or delegated, the verification pass must include:

- A full `check` run (or per-file `check-file` runs covering every delivered
  file), recorded with exact commands and outcomes.
- An obligation audit: grep of every delivered file for the toolchain block's
  `sorry-token` list; the final inventory written into the report.
- An unsafe-marker audit: grep for `unsafe-markers`; every hit disclosed.
- A transcription check: every statement quoted in the report matches the
  declaration on disk.
- Source-layer anchoring of all informal claims.

After the verifier returns, verify on disk that
`outputs/.drafts/<slug>-verified.md` exists. If the verifier wrote elsewhere,
find the file and move or copy it to that path.

## Step 7: Review

If the run was lead-owned and small, review the verified report yourself:
write `outputs/.drafts/<slug>-review.md` with FATAL / MAJOR / MINOR findings
and the checks performed, fix FATAL issues, and skip the reviewer dispatch.

Otherwise, only after `outputs/.drafts/<slug>-verified.md` exists, run the
`reviewer` agent (Agent call, `subagent_type: "reviewer"`) against the
verified report plus the delivered code, with this prompt:

> Review the formalization described in `outputs/.drafts/<slug>-verified.md`
> and delivered in the library files it lists. Prioritize statement fidelity
> against the informal source, definition gaming, smuggled hypotheses, and
> undisclosed obligations. This is a verification pass, not a style review.
> Write the review to `outputs/.drafts/<slug>-review.md`.

Severity guidance: any open obligation contradicting a completeness claim, any
non-equivalence between formal and informal statements, any definition gaming,
or any undisclosed axiom/unsafe marker is FATAL.

If the reviewer flags FATAL issues, fix them before delivery and run one more
review pass. Note MAJOR issues in the report's Open Questions. Accept MINOR
issues.

When applying reviewer fixes, do not issue one giant edit with many
replacements. Use small localized edits for 1-3 simple corrections; for more
than 3 substantive fixes, write the corrected report in full to
`outputs/.drafts/<slug>-revised.md`. Code fixes must be re-checked with
`check-file` after editing.

After applying fixes, run an explicit on-disk verification before saying they
landed: targeted `rg`/`grep`/`diff`/`wc` or reads proving the old wording is
gone and the replacement exists, plus a fresh check run when code changed. If
a write or edit fails, do not describe the fix as applied; record the failure,
retry, and verify again. Provenance may only claim an issue was fixed when
this post-fix verification passed.

The final candidate is `outputs/.drafts/<slug>-revised.md` if it exists;
otherwise `outputs/.drafts/<slug>-verified.md`.

## Step 8: Deliver

Copy the final candidate to `outputs/<slug>.md`. The report must include:

- Summary of what was formalized, with the informal anchors.
- The final informal→formal mapping table (from the plan, updated to truth).
- Encoding decisions and fidelity notes.
- The obligation inventory: `none`, or an enumerated list with locations and
  justification.
- The verification record: every checker run (exact command, outcome, date).
- Open questions and known limitations.

Write provenance next to it as `outputs/<slug>.provenance.md`, using the
shape in `.claude/rules/provenance-template.md`'s formalization-extra-fields
section.

Before responding, verify on disk that all required artifacts exist and that
any fixes claimed in the provenance are reflected in the final candidate
(`rg`/`grep` for removed and replacement wording). Do not claim "all checks
pass" or "fixed" unless these commands succeed.

Final response should be brief: link the report, the provenance file, the
delivered library files, and any blocked checks.
