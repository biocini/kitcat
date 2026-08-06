# Euler

The contract for the euler workflows — autoformalization and
mathematics/PL research work in a proof assistant library. The workflow
bodies live in `.claude/commands/`, their trigger skills in
`.claude/skills/`, and the bundled subagents in `.claude/agents/`.

Subagent behavior does **not** live here. The source of truth for the
bundled subagents is `.claude/agents/`. If you need to change how
`researcher`, `writer`, `verifier`, or `reviewer` behave, edit the
corresponding file there instead of duplicating those prompts here.

## Subagents

Euler ships four bundled research subagents:

- `researcher`
- `writer`
- `verifier`
- `reviewer`

They are defined in `.claude/agents/` and dispatched via the Agent tool
with `subagent_type` set to the agent's name; parallel dispatch is one
message with multiple Agent calls. The `writer` is dispatched by
`/draft` (paper-style write-ups). The deep-research and formalization
pipelines keep synthesis with the lead and do not delegate it.

## What belongs here

Keep this file focused on cross-agent project conventions:

- output locations and file naming expectations
- the toolchain block contract (how agents talk to the proof checker)
- workspace-level continuity expectations for long-running work
- provenance and verification requirements
- handoff rules between the lead agent and subagents

Do **not** restate per-agent prompt text here unless there is a
project-wide constraint that applies to all agents.

A policy or convention states its rule exactly once, in the file that
owns it. Every other file that needs it cites that file rather than
restating the rule — this applies to command bodies, agent prompts, and
skill files alike, not only to this one.

Suite files contain **operational rules only** — instructions that shape
the behavior of the agent executing a workflow at runtime. They never
contain development history: no renames, no alternatives considered, no
redirects, no references to what these files replaced or were derived
from, no narration of how the suite was built. History lives in version
control. When editing these files, state the rule; do not narrate the
change.

## Feature scope

Euler must stay simple yet potent. It is an autoformalization and
mathematics/PL research assistant, not a bundle of adjacent productivity
workflows.

Every new feature must fight for its life before implementation. Keep or
add a feature only when it directly improves at least one core
formalization job:

- discovering prior art: informal sources, existing mechanizations in
  any proof assistant, or relevant material already in the host library
- reading, extracting, and understanding informal mathematics (papers,
  textbooks, lecture notes, problem statements)
- mapping informal definitions and theorems to formal statements
- discharging proof obligations against the kernel
- verifying formalizations: kernel checks, obligation/axiom audits,
  statement fidelity against informal sources
- synthesizing formalization work into auditable artifacts
- improving speed, observability, provenance, or reliability of the
  formalization loop

Reject adjacent product lanes by default. Funding, proposal, admin,
generic writing, and project-management workflows do not belong in Euler
unless the user explicitly scopes them as support for a specific active
formalization run.

Before adding a command, prompt, tool, extension, or document page,
state the core formalization job it serves and the smallest existing
surface that can absorb it. If the value is not concrete and testable,
do not add it.

## Invocation semantics

- A command invocation is an execution request, not a request to
  describe the workflow. Run it; do not narrate what it would do
  instead of doing it.
- After presenting a plan, continue immediately by default. Summarize
  the plan briefly, then proceed. Wait for explicit review only when
  the user asked for it, or when the workflow itself states a hard
  gate (`/deepresearch` and `/formalize` gate on toolchain-block
  resolution and scope confirmation before spending a research or
  formalization budget).

## Toolchain contract

- Workflows are proof-assistant-agnostic. They must never invent a build
  or check command, a sorry token, or a library layout.
- The host project provides these facts in a **toolchain block**: a
  `.euler/TOOLCHAIN.md` file or a `## Toolchain` section in the
  project's `CLAUDE.md`. See `.claude/TOOLCHAIN.example.md` for the
  field contract.
- The check command is the only oracle of proof validity. Agent
  judgment, inspection, or plausibility never substitutes for a recorded
  checker run.
- If the toolchain block is missing, workflows ask the user for it
  before proceeding. If the checker itself cannot run, verification
  claims are recorded as `BLOCKED`, never softened into `verified`.

## Tool map

- Literature: WebSearch and WebFetch.
- Library search: shell (`rg`, `fd`) via Bash, or Grep/Glob, over the
  toolchain block's `search-dirs`.
- Proof checker: Bash runs of the toolchain block's commands. Never
  simulate, predict, or assume a check result; only a recorded run
  counts.
- Subagents: the Agent tool, `subagent_type` one of `researcher`,
  `writer`, `verifier`, `reviewer`.
- User gates: AskUserQuestion.
- Optional capabilities (scheduling via CronCreate or the `schedule`
  skill, background runs via TaskList/TaskOutput or background Bash,
  chart and preview renderers): use them when the session provides
  them, and record the capability as `BLOCKED` when it does not. Never
  claim background state that was not confirmed to exist.

## Writing standard

- Euler prose artifacts follow the `writing` skill: reports,
  briefs, plans, reviews, summaries, session logs, and `CHANGELOG.md`
  entries.
- STE-flavored is the default mode. Use strict mode for procedures,
  step lists, and error text.
- Before delivery, run the skill's self-lint. Then run the
  `writing` skill's bundled linter on the final artifact and record
  the score in the `.provenance.md` sidecar.

## Output conventions

- Formalized code lands in the library tree, placed per the toolchain
  block's `lib-layout` — never in `outputs/`.
- Research and formalization reports go in `outputs/`.
- Paper-style drafts (mechanization reports, write-ups) go in `papers/`.
- Session logs go in `notes/`.
- The workspace-level lab notebook lives at `CHANGELOG.md`.
- Plan artifacts for long-running workflows go in `outputs/.plans/`.
- Intermediate research artifacts are written to disk by subagents and
  read by the lead agent. They are not returned inline unless the user
  explicitly asks for them.
- Long-running workflows should treat the plan artifact as an
  externalized working memory, not a static outline. Keep task status,
  the informal→formal mapping table, and verification state there as the
  run evolves.
- Long-running or resumable workflows should also treat `CHANGELOG.md`
  as the chronological lab notebook: what changed, what checked, what
  failed, and what should happen next.
- Do not create or update `CHANGELOG.md` for trivial one-shot tasks.

## File naming

Every workflow that produces artifacts must derive a short **slug** from
the topic (lowercase, hyphens, no filler words, ≤5 words — e.g.
`girard-paradox`, `stlc-strong-normalization`). All files in a single
run use that slug as a prefix:

- Plan: `outputs/.plans/<slug>.md`
- Per-task briefs: `outputs/.plans/<slug>-T<N>.md`
- Intermediate research: `outputs/.drafts/<slug>-research-*.md`
- Draft report: `outputs/.drafts/<slug>-report-draft.md`
- Verified draft: `outputs/.drafts/<slug>-verified.md`
- Post-review revision: `outputs/.drafts/<slug>-revised.md`
- Review: `outputs/.drafts/<slug>-review.md`
- Final output: `outputs/<slug>.md` (or `papers/<slug>.md` for
  paper-style drafts)
- Provenance: `<slug>.provenance.md` (next to the final output)

Auxiliary workflows may suffix the slug with the workflow name for their
primary artifacts — e.g. `outputs/<slug>-audit.md`,
`outputs/<slug>-audit.provenance.md`, `outputs/<slug>-recipe.md`,
`outputs/.plans/<slug>-recipe.md`, and watch baselines
`outputs/<slug>-baseline.md`.

Three exceptions, all deliberate:

- **Loop state:** `/prove` keeps its session files at fixed paths —
  `outputs/.prove/prove.md`, `prove.jsonl`, `prove.sh` — one active loop
  per project. Concurrent loops run in separate worktrees.
- **Subagent defaults:** the default output names in the
  `.claude/agents/` output contracts are fallbacks; dispatching agents
  always pass a slugged output path.
- **Scratch space:** windowed-reading workflows (`/summarize`) keep
  bulky raw text and chunk intermediates under
  `outputs/.notes/<slug>-*`.

Never use generic names like `research.md`, `draft.md`, `plan.md`, or
`summary.md` for workflow artifacts. Concurrent runs must not collide.

## Status labels

Euler uses status labels at two levels; keep the casing distinct:

- **Claim level** (lowercase): `verified`, `unverified`, `blocked`,
  `inferred` — attached to individual claims, prerequisites, and checks.
- **Run level** (uppercase): `PASS`, `PASS WITH NOTES`, `BLOCKED` — the
  overall verdict in provenance sidecars and verification records.

## Workspace changelog

- `CHANGELOG.md` is a lab notebook, not release notes.
- Read `CHANGELOG.md` before resuming substantial work when it exists.
- Append concise entries after meaningful progress, failed proof
  strategies, major verification results, or new blockers.
- Each entry should identify the active slug or objective and end with
  the next recommended step.
- Mark verification state honestly with the claim-level labels
  (`verified`, `unverified`, `blocked`, `inferred`) only when they match
  the underlying evidence.

## Provenance and verification

Euler verification has two layers, and both are required before
delivery:

1. **Source layer** — every informal mathematical claim anchors to a
   checkable location: paper/textbook with section, theorem number, or
   page, or a URL. Every formal claim about the library anchors to
   `file:line`.
2. **Kernel layer** — every claim that a proof checks, a module builds,
   or an obligation is closed anchors to a recorded run of the project's
   check command (exact command, outcome, date).

- Every output from `/formalize`, `/deepresearch`, `/lit`, `/audit`, and
  `/recipe` must include a `.provenance.md` sidecar, in the shape given
  by `.euler/provenance-template.md`. Workflows use that shape
  and do not restate it.
- Provenance sidecars record source accounting, the checker runs
  performed, and the final obligation (sorry) inventory.
- If the toolchain block exposes a documentation-coverage check, its
  output is mandatory sidecar evidence, on the same footing as the
  obligation count. Absent such a field, nothing is required.
- Point-of-use citation (the credit sitting at the exact construction
  it justifies) is a verifier-stage check, not an assumption. Confirm
  the host project's own citation convention rather than assuming one.
- Source verification, transcription checks, and obligation audits
  belong in the `verifier` stage, not in ad hoc edits after delivery.
- Verification passes happen before delivery when the workflow calls for
  them.
- If a workflow uses the words `verified`, `proved`, `checks`, or
  `complete`, the underlying artifact records the checker run or source
  inspection that actually established it.
- Keep raw artifact paths: checker logs, grep output for obligation
  counts, scripts. Do not rely on polished summaries alone.
- Never smooth over missing checks. Mark work as `blocked`,
  `unverified`, or `inferred` when that is the honest status.
- A sorry/hole/admit is an obligation, not a detail. Open obligations
  are always enumerated, never buried.

## Delegation rules

- The lead agent plans, delegates, formalizes or synthesizes, and
  delivers.
- Use subagents for three distinct reasons, not one: work that is
  meaningfully decomposable (independent source extraction, library
  survey, separate modules); an independent read worth more than its
  cost, since a subagent's blank-slate context yields conclusions less
  anchored to the lead's existing framing; and orchestrator context
  hygiene, since a subagent's tool output and search results accrue in
  its own disposable context and reach the lead only as a distilled
  summary, while the same work done lead-side accrues directly in the
  orchestrator's context and compounds across a long session. The
  quantity to optimize is results per unit of orchestrator-session
  context, not the call count of one task in isolation — a lead-owned
  lookup is cheap only when its results stay small in the orchestrator's
  own context, not merely because it takes few tool calls. Do not spawn
  a subagent for work that is genuinely trivial by all three measures.
- Prefer file-based handoffs over dumping large intermediate results
  back into parent context. Keep subagent call payloads small; write
  briefs to disk.
- The lead agent is responsible for reconciling task completion.
  Subagents may not silently skip assigned tasks; skipped or merged
  tasks must be recorded in the plan artifact.
- The verifier and reviewer stages are strictly ordered: verifier first,
  then reviewer. Never run them in the same parallel dispatch.
- For critical claims — a flagship theorem statement, a claim of
  completeness — require at least one adversarial verification pass
  after synthesis. Fix fatal issues before delivery or surface them
  explicitly.
