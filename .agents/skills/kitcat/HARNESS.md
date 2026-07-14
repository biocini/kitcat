# HARNESS.md — capability rosetta for kitcat workflow skills

Read this file once per session before executing any skill in this
tree. Skill bodies name **capabilities**, never harness tools; this
file maps each capability to the literal tool in the harness you
are running in. The consuming harnesses are exactly two: **Claude
Code** and **pi**. The feynman harness does not consume this
repository, and its `alpha` CLI is not relied on for anything here:
`feynman alpha search` is broken (returns `fetch failed`, verified
2026-07-12), so paper acquisition uses direct arXiv fetch instead
(see the paper-search row). There is no `.feynman/` surface.

Mechanics below were audited against the live builds: Claude Code
(this machine) and pi 0.80.2 with @gotgenes/pi-subagents 18.0.1
(audited 2026-07-11). When either build changes, re-audit this
file; claims about unaudited versions are CONJECTURED.

Ground rules:

- Tool names are literal. Call only tools visible in your current
  tool set.
- Never retry an invalid tool call. Remap to a visible tool with
  valid arguments, or record the capability as blocked.
- A capability with no visible tool is BLOCKED: write
  `<capability>: BLOCKED — no visible tool` in the run artifact,
  state the manual command a human could run instead, and continue
  in degraded mode. Never simulate a capability or claim its result.
- The run artifact is the executing skill's plan file
  (`notes/plans/<YYYY-MM-DD>-<slug>.md`) unless the skill names another recording
  location; a skill with no plan file records in its chat report or
  working file. Skills that produce a provenance sidecar surface
  the run artifact's BLOCKED notes and degraded delegations there
  at delivery.
- **Output handoff is dual-channel** under Claude Code, and under
  any harness that returns a subagent's final message to the lead
  as the dispatch result: both channels operate and complement
  each other, never exclude. The **deliverable** — the findings
  report, evidence file, or other artifact — is still written to
  disk at the dispatch-named path per the file-based handoff
  (`.agents/CLAUDE.md`, Delegation); the returned message never
  replaces it. That returned final message **is** the contract's
  short completion report: a summary — status or findings-by-grade
  plus the artifact's path — not the artifact. Every dispatch
  produces both — write the file **and** return the completion
  report. "The parent reads my message, not the file I write" is
  the misread this closes: the message is the summary channel, the
  on-disk artifact is the deliverable, and neither substitutes for
  the other.
- Never overwrite a final artifact produced by a different run:
  when the target path already exists, confirm via the
  user-question capability or choose a distinct slug.

## Capability map

| Capability | Claude Code | pi |
| --- | --- | --- |
| web-search | `WebSearch` | `web_search` (also `perplexity_search`) |
| url-fetch | `WebFetch` | `web_fetch`, `batch_web_fetch` (also `read_web_page`, `curl_md`) |
| paper-search | web-search + url-fetch against arxiv.org, ncatlab.org, 1lab.dev; direct arXiv fetch by id via shell — `curl https://arxiv.org/e-print/<id>` (canonical LaTeX-source tarball) + `/abs/<id>` (metadata) | same as Claude Code |
| subagent-dispatch | `Agent` (one agent per call; parallelize with several calls in one message) | `subagent`, `get_subagent_result`, `steer_subagent` |
| user-question | `AskUserQuestion` | plain chat: ask and wait for the next user message (no question tool is installed) |
| file-read/write/edit | `Read` / `Write` / `Edit` | `read` / `write` / `edit` |
| shell | `Bash` | `bash` |
| file-search | `Grep` / `Glob`; `rg` / `fd` via shell | `ffgrep` / `fffind`; `rg` / `fd` via shell (core `grep`/`find` exist but are not in the default active tool set) |
| background-process | `Bash` with `run_in_background` | `process` |
| scheduling | a scheduling tool when visible | a scheduling tool when visible |
| session-recovery | `rg` over `~/.claude/projects/<munged-cwd, e.g. -Users-lane-kitcat>/*.jsonl` | `session_search`, `session_list`, `session_read` |
| doc-preview | `just html` for library docs; `Artifact` when visible; `pandoc` via shell | `preview_export`; else `pandoc` via shell |
| persistence | repo files (`notes/plans/`, `notes/research/`) | repo files |

Subagent dispatch schemas differ across harnesses and versions.
Before dispatching, read the visible tool's schema and conform to
it; never copy a call shape from a document, including this one.

Named agents (the kitcat roster: `analyzer`, `coder`, `reviewer`,
`researcher`, `verifier`, `ingest`, `writer`, `suite-maintainer`,
`process-reviewer`):
Claude Code loads them via the
`.claude/agents/` symlinks; pi loads them via the `.pi/agents/`
symlinks — both bridges are load-bearing. When a skill delegates
to a named agent that is absent in your harness, do the work
lead-owned and record the delegation as degraded in the run
artifact (or the location the skill names).

Trust: pi loads this tree's skills and the `.agents/prompts/`
masters only for trusted project directories (persistent store
`~/.pi/agent/trust.json` — this repository is granted — or
`--approve` per run); agent definitions load regardless of trust.
Two invocation routes exist under pi: the `/name` prompt substitutes
`$ARGUMENTS`; the auto-registered `/skill:<name>` form appends
arguments after the body without substitution — the prompt is the
canonical route.

## Authoring rules for this tree

The surface topology — masters under `.agents/`, the shim/prompt
split, and the per-harness symlinks — is stated in `.agents/CLAUDE.md`
("Workflow surface topology"); this section is the mechanical how-to.

- A workflow is **two master files**: the **prompt**
  `.agents/prompts/<name>.md` (the full body) and the **skill shim**
  `.agents/skills/kitcat/<name>/SKILL.md` (the auto-trigger stub).
  `<name>` is kebab-case and identical for both; the shim's
  frontmatter `name` equals it.
- **Prompt bodies use capability nouns** from the table above. This
  file is the only place harness tool names appear; a harness tool
  name in a prompt body is a defect.
- **Prompt bodies NAME cross-agent conventions and defer to
  `.agents/CLAUDE.md`** — that file is the only place the slug rule,
  the epistemic lexicon, the provenance-sidecar contents, and
  degraded-delegation handling are stated (the convention analog of
  the tool rule above). Open every prompt body with "Read
  `.agents/CLAUDE.md` and HARNESS.md first", then reference each
  convention by name ("derive a run slug per the contract", "label
  per the contract lexicon"). A slug/lexicon/sidecar spec appearing
  verbatim in a prompt body is an authoring defect a human confirms;
  a prompt states inline only the genuinely workflow-specific
  (deep-research's required artifact paths, mechanize's per-claim
  ledger, audit's per-axis dimensions).
- **The skill shim is small and mandatory.** Frontmatter is `name` +
  `description`; `description:` is required (the harness matches it to
  auto-invoke, and a skill without it does not load under pi). The
  body is a one-liner routing to `/<name>` — it carries no
  conventions and no capability nouns. (`spike-echo`, the discovery
  diagnostic, is the one whose prompt orchestrates nothing.)
- **The only argument placeholder is `$ARGUMENTS`.** No other dollar
  token may appear anywhere in a prompt body, including inside code
  examples: pi substitutes positional tokens across the entire body.
  (Mechanically only `$N`, `$@`, `$ARGUMENTS`, `${N:-…}`, and
  `${@:N…}` rewrite; the blanket rule is kept as margin.)
- **Prompt frontmatter carries both harness command-sets:**
  `argument-hint` (Claude Code autocomplete) and `args` / `section` /
  `topLevelCli` (pi prompt adapters); each set is inert in the other
  harness.
- **Adding a workflow** = write the two masters. The harness surfaces
  are directory symlinks already in place
  (`.claude/commands` → `.agents/prompts`,
  `.claude/skills` → `.agents/skills/kitcat`); there is no per-skill
  symlink to add, and pi reads the masters directly. Then run
  `just lint authoring` and `spike-echo`.
- The `spike-echo` skill is the discovery diagnostic: invoke it with
  arguments after any harness or tree change and expect
  `SPIKE-ECHO OK ARGS=[<the arguments>]`.
