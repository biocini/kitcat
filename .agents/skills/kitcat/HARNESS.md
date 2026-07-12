# HARNESS.md — capability rosetta for kitcat workflow skills

Read this file once per session before executing any skill in this
tree. Skill bodies name **capabilities**, never harness tools; this
file maps each capability to the literal tool in the harness you are
running in. Identify your harness by the tools visible to you.

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
  (`notes/plans/<slug>.md`) unless the skill names another recording
  location; a skill with no plan file records in its chat report or
  working file. Skills that produce a provenance sidecar surface
  the run artifact's BLOCKED notes and degraded delegations there
  at delivery.
- Never overwrite a final artifact produced by a different run:
  when the target path already exists, confirm via the
  user-question capability or choose a distinct slug.

## Capability map

| Capability | Claude Code | Pi (feynman) | Pi (upstream) |
| --- | --- | --- | --- |
| web-search | `WebSearch` | `web_search` | `web_search` (also `perplexity_search`) |
| url-fetch | `WebFetch` | `fetch_content` | `web_fetch`, `batch_web_fetch` (also `read_web_page`, `curl_md`) |
| paper-search | web-search + url-fetch against arxiv.org, ncatlab.org, 1lab.dev; or `feynman alpha ...` via shell when installed (`command -v feynman`) | `alpha_search`, `alpha_get_paper`, `alpha_ask_paper` when visible; else `feynman alpha ...` via shell | `feynman alpha ...` via shell when installed; else web-search + url-fetch |
| subagent-dispatch | `Agent` (one agent per call; parallelize with several calls in one message) | `subagent` | `subagent`, `get_subagent_result`, `steer_subagent` |
| user-question | `AskUserQuestion` | `ask_user_question` when visible; else ask in plain chat and wait | `ask_user_question` when visible; else ask in plain chat and wait |
| file-read/write/edit | `Read` / `Write` / `Edit` | `read` / `write` / `edit` | `read` / `write` / `edit` |
| shell | `Bash` | `bash` | `bash` |
| file-search | `Grep` / `Glob`; `rg` / `fd` via shell | `grep` / `find` when visible; `rg` / `fd` via shell | `ffgrep` / `fffind`; `rg` / `fd` via shell |
| background-process | `Bash` with `run_in_background` | `process` when visible | `process` |
| scheduling | a scheduling tool when visible | `schedule_prompt` when visible | a scheduling tool when visible |
| session-recovery | `rg` over `~/.claude/projects/<munged-cwd, e.g. -Users-lane-kitcat>/*.jsonl` | `/search` when visible; else `rg` over `~/.feynman/sessions/` | `session_search`, `session_list`, `session_read` |
| doc-preview | `just html` for library docs; `Artifact` when visible; `pandoc` via shell | `/preview` family when visible; else `pandoc` via shell | `preview_export`; else `pandoc` via shell |
| persistence | repo files (`notes/plans/`, `notes/research/`) | repo files; `memory_remember` additionally when visible | repo files |

Subagent dispatch schemas differ across harnesses and versions.
Before dispatching, read the visible tool's schema and conform to
it; never copy a call shape from a document, including this one.

Named agents (the kitcat roster: `cubical-agda-coder`,
`cubical-agda-reviewer`, `cubical-analyzer`, `hott-theoretician`,
`researcher`, `verifier`) are registered
per-harness, and availability varies by harness. When a skill
delegates to a named agent that is absent in your harness, do the
work lead-owned and record the delegation as degraded in the run
artifact (or the location the skill names).

Pi discovers this tree and the agent registry only after project
trust is granted: run once with `--approve` (or accept the
interactive trust prompt) in the repository.

## Authoring rules for this tree

- Skill bodies use capability nouns from the table above. This file
  is the only place harness tool names appear.
- `description:` frontmatter is mandatory — a skill without it does
  not load under Pi.
- The only argument placeholder is `$ARGUMENTS`. No other dollar
  token may appear anywhere in a skill body, including inside code
  examples: Pi substitutes positional tokens across the entire body.
- Frontmatter carries both harness sets: `argument-hint` (Claude
  Code autocomplete) and `args` / `section` / `topLevelCli` (feynman
  CLI); each set is inert in the other harness.
- Skill names are kebab-case and equal to their directory name.
- Claude Code discovers this tree through per-skill symlinks; when
  adding a skill, also add its symlink:
  `ln -s ../../.agents/skills/kitcat/<name> .claude/skills/<name>`
- Pi's typed slash form comes from prompt-adapter symlinks; add
  both alongside:
  `ln -s ../../.agents/skills/kitcat/<name>/SKILL.md .pi/prompts/<name>.md`
  and the same into `.feynman/prompts/<name>.md`.
- The `spike-echo` skill is the discovery diagnostic: invoke it with
  arguments after any harness or tree change and expect
  `SPIKE-ECHO OK ARGS=[<the arguments>]`.
