# .agents/CLAUDE.md — the context-layer source of truth

This is the metacontextual source of truth for kitcat's agentic
context layer: the cross-agent conventions, the workflow surface
design, and the decisions that shaped the layer. Every agent,
workflow, prompt, and repo-specific role reads this file once per
session before executing; it is the authority they defer to.

**Two audiences, cleanly divided.** The *repo user* — a person
developing the Agda library — reads the root `CLAUDE.md` (build,
style, namespaces, hard rules, the mathematics) and does not need
the context-layer meta here unless they choose to read it; root
`CLAUDE.md` orients them and points here. The *agent / context
layer* reads THIS file for the conventions and design that commands,
prompts, and agents rely on. That is the division of labor: root
`CLAUDE.md` is the repo user's guide, `.agents/` is the agent-facing
source of truth.

Where the pieces live: harness mechanics (capability→tool mapping,
authoring rules) in `.agents/skills/kitcat/HARNESS.md`; per-agent
prompt text in `.agents/<name>.md` — edit those files rather than
restating them here; the working discipline (the practiced
principles and their exemplars) in `.agents/methodology.md`; honesty
and citation standards in `docs/provenance.md`, which is binding; the
design decisions in the last section below.

This file is the source of truth — the only place the cross-agent
conventions (output locations, the slug rule, the epistemic lexicon,
provenance-sidecar contents, delegation and degraded-delegation
handling, and ingestion) are stated with authority. Root `CLAUDE.md`
may summarize one for the repo user, but defers here. Every prompt
body, agent definition, and workflow NAMES a convention and defers
here ("derive a run slug per the contract", "write the sidecar per
the contract"), never restating its content; a slug/lexicon/sidecar
spec appearing verbatim in a prompt body (`.agents/prompts/`) or an
agent definition is an authoring defect a human confirms — exactly
as `HARNESS.md` is the sole home of tool names.

## Workflow surface topology

The workflow suite is authored once under `.agents/` — the masters
live here, and every harness reaches them from its own idiomatic
location, by native discovery or a symlink, never a per-harness
copy. The systems are parallel: each harness does the same thing
from a different path.

Two master layers, following the feynman-style shim/prompt split:

- **`.agents/prompts/<name>.md`** — the master **prompt**: the full
  workflow body, invoked as the typed `/<name>` command. This is
  where the work is written; capability nouns and `$ARGUMENTS` live
  here.
- **`.agents/skills/kitcat/<name>/SKILL.md`** — the master
  **skill**: a small auto-trigger shim (frontmatter `name` +
  `description`, a one-line body routing to `/<name>`). A harness
  matches the `description` to auto-invoke the workflow; the shim
  stays lightweight so the heavy body is never duplicated. This
  buys prompt/command ergonomics *and* automatic skill discovery
  from one source.

How each harness reaches the masters:

- **pi and every other `.agents`-native harness** read
  `.agents/prompts/` and `.agents/skills/` directly — no adapter
  files.
- **Claude Code** reads its own dirs, which are single directory
  symlinks to the masters: `.claude/commands` → `.agents/prompts`,
  `.claude/skills` → `.agents/skills/kitcat`.

Adding or renaming a workflow touches only the two masters; the
harness surfaces are symlinks and need no maintenance. The
authoring mechanics (frontmatter, the shim template, the
`$ARGUMENTS` rule) and the capability rosetta live in
`.agents/skills/kitcat/HARNESS.md`.

## Output locations

- `notes/plans/<slug>.md` — run plans and ledgers: **local working
  memory** (gitignored, not tracked), updated as the run evolves,
  never a static outline. Failed attempts are preserved here.
- `notes/research/` — research intermediates and finals: **local
  working memory** (gitignored), with `.provenance.md` sidecars
  beside finals.
- `notes/session-logs/<YYYY-MM-DD>-<slug>.md` — session logs,
  written only by the log workflow; append-only history. This and
  `CHANGELOG.md` are the tracked, durable session bridge; the
  working-memory notes above are local and are distilled into these
  and the canonical homes at session close.
- `notes/watches/` — literature-watch state.
- `resources/<slug>/` — vetted source entries
  (`resources/README.md` is the format authority).
- `CHANGELOG.md` — the lab notebook; dated entries newest-first,
  written by the log workflow. Not updated for trivial one-shot
  tasks.
- `src/Test/<Name>-<timestamp>.lagda.md` — Agda scratchpads
  (gitignored; nothing committed may reference them).

Intermediate artifacts are written to disk by subagents and read
by the lead; they are not returned inline.

## Slugs and file naming

Every workflow that produces artifacts derives a short slug from
its topic: lowercase, hyphens, no filler words, at most 5 words.
All files in one run use that slug:

- Plan: `notes/plans/<slug>.md`
- Evidence: `notes/research/<slug>-research-<angle>.md`
- Final: `notes/research/<slug>.md`
- Sidecar: `notes/research/<slug>.provenance.md`
- Watch state: `notes/watches/<slug>.md`

Never use generic names (`research.md`, `draft.md`, `notes.md`);
concurrent runs must not collide. Never overwrite a final artifact
produced by a different run: when the target path exists, confirm
via the user-question capability or choose a distinct slug.

## Epistemic labels

`docs/provenance.md` is binding. The lexicon: VERIFIED only for
claims machine-checked in this repository, naming the module or
`Gloss.*` certificate; SOURCE-CHECKED when the opened document
states the claim at the cited location; every mathematical claim
harvested from literature is CONJECTURED (typically `CONJECTURED,
SOURCE-CHECKED against <ref>`); references surfaced by automated
search are `[unvetted]` and support nothing load-bearing until a
human confirmation — Lane ratifying the source, recorded as a
*vetted* `resources/` entry — covers them (a PROVISIONAL entry does
not lift the bar); each promotion is recorded in the run's sidecar. Novelty language is
"we are not aware of prior work" plus the search performed.

A "verified" claim names the command or check that verified it, so
re-running is mechanical; when a later change in the same session
touches an input of a verified claim, the marker is void until the
check is re-run.

## Provenance sidecars

Finals from research workflows carry a `.provenance.md` sidecar
recording: date and requester; sources consulted vs accepted vs
rejected, with reasons and each accepted source's vetting status;
intermediate files used, each with its producer (which agent, or
lead-owned degraded); blocked capabilities and degraded
delegations, each with what was done instead; verification status
— PASS (clean final pass), PASS WITH NOTES (MAJOR findings remain
in Open Questions), or BLOCKED (a required check could not run;
name it); and candidate `resources/` entries proposed, never
created as a silent side effect (see Ingestion below).

## Delegation

- The lead plans, delegates, synthesizes, and delivers. Synthesis
  is never delegated.
- Dispatch subagents with complete, self-contained briefs naming
  the exact output path; do not spawn them for trivial or narrow
  work — scale the fleet to the task, and never delegate an
  explainer-scale question.
- File-based handoffs: subagents write evidence to disk and reply
  with a short completion report; the lead reads the file, never
  the dump.
- The lead reconciles task completion. No task is silently
  skipped: every planned item ends `done`, `blocked`, or
  `superseded` in the run ledger.
- When a skill names an agent absent in the current harness, the
  work runs lead-owned under the same discipline and the ledger
  records the delegation as degraded.
- Critical claims get at least one adversarial verification pass
  after synthesis (FATAL / MAJOR / MINOR; fix FATAL before
  delivery and re-pass; MAJOR goes to Open Questions; accept
  MINOR).
- Two consecutive failures on the same goal is a full stop: state
  what is known, what is not, what was tried; wait for direction.
- Delegation is an ordered sequence, not a set: when a run cites,
  verifies, and reviews, the adversarial verify pass runs BEFORE
  the review pass and never in the same parallel dispatch — the
  adversarial pass sharpens what the review then judges. An on-disk
  proof that a claimed fix landed precedes calling it fixed.

## Ingestion of sources (resources/)

`resources/README.md` is the format authority. When a load-bearing
claim rests on a source not yet vendored, the default action is to
ingest it — vendor it as a PROVISIONAL entry immediately
(ingest-on-firsthand-need), not merely propose a candidate; Lane
ratifies before the claim is treated as load-bearing. No
load-bearing citation rests on a provisional entry.

Prefer the canonical source format. House the source's own markup —
LaTeX/`.tex` (an arXiv e-print) or other markup — when it is
available; the PDF is the next choice; a transcribed text
extraction (`.pdftext`) is the lowest, a greppability fallback.
Each entry records its canonical format (LaTeX-source / PDF /
scan), and the recorded document hash is of the canonical artifact
(the e-print tarball for a LaTeX source; the PDF for a PDF-only
source) — the format record disambiguates which. All vendored and
derived forms stay gitignored (the tarball, the extracted markup,
the `.pdftext`); only the committed line-anchored map, the hash,
and the publication data are tracked. A new unfolded-source file
extension not yet ignored is added to `.gitignore` as encountered.

Acquire an arXiv source directly — `curl
https://arxiv.org/e-print/<id>` for the LaTeX-source tarball plus
`https://arxiv.org/abs/<id>` for metadata (feynman alpha is not
relied on); compute the sha256 of the canonical artifact and record
it. Agents may ask to vendor a source at any time, especially when
a construction under development draws on it, so the citation and
the notes needed to use it for formalization are tracked.

## Delivery

Before stopping, verify on disk that every promised artifact
exists at its named path — never stop at an unsaved draft or an
intermediate. Report outcomes faithfully: failed checks and
blocked capabilities are reported as such, never smoothed over.

## Context-layer design decisions

The rulings that shaped this layer (Lane, 2026-07-11 → 07-13). Kept
here — tracked, in the agent-facing source of truth — so the design
ground-truth travels with the repository rather than living only in
local working memory. The full deliberation is in the session logs
(`notes/session-logs/`, the reboot and hardening entries).

- **Fan-out workflows are prose, not code.** The research workflows
  (deep-research, lit, compare, audit, mechanize, …) are prose prompt
  bodies orchestrating the agent roster; a deterministic multi-agent
  script is reserved for a bespoke one-off investigation, never the
  recurring workflows.
- **Ingest on firsthand need.** When a load-bearing claim rests on
  an unvendored source, dispatch the `ingest` agent for a directed
  PROVISIONAL entry; Lane ratifies before the claim is load-bearing.
  No load-bearing citation rests on a provisional entry.
- **resources/ = committed map over gitignored source.** A committed
  line-anchored location→content map (depth ∝ the source's load); the
  vendored artifact and every derived form gitignored; citations
  resolve through the committed map. Canonical-format hierarchy:
  source-markup (LaTeX) > PDF > transcribed text; the recorded hash
  is of the canonical artifact. Acquisition is direct (arXiv
  `curl .../e-print/` + web-search); the feynman-alpha path is broken
  and not relied on.
- **Repo-owned toolchain.** `flake.nix` pins every tool the layer
  needs (Agda + the ingestion/render/script tools), so operations and
  every `Gloss.*` certificate's `@ <commit>` pin are reproducible
  across environments.
- **The shim/prompt surface split** (2026-07-13, superseding the
  earlier merge): masters under `.agents/` — full bodies in
  `.agents/prompts/`, small auto-trigger shims in
  `.agents/skills/kitcat/` — reached by per-harness symlink or native
  discovery (see "Workflow surface topology"). This realizes the
  trigger/command split structurally; the shim and prompt names are
  kept identical across the pair.
- **The roster is the symmetric bracket.** `analyzer` (merged
  proof-strategist + structural analyst) prepares → `coder`
  implements → `analyzer` reviews accuracy + `reviewer` runs the
  mechanical gate; plus `researcher`, `verifier`, `ingest`, `writer`,
  `suite-maintainer`. Roles are `.agents/<name>.md`, symlinked to
  `.claude/agents/` and `.pi/agents/`.
- **Rijke is the foundational reference.** arXiv 2212.11082
  (`resources/rijke-hott/`) — the univalent-mathematics idiom every
  role draws on.
- **Memory is pointers.** Rulings and design live in tracked repo
  homes (this file, the session logs, `docs/gloss.md`, `docs/roadmap.md`);
  harness memory holds short-term state and pointers into them, never
  the canonical store. `/log` flags any ruling that exists only in
  memory so it is promoted here.
