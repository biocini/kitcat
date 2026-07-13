# .agents/CLAUDE.md — the cross-agent contract

The repo-level contract for every agent and workflow operating in
this repository, under any harness. Skill bodies, agent
definitions, and workflow runs follow the conventions here; read
this file once per session before executing any workflow.

Division of authority: this file carries cross-agent conventions
only. Harness mechanics (capability→tool mapping, authoring rules
for the skills tree) live in `.agents/skills/kitcat/HARNESS.md`;
per-agent prompt text lives in `.agents/<name>.md` — edit those
files rather than restating them here; the working discipline (the
practiced principles and their exemplars) is `.agents/methodology.md`;
honesty and citation standards are `docs/provenance.md`, which is
binding; the repository contract (build, style, namespaces, hard
rules) is the root `CLAUDE.md`.

This file is the only place these cross-agent conventions — output
locations, the slug rule, the epistemic lexicon, provenance-sidecar
contents, delegation and degraded-delegation handling, and
ingestion — are stated. Every prompt body, agent definition, and
workflow NAMES a convention and defers here ("derive a run slug per
the contract", "write the sidecar per the contract"), never
restating its content; a slug/lexicon/sidecar spec appearing
verbatim in a prompt body (`.agents/prompts/`) or an agent
definition is an authoring defect a human confirms — exactly as
`HARNESS.md` is the sole home of tool names.

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
