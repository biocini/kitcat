# Session log — the context-layer reboot (feynman port)

**Date:** 2026-07-11 (branch `dev`, renamed from `typecheck-minimal`
this session)

**Scope:** The feynman.is skills bundle was ported into a
kitcat-owned, harness-generic workflow suite — sixteen research
workflows plus a capability rosetta, first-class under both Claude
Code and Pi from one canonical tree — with the ML-research content
morally translated to mathematics research. Mid-session, Lane ruled
the effort a **reboot, not an addition**: the pre-existing context
layer was retired entirely into `.attic/`, the new layer was purged
of every pointer into it, and the session-bridge mechanism itself
was replaced (handoff.md → `docs/roadmap.md` + this log chain +
`CHANGELOG.md`). A binding honesty standard (`docs/provenance.md`)
and a vetted-sources convention (`resources/`) were established.
No Agda was written or modified.

**Status:** built + discovery-verified on both harnesses (live
probes), staged in full, **not committed** — awaiting Lane's go.
`just check-all` was not run this session (no Agda changes; last
green at `593f44a`).

## 1. Work completed

The arc, with course corrections pinned:

1. **Investigation** — the bundle's anatomy (thin skill shims over
   prompt templates; a byte-identical tool-discipline block across
   all 13 prompts); both Pi builds' discovery mechanics verified
   from source (symlinks followed with realpath dedup; `$ARGUMENTS`
   an exact alias of `$@`; `.agents/skills/` a native project path;
   skills without `description:` silently unloaded); Claude Code
   mechanics verified from docs and live probes; a norms survey of
   AI-in-mathematics policy (arXiv, mathlib, Leiden Declaration,
   ACM/IEEE/Springer, all date-stamped in `docs/provenance.md`).
2. **Phase-0 spike** — the generic architecture validated end to
   end: `.agents/skills/kitcat/<name>/SKILL.md` canonical, Claude
   Code bridged by per-skill symlinks, Pi discovering natively.
   The `spike-echo` diagnostic returned
   `SPIKE-ECHO OK ARGS=[alpha beta]` under both harnesses.
3. **The port** — fifteen further skills drafted against a binding
   charter with the review-hardened `lit` as exemplar, each
   adversarially reviewed; 2 FATAL + 6 MAJOR + ~30 MINOR findings
   all applied. The FATALs forced the epistemic-label split:
   VERIFIED strictly machine-checked; SOURCE-CHECKED orthogonal.
4. **Course correction (Lane): reboot, not addition.** The layer
   had been built atop the old foundation — the drafting charter
   cited the old convention documents as authorities and handoff.md
   was wired in as the session bridge. Corrected in stages as
   Lane's intent sharpened: consultation pointers swept; insulation
   restated as a whitelist with total silence about what is outside
   it; finally the old layer retired bodily into `.attic/` (eleven
   artifacts: four convention docs moved with git history, coh.md,
   handoff.md, six pre-reboot research memos, four agent
   definitions, the docs-drift tooling porcelain with its justfile
   recipe removed, and the corpus review banked as the renovation
   reference). Declined en route, with reasons: revising the old
   convention docs now (gated post-refactor — Cat.* is in flight
   and current practice is not normative); treating my memory layer
   as the bank (memory is pointers into canonical context, never
   the store).
5. **The reference alignment** — Lane pointed at an external
   reference implementation of the workflow discipline; imported:
   `notes/session-logs/` naming, the `CHANGELOG.md` lab notebook
   with `/log` writing both, and the session-log header discipline
   (scope paragraph, honest status line, meta-process notes).
6. **Closing mechanics** — Pi slash adapters as prompt-template
   symlinks in `.pi/prompts/` and `.feynman/prompts/` (adapter
   chain probe green); the feynman original deleted per standing
   ruling; README adapted in place (present-tense identity, a
   research-provenance section, a build section, dead-module
   credits fixed), then trimmed to purpose-and-orientation only —
   no implementation particulars — by Lane's direction; the full
   reboot set staged.
7. **The agent roster, authored this session** — six definitions
   in `.agents/*.md`: `researcher` and `verifier` ported from the
   feynman originals under their original names (Lane's ruling),
   and the four Agda specialists (`cubical-agda-coder`,
   `cubical-agda-reviewer`, `cubical-analyzer`,
   `hott-theoretician`) written fresh from the contract — never
   from the quarantined definitions. Registration: the canonical
   files are discovered natively by the feynman-Pi build; symlinks
   bridge `.pi/agents/` and `.claude/agents/` (a differential
   probe confirmed Claude Code follows agent-file symlinks).
   Writer stays unported (the draft skill's synthesis is
   lead-owned by design); no standalone artifact-review agent (the
   review skill is lead-owned; its adversarial discipline lives in
   `verifier`).
8. **The whole-suite Opus review** — six lenses over the layer as
   one system found 2 FATAL, 6 MAJOR, and a set of MINOR findings;
   all applied. The FATALs were git-state traps: the `Log/`
   gitignore pattern was case-insensitively swallowing the log
   skill's directory (fixed by rooting the pattern to `/Log/`),
   and nine skill files were staged pre-rename. The load-bearing
   MAJORs: the `verifier` agent was narrowed from citation-writer
   to findings-report auditor to match every skill's Verify-step
   dispatch; the review skill's delegation step now distinguishes
   the file-writing researcher from the in-reply theoretician and
   analyzer; `notes/session-logs/` became exclusively the
   session-close log's namespace (mechanize and autoresearch
   progress records moved to their own plan ledgers); mechanize's
   full-module ledger edits were demoted to proposals-always;
   spike-mode failure preservation was reconciled with the coder's
   failure discipline; and HARNESS.md gained the
   final-artifact overwrite guard, the plan-less-skill recording
   rule, and the Pi trust-bootstrap note.
9. **The porcelain purge** — a nine-unit adversarial sweep of the
   justfile/bin tooling (Lane: cheap-model provenance, cut by
   default). CUT with all layer references trimmed: `log-failure`
   and the never-used `Log/` convention (failed attempts now
   preserved in plan ledgers); the `deps` cluster (`--orphans`
   crashed, `--reverse` answered wrongly; import questions now go
   through the file-search capability); `benchmark` (never run;
   timing is wall-clock via shell); `html-deploy` (never completed,
   remote-touching, publish target undecided); `check-dirty`
   (blind to untracked modules; the ritual is `just check` per
   touched module); and lint's imports check (~80% false
   positives). KEPT, verified sound: `check-all`/`check`,
   `sync-all`, `lint` (width+flags), `new-module` (blank-line fix),
   `html`/`html-serve`, `stats` (now Test-filtered) and `wip`.
   `mmv` KEPT with the boundary-safe sweep fix and a real-diff
   dry-run (the unbounded substring sweep had a demonstrated
   Alt/Alternative collision). Rulings enacted alongside: `src/Test/`
   and `Stash/` are gitignored (Test = WIP scratchpads only,
   upgrade path Gloss); the `import Test.Scratch` line left
   `All.lagda.md`, fixing the broken-clean-clone defect; the
   branch was renamed to `dev`.

Movement against a previous preview: none to record — this is the
first entry of the log chain; the mechanism it replaces was retired
this session. `docs/roadmap.md` targets 1–5 (stratum spike,
bimodule spike, THE REFACTOR, Chir, framed syntax) were not
advanced: this was infrastructure throughout.

## 2. Strongest findings and decisions

- VERIFIED (live probe, this machine): Claude Code loads symlinked
  skill directories, tolerates the dual-harness frontmatter, and
  substitutes `$ARGUMENTS` on `/name` invocation; upstream pi
  discovers the tree under project trust and runs the typed
  adapters. Evidence: the spike-echo outputs quoted above.
- VERIFIED (source, pinned in `.agents/skills/kitcat/HARNESS.md`):
  the capability map's three columns — including two incompatible
  Pi `subagent` schemas, which is why skills never copy dispatch
  shapes from documents.
- VERIFIED (source): Pi's context loader prefers AGENTS.md over
  CLAUDE.md when both exist — the reason root AGENTS.md was
  deleted, not just superseded.
- SOURCE-CHECKED (survey, URLs and dates in
  `docs/provenance.md`): the external policy landscape moved
  during 2026 — arXiv tightened while ACM dropped its disclosure
  mandate; mathlib's contributing guide is the nearest peer
  standard; no Agda-community policy exists.
- Decision (Lane): the nine honesty practices, mathlib-style commit
  trailers plus the repo-level statement, the `resources/` entry
  format (hash-verified vendored documents, gitignored), and the
  strict label semantics are binding — `docs/provenance.md`.

## 3. Modules touched

None. The only `src/` change is a one-line prose edit in
`src/Gloss/CLAUDE.md` (certificate conventions; no Agda). The
standing `src/Cat/Type.lagda.md` whitespace diff predates the
session and remains uncommitted by Lane's standing call.

## 4. Spikes

None created. The 25 files under `src/Test/` predate this session;
their fates are unchanged.

## 5. Theorem ledger

No entries added or upgraded. One maintenance-prose clause struck
by Lane's ruling; the ledger↔certificate bijection is intact (five
🧪 markers ↔ five `Gloss.*` modules, verified during the corpus
review).

## 6. Failures preserved

None; `Log/` is empty and `just log-failure` was not invoked.

## 7. Proposals

- Founding `resources/` entries from the repo-root PDFs: Melliès
  (Dialogue categories and chiralities; braided dialogue), Petrakis
  slides, cat-dep-arrows, the thesis, the semiring-annotated type
  systems paper, the microlocal-negation paper.
- `resources/` entries for Kelly and Melliès to back the ledger's
  T15/T16 source references (currently uncovered by vetting).

## 8. Meta-process notes worth carrying

- The session's costly failure: building the layer as an addition
  when the directive meant a reboot. When a directive names a fresh
  start, establish FIRST whether existing artifacts are inputs or
  objects of replacement — before any drafting charter is written.
- The save: contamination entered through single sources (one
  charter block; one insulation list), so the cure was a sweep, not
  a rebuild. Centralize the things that could taint.
- Insulation done right is a whitelist plus total silence; naming
  what is excluded re-imports it.
- Dimension-specific adversarial review briefs earn their cost:
  both FATALs came from the one reviewer whose brief carried the
  honesty practices.
- Live headless probes (`claude -p`, `pi -p -a`) settle
  "UNVERIFIED" in minutes; almost nothing about a locally installed
  harness should stay unverified for a whole session.

## 9. Open questions and risks

- The commit itself: everything is staged; nothing is committed.
- Pi-side discovery is trust-gated per machine (`--approve` or
  persistent trust); a fresh clone shows no skills under Pi until
  trust is granted.
- Pi's `enableSkillCommands` remains unset by design (the adapters
  provide the typed form).
- The ledger's T15/T16 literature references remain unvetted
  pending their `resources/` entries.
- The attic renovation queue is entirely gated on Lane
  (post-refactor): nothing in `.attic/` may be consulted meanwhile.
- `just lint` reports pre-existing width violations in `src/` —
  the style-adherence debt Lane named, untouched by this session
  (no Agda changed), waiting on the post-refactor style arc.
- Gitignore rulings closed at session end: Lane removed `keys/`
  and ignored `.pi/tasks` directly; `MAlonzo/**` kept; the
  vendored-format set ratified in full. `mmv`'s left-boundary
  guard was fixed and probe-verified alongside the trailing one.
  Lane restored the standing `Cat/Type` whitespace diff.

## 10. Next steps

1. Commit the staged reboot on Lane's go-ahead
   (`Assisted-by: Claude (claude-fable-5)` per provenance practice
   6).
2. **The clean-working-directory session**: every remaining
   untracked file cleaned up, ignored, or given a canonical home.
   The stray inventory after this session's gitignore rulings:
   the root PDFs (ingest into `resources/` via the
   alpha-research acquisition path — hash, vet, entry per
   `resources/README.md`; the Melliès and Petrakis items double as
   the T15/T16 vetting backlog), `src/Cat/Experiment/`, and
   `.pi/tasks/`. The ingestion is the FIRST TEST of the paper
   acquisition workflow: run it as a shakedown, and record
   workflow defects (skill gaps, hash-protocol friction, entry
   format problems) as first-class findings alongside the entries
   produced.
3. Resume the mathematics: roadmap targets 1–2 (faithful-stratum
   spike A1–A3; bimodule spike B1–B3).

## 11. Artifacts

- Canonical layer (staged): `.agents/skills/kitcat/` (HARNESS.md +
  17 skills), `.agents/*.md` (six agents), `.claude/skills/` +
  `.claude/agents/` symlinks, `.pi/prompts/` + `.pi/agents/` +
  `.feynman/prompts/` symlinks, `CLAUDE.md`,
  `docs/{gloss,provenance,roadmap}.md`, `resources/README.md`,
  `README.md`, `CHANGELOG.md`, `justfile`, `.gitignore`,
  `src/Gloss/CLAUDE.md`, `.attic/` (eleven quarantined artifacts +
  its README).
- Run artifacts: none under `notes/plans/`, `notes/research/`, or
  `notes/watches/` — the session's plans were carried in
  conversation and this log supersedes them.
- Blocked capabilities: none — every capability named by the suite
  was visible this session. Delegations after Lane disabled
  workflow orchestration were lead-owned by direction (process
  control), not degraded.
