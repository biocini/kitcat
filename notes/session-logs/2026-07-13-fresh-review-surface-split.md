# Session log — the fresh-review and the shim/prompt surface split

**Date:** 2026-07-13 (branch `dev`).

**Scope:** Opened on the previous session's next-step 1 — a
fresh-eyes adversarial review of the hardened context layer — and
carried it through to application, then absorbed a substantial
architecture change Lane directed: the workflow surface was
re-expressed as the feynman-style shim/prompt split, harness-generic.
An eight-reviewer workflow (adversarially verified) produced 58
findings against rulings R1–R13; all FATAL/MAJOR and Lane's five
decisions were applied, six `resources/` entries were brought to the
R11 bar by delegated `ingest` runs, the surface was rebuilt (masters
in `.agents/`, Claude Code via symlinks, `.pi/prompts` + `.feynman/`
removed), and the design was documented in `.agents/CLAUDE.md` as the
context-layer source of truth. No Agda changed.

**Status:** built + committed + verified where verifiable (authoring
lint, `just sync`, flake build with agda 2.8.0 + all layer tools,
symlink integrity, tree independence, shim↔prompt pairing all green).
Three commits: the amended `1b50416` (codename scrub), `38dcb3c`
(apply-pass + surface redesign), `4c7d34b` (resolved deferrals). Six
`resources/` entries remain PROVISIONAL pending Lane's ratification.

## 1. Work completed

The arc, with course-corrections pinned:

1. **The fresh review (Workflow 1).** An 8-reviewer fan-out over the
   whole layer (contract core, roster, both skill clusters, resources
   + provenance, substrate, independence sweep, fresh-session
   simulation), each finding then run through an adversarial verifier
   defaulting to refute, with R1–R13 as ground truth. 62 raw → 58
   verified findings (33 CONFIRMED, 25 WEAKENED; 3 REFUTED and
   dropped): after severity correction, 5 FATAL, 18 MAJOR, 35 MINOR.
   The structural spine got a clean bill.
2. **Spend-limit interruption + resume.** The verify phase was cut
   off mid-run when Fable 5 hit the monthly spend limit (17 of 61
   verify agents died). Switched to Opus 4.8 and resumed the workflow
   via `resumeFromRunId` — the 52 completed agents replayed from
   cache, only the 17 failed verifiers re-ran, reusing the exact
   dedup indices. Clean recovery; no findings lost.
3. **The five decisions (Lane).** Independence: reword the two
   codename lines, amend permitted. Lint baseline: establish a good
   in-flight baseline and weave it in, strictify later. Marker-
   shedding: gate on ratification. `flake.lock`: commit it. Resources:
   dedup chiralities, cite braided as unpublished iff unverifiable
   elsewhere, give the codep slides a library reference, re-ingest
   dep-arrows as canonical.
4. **The apply-pass.** All FATAL/MAJOR fixed: R7 Rijke to
   coder/reviewer/ingest + root References; R2 ingest wired into
   alpha-research + the research skills; R6 writer dispatched by
   draft; the writer↔verifier citation contradiction; the
   marker-shedding policy across gloss/provenance/contract/verifier;
   the `bin/lint` soundness fix; the new `lint changed` non-regression
   width gate; the flake tool additions; the session-log independence
   correction. Six `resources/` entries brought to R11 by three
   delegated `ingest` runs and one `researcher` pub-status check.
5. **The surface redesign (Lane, three rounds).** Lane directed the
   shim/prompt split. It took three exchanges to land because the lead
   over-complicated a simple design (see §8). Final shape: full
   workflow bodies are masters at `.agents/prompts/<name>.md`; small
   auto-trigger shims at `.agents/skills/kitcat/<name>/SKILL.md`;
   Claude Code reaches them via two directory symlinks
   (`.claude/commands` → `.agents/prompts`, `.claude/skills` →
   `.agents/skills/kitcat`); pi reads `.agents/` directly;
   `.pi/prompts` and `.feynman/` deleted. 18 bodies moved, 18 shims
   written, 71 per-skill symlinks replaced by 2.
6. **Documentation + deferrals.** `.agents/CLAUDE.md` established as
   the metacontextual source of truth with the two-audience division
   of labor explicit, plus a Context-layer design-decisions section
   (R10 externalization). Then Lane's rulings on the deferrals:
   analyzer lexicon trimmed to defer; Test/ reference rule scoped to
   the dependency/evidence-citation sense; methodology P5 exemplar
   repointed to the tracked killcheck witnesses.

Movement against the previous preview (2026-07-12 next-steps): step 1
(fresh review) done and applied; step 3 (flake shakedown) done — it
caught the `poppler_utils` rename that would have broken the flake at
HEAD; step 4 (resume the mathematics) is still teed up — this session
stayed in the context layer throughout. `docs/roadmap.md` targets 1–5
were not advanced.

## 2. Strongest findings and decisions

- **The fresh review found the layer sound but under-executed**
  (VERIFIED by the workflow + adversarial pass): almost every finding
  was a ruling not fully propagated, not a design flaw. The FATAL
  five were R7 reaching 3 of 7 roles, R2 inverted inside
  alpha-research, R6 writer unreachable, the codename in the tracked
  session log, and the flake not evaluating.
- **The flake did not evaluate at HEAD** (VERIFIED): `poppler_utils`
  was renamed to `poppler-utils` in the pinned nixpkgs. Fixed; the
  devshell now provides agda 2.8.0 + curl/git/gnutar/perl/poppler and
  runs `just check-all`. `flake.lock` committed.
- **`.agents/CLAUDE.md` is the context-layer source of truth**
  (Lane's reframe, the key architectural decision): root `CLAUDE.md`
  is the repo user's guide; `.agents/` is the agent-facing source of
  truth. The "only place" tension resolves by deference, not
  duplication. The durable R1–R13 rulings now travel tracked in the
  design-decisions section.
- **The lint baseline is a non-regression gate** (VERIFIED, self-
  tested): `just lint changed` flags only over-width lines a change
  adds/modifies, ignoring the ~197-line in-flight width baseline;
  full `just lint` is the strictification target. Woven into
  CLAUDE.md, reviewer, coder, methodology.
- **The Melliès *Braided notions* manuscript has no published
  version** (SOURCE-CHECKED against arXiv author listing, DBLP, the
  author's IRIF index, 2026-07-13): cite as unpublished; the balanced-
  dialogue-category notion continues in the published *Ribbon
  Tensorial Logic*, LICS 2018 (DOI 10.1145/3209108.3209129).
- **`petrakis-dep-arrows` re-ingested as LaTeX-source canonical**
  (VERIFIED, hash `3cb80488…` of the e-print tarball; v1 is the only
  arXiv version).

## 3. Modules touched

No Agda modules (VERIFIED: no `src/**/*.lagda.md` changed except
none). Context layer only: `.agents/` (46 files — `CLAUDE.md`
reframed + design decisions, `methodology.md`, the roster
analyzer/coder/reviewer/ingest/writer/verifier/suite-maintainer,
`HARNESS.md`, all 18 prompts moved + 18 shims written); `.claude/`
(38 — the two new dir-symlinks replacing per-skill ones); `.pi/`
(18 — `.pi/prompts` removed); `.feynman/` (17 — removed);
`resources/` (5 tracked READMEs brought to R11 + rijke unchanged);
`docs/` (gloss, provenance, roadmap); `flake.nix` + `flake.lock`;
`CLAUDE.md`; `bin/lint`.

## 4. Spikes

None created this session (no Agda). The `src/Test/` files present
are from the mathematics arc, unchanged.

## 5. Theorem ledger

One change (VERIFIED in `docs/gloss.md`): T16 (Melliès convergence)
`📐 → 📐⚠️`, now CONJECTURED until Lane ratifies its backing
`resources/mellies-dialogue-chiralities` entry. The maintenance rule
was corrected to gate the ⚠️/CONJECTURED lift on a *vetted*
(Lane-ratified) entry, not merely a present one — a PROVISIONAL entry
does not lift the marker. The ledger↔certificate bijection (5↔5) is
unaffected; no certificates changed.

## 6. Failures preserved

No proof attempts (no Agda). Two operational course-corrections worth
carrying are in §8.

## 7. Proposals

- **Ratify the six `resources/` entries** — the packet is ready (per
  entry: source + identifier, canonical format, hash, map depth,
  per-entry decisions). Rijke is the R7 keystone; ratifying it
  unblocks the foundational references.
- **Shake down the never-run workflows** (audit, mechanize,
  deep-research, compare, lit, formulation-survey, draft,
  autoresearch, watch, `/prove`) before reliance — the fresh review
  itself was the exemplar of what a real run surfaces.
- **Vendor the Kelly source** (`resources/kelly-mac-lane-coherence`,
  Kelly 1964) to lift T15 off ⚠️ — paywalled, needs Lane's access.
- **Deferred, per Lane's ruling:** the `methodology.md` exemplar-
  provenance cleanup beyond P5 (P1's "mined the wall into a
  naturality" detail is in the tracked session log but the finer
  provenance is in harness memory) — low priority.

## 8. Meta-process notes worth carrying

- **The surface redesign took three rounds because the lead
  over-complicated a simple design.** The design is: masters in
  `.agents/`, symlinks in each harness's idiomatic dir, ONLY symlinks
  needed — the systems are parallel, each harness reads the same
  masters from its own location. The lead kept trying to reconcile
  root `CLAUDE.md` and `.agents/CLAUDE.md` as competing, and kept
  proposing topology variants, instead of seeing the two-audience
  division. Lesson: when a user says a design is simple and points at
  a working exemplar, model the exemplar's mechanism concretely
  before proposing options — and name the division of labor first.
- **Resume-from-runId recovered a spend-limit interruption cleanly.**
  A workflow cut off mid-phase (monthly limit) resumed on a different
  model with cached prefixes intact; only the failed tail re-ran. The
  journal (`journal.jsonl`) reconstructed the full finding set when
  the returned result was truncated.
- **Delegate the mechanical, lead-own the high-stakes.** The six
  resources R11 upgrades and the eight skill-body amendments went to
  `ingest`/`suite-maintainer` agents on disjoint files; the contract,
  policy, code, and git edits stayed lead-owned — matching the WF2
  discipline from the plan.
- **A "clean" claim that contains its own counterexample.** The
  independence-correction note first quoted the search pattern
  `rg 'lb|…'`, so the line asserting "no matches" contained the token
  — caught and reworded to describe the check without embedding the
  codename. Documenting a search is not the same as being free of
  what it searches for.

## 9. Open questions and risks

- **Six PROVISIONAL `resources/` entries** await ratification before
  any citation on them is load-bearing.
- **The workflows are still mostly unexercised** — the fresh review,
  the ingest runs, and this `/log` are the only real runs; expect
  defects on first use of the others.
- **Root `CLAUDE.md` still carries agent-facing sections** (roster,
  discipline, delegation) that the two-audience division would place
  in `.agents/`. Left as-is this session; a further migration is a
  larger call for Lane.
- **The mathematics has not resumed** — roadmap targets 1–2 (faithful-
  stratum spike A1–A3, bimodule spike B1–B3) are teed up but untouched
  across two infrastructure-heavy sessions.

## 10. Next steps

1. **Ratify the `resources/` entries** (open the PROVISIONAL six) —
   Rijke first (the R7 keystone), then the five founding entries.
2. **Resume the mathematics in earnest** — `docs/roadmap.md` targets
   1–2, driven by `/prove`; the pre-registered kill criteria are in
   the ontology memo (memo A). This is the standing priority the last
   two sessions deferred.
3. **Shake down a research workflow** on a real question before
   relying on the suite (mechanize or deep-research is the natural
   first).
4. As they arise: the Kelly resource (Lane's access); whether to
   migrate root `CLAUDE.md`'s agent sections into `.agents/`.

## 11. Artifacts

- Committed: the three commits above (context layer only).
- Tracked session bridge: this log + `CHANGELOG.md` + the prior
  session logs.
- Local working memory (gitignored, this machine): the fresh-review
  workflow transcript and its `journal.jsonl` (the full 58-finding
  set), `notes/research/mellies-braided-pubstatus.md`, and the prior
  session's `notes/plans/` audit trail (the full R1–R13 deliberation;
  the durable rulings are now tracked in `.agents/CLAUDE.md`).
- No blocked capabilities. Delegations (three `ingest`, one
  `researcher`, one `suite-maintainer`, the review workflow) all
  completed clean; the review's verify phase blocked once on the
  spend limit and was resumed successfully.
