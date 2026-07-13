# Kitcat — Cubical Agda Library

Experimental univalent mathematics and computer science library in
Cubical Agda. This file is the canonical agent contract; every
harness (Claude Code, Pi) loads it.

## CRITICAL WORKFLOW RULE

**Never implement Agda code directly when the roster is present.
Delegate:**

- Implementation/coding → `coder`
- Analysis, proof strategy, placement, accuracy review → `analyzer`
- Mechanical review/quality gate → `reviewer`

Your role is orchestration: gather minimal context, delegate with
complete self-contained briefs, synthesize results. The roster is
authored once in `.agents/` and registered per-harness via the
agent symlinks; when a named agent is not registered in your
harness, do the work lead-owned under the same discipline and
record the delegation as degraded.

## Specialized Agents

| Agent | Use when |
| --- | --- |
| `analyzer` | Dependencies, imports, gaps, placement, duplication, planning; proof strategy, formulations, required lemmas; accuracy review of an implementation |
| `coder` | Any request to produce or fix Agda code |
| `reviewer` | Mechanical style/correctness/hard-rule/ledger gate before any commit |
| `researcher` | External literature evidence: arXiv/nLab/1lab sweeps, file-based notes |
| `verifier` | Citation checks: URLs resolve, sources state their claims, ledger bijection |
| `ingest` | Acquire and vendor a source (arXiv LaTeX / PDF), hash the canonical artifact, prepare a PROVISIONAL `resources/` entry |
| `writer` | Turn research, ledger entries, and certificates into structured exposition (adds no citations — the lead cites, the verifier audits) |
| `suite-maintainer` | Author or repair skills and agent definitions; the authoring lint; the shim/prompt masters, harness symlinks, and bind-once contract |
| `process-reviewer` | Session-close process review (the `/log` stage): friction points mapped to workflow revision/addition proposals or named system weaknesses, tagged ratify-now / next-session for Lane's discretion |

Agent registries are per-harness and availability varies; a
workflow that names an absent agent runs lead-owned and records the
delegation as degraded.

Consult the `analyzer` BEFORE the coder starts any proof
involving: h-levels or truncation, equivalence constructions,
coherence or naturality, transport/substitution chains, fiber
arguments, univalence. Don't consult for routine proofs (ap, sym,
simple paths, direct pattern matching).

**Workflow** (the symmetric bracket) — new features: `analyzer`
(analysis + strategy) → `coder` → `analyzer` (accuracy review) +
`reviewer` (mechanical gate). Bug fixes: `analyzer` if strategy is
unclear → `coder` → `reviewer`. Refactoring: `analyzer` → `coder`
→ `reviewer`.

## Agent Discipline

- Two consecutive failures on the same goal = full stop. State
  what you know, what you don't, what you've tried. Wait for
  direction.
- State confidence and what you haven't verified before every
  proposed change.
- Before modifying a module: read it and everything it imports
  that you'll touch. State what you found. Then act.
- After a failed proof attempt: preserve the attempt in the run's
  plan ledger, then revert. Do not stack fixes on a broken
  approach. On a genuine two-strikes wall, KEEP the timestamped
  `src/Test/` spike (do not delete it) with `-- STUCK:` comments
  transcribing the goal type at the stuck hole — verbatim or
  content-exact, per the spike report contract below — and what
  was tried; revert the real modules; invent no auxiliary axioms;
  and register the kept spike plus its salvage — the reusable
  machinery it produced and what the wall points at — in the run
  ledger under a "do not re-derive; build on" heading, so the next
  session builds on the recorded wall rather than re-litigating it
  (the θ-core/op-invol arc kept `Test/CodepOpTheta-20260710-223915`,
  whose walls were mined next session into a naturality across the
  polarity swap).
- If a directive is ambiguous — multiple readings leading to
  different actions — seek clarification first. A short approval
  is not a blank check.
- Memo/consultation claims are conjectures until machine-checked:
  mark every load-bearing claim VERIFIED or CONJECTURED, and gate
  implementation on a spike for the conjectured ones. A spike is
  dispatched with an oracle-shaped report contract — a required
  verdict in {DERIVED, STUCK, PARTIAL}, which route closed, and the
  exact goal residue at any stuck hole. "Verbatim" for a residue
  means the fenced raw typechecker error from a refl-probe (force
  the missing bridge with `refl`, capture the exit-42 error,
  revert); a reconstruction is labeled content-exact, and either
  discharges the contract. The typecheck against the real
  foundation (never a toy model) is the pin, prose is never the
  pin. A spike is warranted only by an actually-open
  fork (a candidate cell, an unpinned coherence, an is-X-derivable
  question), never a routine ap/sym proof — a redundant spike is the
  ornamental redundancy faithfulness forbids.
- Commit only when Lane says to commit.

## Proof Sketches

When the `analyzer` produces proof sketches for the coder, include
explicit type annotations at each step — ambiguous intermediate
types make the coder guess wrong and burn debugging cycles:

- Annotate the goal type of each lemma and `where`-binding.
- For ∙-chains, annotate each link's endpoints when they involve
  compositions or derived operations.
- For cancellation lemmas, spell out the injected equation that
  gets cancelled.
- For `iso→equiv`-style constructions, write the section and
  retraction types, not just the function names.
- When pointing the coder at a probe/scratch file, say whether the
  surrounding wrapper (e.g. the `contr-face` plumbing) is included
  or must be built.

## Library Constraints

Per-module flags:

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}
```

Global flags in `kitcat.agda-lib`: `--no-import-sorts`,
`--no-sized-types`, `--erasure`, `--auto-inline`,
`--erased-matches`, `--exact-split`, `--hidden-argument-puns`,
`--postfix-projections`, `--qualified-instances`, `-Werror`,
`-WnoUnsupportedIndexedMatch`. Variants: `--erased-cubical`
(default), `--cubical-compatible` (pure foundation layers),
`--cubical` (only for Glue/computational univalence). Dependencies:
Agda builtins only — no agda-stdlib, no cubical library. Records:
`no-eta-equality` for multi-field or proof-valued records, `INLINE`
constructors via copatterns, `@0` on law fields (never on
operations).

## Namespaces

| Namespace | Purpose |
| --------- | ---------------------------------------------- |
| `Core.*`  | Foundational primitives (stable, core API)     |
| `Data.*`  | Concrete data types and their properties       |
| `HData.*` | Higher inductive types (pushouts, quotients)   |
| `Cat.*`   | Category theory (`Cat.Codep` is canonical)     |
| `Lib.*`   | Extended developments (groups, cubical sets)   |
| `Trait.*` | Typeclass-like interfaces and instances        |
| `Meta.*`  | Metaprogramming, reflection, tactics           |
| `Gloss.*` | Frozen evidence certificates for docs/gloss.md (in All; see src/Gloss/CLAUDE.md) |
| `Test.*`  | Tracked scratch + regression witnesses (gate-exempt; upgrade path: `Gloss.*`) |

Use `just stats` for live inventories rather than maintaining
static tables.

## Context Layer

This root file is the repo user's guide — build, style, namespaces,
hard rules, the mathematics. **The agent-facing source of truth for
the context layer is `.agents/CLAUDE.md`**: the cross-agent
conventions, the workflow surface design, and the design decisions
live there, and every agent, workflow, and prompt defers to it. A
repo user does not need the context-layer meta unless they choose to
read `.agents/CLAUDE.md`; this section only enumerates the layer.

The agent-facing context is exactly: this file, src/Gloss/CLAUDE.md,
`.agents/CLAUDE.md` (the context-layer source of truth),
`.agents/methodology.md` (the working discipline), the agent roster
(`.agents/*.md`), README.md, CHANGELOG.md, docs/gloss.md (the theorem
ledger), docs/provenance.md, docs/roadmap.md, docs/styleguide.md
(the Core.* idiom codified), the workflow suite
(`.agents/prompts/` bodies + `.agents/skills/kitcat/` shims),
`resources/`, and `notes/`. Nothing else in the repository is
loaded, cited, or consulted as an authority. Style law: match the
local idiom of the module you are editing — Core.* is the exemplar,
docs/styleguide.md the codified mechanics — and escalate style
questions to Lane. Sessions open by reading
the latest `notes/session-logs/` entry and docs/roadmap.md, and close with
`/log`.

## References

- **docs/gloss.md** — the theorem ledger (proven results + status)
- **docs/provenance.md** — honesty and citation standards (binding)
- **resources/** — vetted source entries: citation, vetting record,
  document hash, summaries (resources/README.md is the format
  authority); vet claims against these, and cite by entry
- [Rijke, *Introduction to Homotopy Type Theory*](https://arxiv.org/abs/2212.11082)
  (`resources/rijke-hott/`) — the library's mathematical-foundations
  reference (univalent mathematics); the common knowledge base every
  role draws on for definitions and terminology
- [Bentzen, *Naive cubical type theory*](https://arxiv.org/abs/1911.05844)
  (`resources/bentzen-naive-cubical/`) — Rijke's cubical-idiom
  companion: paths as interval functions, the Kan operations,
  derived connections, the cubical groupoid laws by explicit
  composition scenarios (develops no univalence — that side is
  Rijke's)
- [1lab](https://1lab.dev) — idiomatic cubical Agda patterns
- [Capriotti–Kraus](https://arxiv.org/abs/1707.03693) — univalent higher categories
- [Petrakis, *Categories with dependent arrows*](https://arxiv.org/abs/2303.14754)
  (`resources/petrakis-dep-arrows/`) — the dependent-arrows ancestor
  of `Cat.Codep`; the codependent half is in
  `resources/petrakis-codep-slides/`
- [Petrakis](https://arxiv.org/abs/2205.06651) — univalent typoids
- [Sterling](https://www.jonmsterling.com/005B) — virtual bicategory theory

## Tooling

`just --list` shows all recipes; `bin/` scripts are on PATH via
`.envrc`. The load-bearing ones:

| Command | What it does |
| --- | --- |
| `just check-all` | Typecheck the library via `All.lagda.md` |
| `just check <Mod>` | Typecheck one module (dot-path or file path) |
| `just new <Mod> [--aggregator]` | New module with correct boilerplate |
| `just mv Old.Name New.Name [--dry-run]` | Move/rename, updating references |
| `just sync [--fix]` | Report/fix drift between All and the filesystem |
| `just lint [width\|flags\|authoring\|changed]` | Lint (72 prose / 85 code, pragmas; `authoring` gates the skills tree; `changed` is the non-regression pre-commit gate) |
| `just resources-verify [--remote]` | Custody check: entry hashes vs vendored artifacts; `--remote` adds arXiv version drift |
| `just stats` / `just wip` | Inventories |
| `just html` / `html-serve` | Docs site, built and served locally |

Notes: `sync` is aggregator-aware (submodules re-exported via
`open import … public` are not flagged). `just mv`'s reference
sweep covers `src/` only — hand-check `docs/` citations after
moving a cited module.

Use the tools, not raw invocations: after creating a module →
`just sync --fix`; after renaming → `just mv`; before committing →
`just lint changed` + `just check <Mod>` on every touched module;
investigating structure → the file-search capability over imports.
Never hand-edit `All.lagda.md` imports when `sync` can do it.

Lint baseline: the library is in flight, so the full `just lint`
currently reports a known width baseline (~197 lines, all width, no
flag violations — run `just lint width` for the live list). The
pre-commit gate is therefore `just lint changed`, the non-regression
scope: it lints only files modified vs HEAD and flags width only on
lines the change itself adds or modifies, so a touched file's
pre-existing baseline does not block the commit while a newly
over-width line does. The full `just lint` is the periodic
strictification target (drive the baseline down deliberately, not as
a side effect); `just lint flags` and `just lint authoring` are
always strict (zero tolerance).

**Test/ scratchpad**: agents may create timestamped scratch files
`src/Test/<Name>-<YYYYMMDD-HHMMSS>.lagda.md` for experiments —
`<Name>` PascalCase and topic-prefixed by arc (`CodepFaithful`,
`TriFace23Probe`), the timestamp fixed at creation; the pair reads
cleanly as the module name (`Test.CodepFaithful-20260713-140913`).
The timestamp IS the tier marker: timestamped = scratch,
untimestamped = durable. The directory is tracked but gate-exempt:
its files need not typecheck cleanly, `just lint` skips them by
name, and `just stats` excludes them — `Gloss.*` is the polished
tier. Untimestamped Test/ files (`src/Test/<Name>.lagda.md`,
PascalCase, named for what they guard) are the durable exception:
regression witnesses (killchecks, probative tests), wired into
`src/All.lagda.md` by a manual `import Test.<Name>` so they run
with every `just check-all` (`sync` preserves manual Test entries
and never adds its own). Legacy files predating this convention
are triaged at the untracked-file cleanup, not renamed ad hoc. No
library module (`Core.*`, `Data.*`, `Cat.*`, …) or committed doc
may reference a Test/ file *as a dependency or evidence citation*
— All's manual regression imports are the one sanctioned import,
and no committed doc cites a Test/ file as the proof of a claim
(such a citation is a Test→Gloss promotion trigger: promote the
evidence to `Gloss.*` or drop the citation, per
src/Gloss/CLAUDE.md). Recording a kept spike's existence and fate
in a session log or plan ledger is the sanctioned process-history
exception — "preserve the attempt", not an evidence citation.
Promotion of settled evidence to `Gloss.*` follows
src/Gloss/CLAUDE.md.

## Workflow Suite

Each workflow is two harness-generic masters under `.agents/`: the
prompt body `.agents/prompts/<name>.md` (the full `/name` workflow)
and a small auto-trigger shim `.agents/skills/kitcat/<name>/SKILL.md`.
The masters live once; each harness reads them from its own location
— Pi natively (project trust required), Claude Code through two
directory symlinks (`.claude/commands` → `.agents/prompts`,
`.claude/skills` → `.agents/skills/kitcat`). The full topology is in
`.agents/CLAUDE.md` ("Workflow surface topology");
`.agents/skills/kitcat/HARNESS.md` is the capability rosetta (prompt
bodies name capabilities, HARNESS.md alone names harness tools) and
carries the authoring mechanics. Workflows invoke as `/name` and
auto-trigger by the shim's description; `spike-echo` is the discovery
diagnostic. The suite: deep-research, lit, compare, audit, mechanize,
formulation-survey, critique, draft, autoresearch, watch, eli5, hott,
log, jobs, preview, session-search, alpha-research, prove.

## Research Artifacts

- `notes/plans/<YYYY-MM-DD>-<slug>.md` — run plans: local working memory
  (gitignored), readable by any harness on this machine.
- `notes/research/` — research intermediates, finals, and their
  `.provenance.md` sidecars: local working memory (gitignored).
- `notes/session-logs/<YYYY-MM-DD>-<slug>.md` — append-only session
  logs: where things stand, open questions, next-step preview. This
  and `CHANGELOG.md` are the tracked session bridge; the
  working-memory notes are distilled into them at session close.
- `CHANGELOG.md` — the lab notebook: what happened, newest first,
  with honest verification markers. `/log` writes both at session
  close.
- `notes/watches/` — literature-watch state.
- `resources/<slug>/` — vetted sources (documents vendored locally
  and gitignored; hashes and vetting records tracked).
- `docs/roadmap.md` — the high-level overview of the repository's
  ongoing projects and their gates, in the rough order of intended
  progression, subject to Lane's direction; updated when a project
  lands or is re-gated, not per session. The latest
  `notes/session-logs/` entry is the session bridge.

## Honesty and Provenance

docs/provenance.md is binding. The short form: VERIFIED means
machine-checked in this repository (name the module or Gloss
certificate); SOURCE-CHECKED means the opened document states the
claim; literature claims are CONJECTURED; `[unvetted]` references
support nothing load-bearing. Novelty language is "we are not aware
of prior work" plus the search performed. Commits with substantial
AI-produced content carry the trailer
`Assisted-by: Claude (<model>)`. Code adapted from external sources
carries a credit comment (docs/provenance.md "Code citations" owns
the spec: the obligation travels through memo/brief handoffs —
never laundered — and adding or changing credits triggers the
verifier's citation review before commit):

```agda
-- Credit: 1lab, Equiv.Fibrewise
-- Following Rijke, Theorem 11.2.4
-- From Capriotti–Kraus (arXiv:1707.03693), Section 3.2
```

## Documentation Maintenance

These documents track the development at different cadences:

- **docs/gloss.md** — the theorem ledger. Add an entry when a
  result is proven or a countermodel established; upgrade 📐 → ✅
  on mechanization; every 🧪 entry names its `Gloss.*` certificate
  and vice versa.
- **docs/provenance.md** — honesty standards. Update when the
  external policy landscape shifts; date-stamp policy citations.

## All Module

`src/All.lagda.md` is the whole-library typecheck target.
Conventions (enforced by `sync`): aggregator imports only;
`import` not `open import`; WIP modules commented out with a
reason (`just wip`). Manual `Test.*` imports are the sanctioned
regression tripwires (see the Test/ rules): `sync` preserves them
and never adds its own.

## Hard Rules

- All code compiles with ZERO warnings — exit 42 is failure. Fix
  warnings; never add `-W` suppression flags without explicit
  authorization. Watch for `InlineNoExactSplit` (use copatterns,
  not constructor application) and `UselessPrivate` (no `private`
  inside `where`).
- No postulates, no TERMINATING pragmas, no unsafe features
  without explicit authorization.
- No external library imports.
- No features incompatible with `--erased-cubical`.
- Style: match the surrounding module's idiom (Core.* is the
  exemplar; docs/styleguide.md codifies its mechanics); escalate
  style questions rather than improvising.
- **Never truncate homs.** Categories here are wild by design; do
  not pursue or assume hom-set conditions. (The op-involution
  regress theorem, docs/gloss.md T12, is why this is
  load-bearing, not aesthetic.)
- No wrapper definitions that are beta-eta equal to an existing
  function (e.g. a specialized alias of `funext`). Factoring a
  shared proof skeleton into a named helper is good; re-typing a
  primitive is ornament.

## Process Assessment

After any non-trivial delegated task (roughly >3 minutes), deliver
a concise process assessment: challenges, decisions, workflow
gaps, recommendations. Bullet points; skip for trivial
delegations.

## Comment Style

Straightforward and direct. No "Key insight:", "Note:",
"Important:" or other heading-style labels — just say the thing.
Comments state constraints the code can't show, never why a change
is correct or what the next line does.

## Public Module Style

- Public-facing modules are crafted API-first: a clean, ergonomic
  export surface, modeled on how `Core.*` is written — `Core.*` is
  the exemplar for naming, ordering, and what earns a public name;
  docs/styleguide.md codifies the mechanics.
- Literate prose in a module is sound documentation of its
  adjacent code block — what it states, why it exists, the
  constraints the code can't show — never process narration,
  session history, or exploratory commentary.
- No testing or probing artifacts in public modules: killchecks
  and probative tests live exclusively in `Test/` (wired into
  `All` when they must run with the build; see the Test/ rules)
  and are promoted to `Gloss.*` if and when appropriate.

## Import and Placement Discipline

- Import the narrowest submodule that provides what you use — not
  the aggregator.
- Proofs about a type's properties belong in that type's own
  `*.Properties`/`*.Impl.*` module, never an unrelated collector.
- No ad-hoc submodule aliases diverging from the namespace:
  `as Nat`, not `as NatP`.
- Generally-applicable lemmas never live in `private` blocks of
  consuming modules — if another module could plausibly need it,
  it belongs in the matching `Core.*` module; create it there
  first, then import.

## Mechanization Discipline

Every definitional reduction a proof leans on is pinned as a
named, present-tense `killcheck-<name> = refl` witness (the
reduction stated as its own type) in an untimestamped Test/
regression file imported by `All`, so a reduction that stops
firing fails the next `just check-all` — killchecks and probative
tests never live in the public modules themselves. Exemplar
`src/Test/CodepCoherentKillchecks.lagda.md`
(`killcheck-apPost`/`killcheck-apPre = refl`, which record the
reductions θ-core relies on). A route that should close but provably
does not is banked as a WALL transcribing the verbatim refl-probe
goal at the stuck hole (`Gloss.EightFieldWall`), never dropped
silently. When a settled spike graduates to a `Gloss.*` certificate
it is frozen self-contained modulo `Core`, each needed `Cat.*`
definition inlined `Frozen from <Module> @ <commit>`, re-typechecked
against CURRENT `Core` before landing (never copy-forward on faith —
a stale certificate rots silently), and landed in the same change as
its `docs/gloss.md` 🧪 entry so the ledger↔certificate bijection
holds. Details: `src/Gloss/CLAUDE.md`.

## Representability-First Style (Cat.*)

`Cat.Codep` (the hcategory records) is the canonical development.
Its method, which new Cat.* work follows:

- Operations are emb-images: composition, units, and actions are
  extracted as **centers of contractible fibers** (`compose-contr`
  and its relatives), never posited as raw data when a
  representability axiom can generate them.
- State coherences where they live — in the contractible fiber —
  then project with `ap fst`. Parallel paths inside one
  contractible fiber are identified for free
  (`is-contr→is-prop`/`is-set`); the free/paid boundary is whether
  all vertices share one fiber (docs/gloss.md T4 vs T5).
- Derived laws are record-internal; provenance facts that certify
  a minimal hypothesis set are standalone hypothesis-explicit
  lemmas (the `*-from-coupling` pattern).
- h-level decomposition for fibered constructions: path-level
  obligations (h-level 0, reversed singletons) go to
  `SinglP-contr`; morphism-level obligations (h-level 1,
  composition fibers) go to `compose-contr`/`emb-image-contr`.
  Σ-reassociate to separate the two, then discharge independently.
- Naming semantics for the actions: pre/post name the position of
  the **represented morphism** (the agent) in the sequential
  composite — "the action of `g` precomposing on `b`", never
  "`g` postcomposed by `b`". Escalate to Lane before coining or
  renaming anything in this family.
- Pre-refactor modules (`Cat.Type`, `Cat.Base`, `Cat.Virtual`,
  `Cat.Coherence`) use the older composite-witness style; follow
  their local idiom when editing them, but do not export it into
  new work. They are slated for rebase-or-retire at THE REFACTOR
  (docs/roadmap.md target 3, which owns the plan and its gates).

## Ternary-First Composition (Core.*)

When composing three or more paths, use `pcom` — do not chain
binary `_∙_` unless the lemma is specifically about binary
composition (the pentagon/triangle type formers use `_∙_` because
that IS the statement).

- `pcom (sym p) q r` is the native 3-fold composition; `_∙_` =
  `pcom refl` is derived.
- `pcom.ap` distributes `ap f` over `pcom` in one step; prefer it
  to chained `ap-comp`.
- Proof-internal chains (`where` clauses, fiber witnesses) use
  `pcom`; type-level statements use `_∙_` when canonical.
- Measured exception: coherence-tower fiber witnesses born by
  iterated lifting are binary right-nested — that is a verified
  optimum, not a violation (docs/gloss.md T20).
