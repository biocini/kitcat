# Kitcat

A research library at the intersection of higher category theory,
homotopy type theory, and programming language foundations, with
machine-checked proof as its standard of evidence. API unstable.

## Guidelines

`docs/guidelines/` carries the development knowledge, by topic. Read
what the task calls for. [The index](docs/guidelines/README.md) maps
them.

| Doing | Read |
| --- | --- |
| Writing a module | [module-anatomy](docs/guidelines/module-anatomy.md), [naming](docs/guidelines/naming.md), [prose-and-comments](docs/guidelines/prose-and-comments.md), [api-surface](docs/guidelines/api-surface.md) |
| Writing proofs | [definitions-and-proofs](docs/guidelines/definitions-and-proofs.md), [records](docs/guidelines/records.md) |
| Designing a signature | [elaboration](docs/guidelines/elaboration.md) on implicit vs explicit, before a parameterized module or an edge-indexed API |
| Chasing typecheck time | [profiling](docs/guidelines/profiling.md) first, then [performance](docs/guidelines/performance.md) |
| Asking if a question is settled | [rulings](docs/guidelines/rulings.md) |

Style law, for code: match the local idiom of the module you edit.
`Core.*` is the exemplar, and the guidelines codify its mechanics.
Escalate style questions. Do not improvise.

Style law, for prose: the `writing` skill is normative and outranks
local pattern. Where existing prose deviates from the skill, the
deviation is debt to fix (tracked in `TODO.md`), never idiom to
match. [prose-and-comments](docs/guidelines/prose-and-comments.md)
states the scope.

## Build

Per-module pragma, the default stratum:

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}
```

Variants: `--cubical-compatible` for pure-MLTT foundation leaves, and
`--cubical` only where Glue is required. Justify the deviation in the
module's opening prose. No flag redundant with the global set appears
in a per-module pragma.

Global flags live in `kitcat.agda-lib`: `--no-import-sorts`,
`--no-sized-types`, `--erasure`, `--auto-inline`, `--erased-matches`,
`--exact-split`, `--hidden-argument-puns`, `--postfix-projections`,
`--qualified-instances`, `-Werror`, `-WnoUnsupportedIndexedMatch`.

Dependencies: Agda builtins only. No agda-stdlib, no cubical library.

## Namespaces

| Namespace | Purpose |
| --- | --- |
| `Core.*` | Foundational primitives (stable, core API) |
| `Data.*` | Concrete data types and their properties |
| `HData.*` | Higher inductive types |
| `Cat.*` | Category theory |
| `Lib.*` | Extended developments |
| `Bb.*` | Blackboard: archived strata, frozen green |
| `Test.*` | Scratch and regression witnesses (gate-exempt) |

`just stats` gives live inventories. Do not keep static tables.

## Tooling

`just --list` shows every recipe. `bin/` is on PATH via `.envrc`.

| Command | What it does |
| --- | --- |
| `just check <Mod>` | Typecheck one module (dot-path or file path) |
| `just check-tree [dir]` | Typecheck every module under a directory, listing failures |
| `just profile <Mod>` | Elaboration time, cold (`--total [N]`, `--internal`, `--warm`) |
| `just mv Old New [--dry-run]` | Move or rename, updating references |
| `just lint [width\|flags\|authoring\|frontmatter\|citations\|changed]` | Lint. `changed` is the pre-commit gate. `citations` checks that every module a ledger names still exists. The `writing` skill's bundled linter gates prose, not this |
| `just resources-verify [--remote]` | Custody check on `resources/` |

Use the tools, not raw invocations. Before a commit, run `just lint
changed` and `just check <Mod>` on every touched module. The `just mv`
reference sweep covers `src/` only. Hand-check `docs/` citations after
you move a cited module.

## Delegation

Subagent tiers, by task shape:

| Task | Tier |
| --- | --- |
| Tree surgery with an exact procedure: `just mv` sweeps, citation re-points, vendoring with a verification ladder | Sonnet |
| Read-only inventory, comparison, and provenance forensics (analysis pass first, mutation as a separate pass) | Sonnet |
| Process and documentation design: READMEs with sourced provenance, policy files, literate indexes | Opus |
| Novel formalization against the checker | The strongest tier available. The brief matters more than the tier |

A brief that works has these parts:

- On disk, in `outputs/.plans/`.
- Exact signatures and record shapes, with `file:line` anchors.
- Prior artifacts listed as mandatory inputs.
- A reading budget before the first edit.
- A green checker run as the gate for each stage.
- A 300-second bound per checker run. A longer run is a hang
  signal (the implicit-argument trap).
- Two attempts per search and per resisting lemma, then move on.
- The verification ladder, as exact commands.

The known failure mode is an unbudgeted exploration phase that
produces no code.

Sequencing: one writer per tree. `Bb/index.lagda.md` and the
per-tree changelogs are contention points, so tree-creating agents
run serially, with analysis passes read-only beside them. A killed
agent resumes by message. A resume is not proof of restored
context: verify before you rely on it, and inventory an agent's
artifacts before any stop.

## Hard rules

- **Zero warnings.** `-Werror` is global. Exit 42 is failure. Fix
  warnings. Never add `-W` suppression without explicit
  authorization. `InlineNoExactSplit` means use copatterns, not
  constructor application. `UselessPrivate` means no `private`
  inside `where`.
- **No postulates, no `TERMINATING`, no unsafe features** without
  explicit authorization. Library modules are `--safe`.
- **No external library imports.**
- **Never truncate homs.** Categories here are wild by design. Do
  not pursue or assume hom-set conditions. This is a working
  constraint, not an aesthetic one: see the op-involution regress,
  `docs/gloss.md` T12.
- **Commit only when Lane says to commit.**

## Documents

- `docs/roadmap.md`: the projects and their gates, in intended
  order. Read it for what the repository works toward.
- `docs/gloss.md`: the theorem ledger. Statement, location, status,
  date.
- `docs/provenance.md`: honesty and citation standards. Binding.
  VERIFIED means machine-checked here (name the module).
  SOURCE-CHECKED means the opened document states the claim.
  Literature claims are CONJECTURED.
- `.euler/TOOLCHAIN.md`: the toolchain block. Check commands,
  obligation and unsafe-marker tokens, library layout. Field
  contract in `.claude/TOOLCHAIN.example.md`.
- `outputs/`, `papers/`: research and formalization reports with
  `.provenance.md` sidecars, and paper-style drafts. The euler
  workflows produce them (`.claude/` commands, skills, agents).
  Their contract is `.claude/rules/euler.md`.
- `TODO.md`: repo-level maintenance tasks.
- `notes/`: session logs (`<date>-<slug>.md`).
- `resources/`: vetted sources, cited by entry.
  `resources/README.md` is the format authority.
