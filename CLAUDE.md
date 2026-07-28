# Kitcat — Cubical Agda Library

A research library at the intersection of higher category theory,
homotopy type theory, and programming language foundations, with
machine-checked proof as its standard of evidence. API unstable.

## Guidelines

`docs/guidelines/` carries the development knowledge, by topic. Read
what the task calls for; [the index](docs/guidelines/README.md) maps
them.

| Doing | Read |
| --- | --- |
| Writing a module | [module-anatomy](docs/guidelines/module-anatomy.md), [naming](docs/guidelines/naming.md), [prose-and-comments](docs/guidelines/prose-and-comments.md), [api-surface](docs/guidelines/api-surface.md) |
| Writing proofs | [definitions-and-proofs](docs/guidelines/definitions-and-proofs.md), [records](docs/guidelines/records.md) |
| Designing a signature | [elaboration](docs/guidelines/elaboration.md) — implicit vs explicit, before adding a parameterized module or an edge-indexed API |
| Chasing typecheck time | [profiling](docs/guidelines/profiling.md) first, then [performance](docs/guidelines/performance.md) |
| Wondering if it's settled | [rulings](docs/guidelines/rulings.md) |

Style law: match the local idiom of the module you are editing —
`Core.*` is the exemplar, the guidelines codify its mechanics — and
escalate style questions rather than improvising. Prose follows the
STE register: the `writing` skill is the normative statement, and
[prose-and-comments](docs/guidelines/prose-and-comments.md) states
the scope.

## Build

Per-module pragma, the default stratum:

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}
```

Variants: `--cubical-compatible` for pure-MLTT foundation leaves,
`--cubical` only where Glue is required, with the deviation justified in
the module's opening prose. No flag redundant with the global set
appears in a per-module pragma.

Global flags live in `kitcat.agda-lib`: `--no-import-sorts`,
`--no-sized-types`, `--erasure`, `--auto-inline`, `--erased-matches`,
`--exact-split`, `--hidden-argument-puns`, `--postfix-projections`,
`--qualified-instances`, `-Werror`, `-WnoUnsupportedIndexedMatch`.

Dependencies: Agda builtins only — no agda-stdlib, no cubical library.

## Namespaces

| Namespace | Purpose |
| --- | --- |
| `Core.*` | Foundational primitives (stable, core API) |
| `Data.*` | Concrete data types and their properties |
| `HData.*` | Higher inductive types |
| `Cat.*` | Category theory |
| `Lib.*` | Extended developments |
| `Test.*` | Scratch and regression witnesses (gate-exempt) |

`just stats` for live inventories rather than static tables.

## Tooling

`just --list` shows every recipe; `bin/` is on PATH via `.envrc`.

| Command | What it does |
| --- | --- |
| `just check <Mod>` | Typecheck one module (dot-path or file path) |
| `just check-tree [dir]` | Typecheck every module under a directory, listing failures |
| `just profile <Mod>` | Elaboration time, cold — `--total [N]`, `--internal`, `--warm` |
| `just new <Mod> [--aggregator]` | New module with correct boilerplate |
| `just mv Old New [--dry-run]` | Move/rename, updating references |
| `just lint [width\|flags\|frontmatter\|changed]` | Lint; `changed` is the pre-commit gate. Prose is gated by the `writing` skill's bundled linter, not here |
| `just resources-verify [--remote]` | Custody check on `resources/` |
| `just stats` / `just wip` | Inventories |
| `just html` / `just html-serve` | Docs site |

Use the tools rather than raw invocations. Before committing: `just lint
changed`, and `just check <Mod>` on every touched module. `just mv`'s
reference sweep covers `src/` only — hand-check `docs/` citations after
moving a cited module.

The `All.lagda.md` aggregator is retired pending module-organisation
decisions; `just check-tree` is the whole-library check meanwhile, and
`bin/sync-all` is not to be run.

## Hard rules

- **Zero warnings.** `-Werror` is global; exit 42 is failure. Fix
  warnings, never add `-W` suppression without explicit authorization.
  `InlineNoExactSplit` means use copatterns, not constructor
  application; `UselessPrivate` means no `private` inside `where`.
- **No postulates, no `TERMINATING`, no unsafe features** without
  explicit authorization. Library modules are `--safe`.
- **No external library imports.**
- **Never truncate homs.** Categories here are wild by design; do not
  pursue or assume hom-set conditions. A working constraint, not an aesthetic one — see
  the op-involution regress, `docs/gloss.md` T12.
- **Commit only when Lane says to commit.**

## Documents

- `docs/roadmap.md` — the projects and their gates, in intended order.
  Read for what the repository is working toward.
- `docs/gloss.md` — the theorem ledger: statement, location, status,
  date.
- `docs/provenance.md` — honesty and citation standards. Binding.
  VERIFIED means machine-checked here (name the module); SOURCE-CHECKED
  means the opened document states the claim; literature claims are
  CONJECTURED.
- `.euler/TOOLCHAIN.md` — the toolchain block: check commands,
  obligation and unsafe-marker tokens, library layout. Field contract
  in `.claude/TOOLCHAIN.example.md`.
- `outputs/`, `papers/` — research/formalization reports with
  `.provenance.md` sidecars, and paper-style drafts. Produced by the
  euler workflows (`.claude/` commands, skills, agents); their contract
  is `.claude/rules/euler.md`.
- `notes/` — session logs (`<date>-<slug>.md`).
- `resources/` — vetted sources; cite by entry. `resources/README.md` is
  the format authority.
