# Styleguide — the Core.* idiom, codified

The mechanics of the library's style, distilled from a norms survey
of the `Core.*` tree (2026-07-13; 31 of 134 files read in full,
tree-wide sweeps for every count). Root `CLAUDE.md` carries the
law — the Style hard rule, Public Module Style, Comment Style,
Import and Placement Discipline, Ternary-First Composition — and
wins on any conflict; this guide codifies how `Core.*` practices
it, with exemplar citations. Rudimentary by design: the ~24
highest-value conventions for new work, not an exhaustive census.
Where Core itself splits, the split is flagged under Open rulings
at the end — do not invent a rule from a split.

## Module anatomy

- **Opener**: one plain-prose sentence naming the module's content
  (not a heading), blank line, first fence, OPTIONS pragma, blank
  line, `module … where`. (`src/Core/Type.lagda.md:1-6`,
  `src/Core/Kan.lagda.md:1-6`.)
- **Pragma tracks the stratum**: default
  `--safe --erased-cubical --no-guardedness`; pure-MLTT foundation
  leaves use `--cubical-compatible`
  (`src/Core/Data/Nat/Base.lagda.md:5`); `--cubical` only where
  Glue is required, with the deviation justified in the opening
  prose (`src/Core/Univalence.lagda.md:3-8`).
- **Imports**: immediately after the header, one `open import` per
  line, `Core.Type`/`Core.Base` first then rough dependency order.
  Plain opens dominate; `using`-lists where the pull is
  deliberately narrow or a clash exists
  (`src/Core/Function/Embedding.lagda.md:26-28`). Qualified alias =
  the type's own name (`import Core.Data.Nat.Properties as Nat`).
  Builtins are imported and renamed only by the module that owns
  the wrapping (`src/Core/Type.lagda.md:8-17`); fixity may be
  assigned inside the renaming
  (`src/Core/Data/Sigma/Type.lagda.md:13`).
- **Prose and headings**: `##`/`###` only, never `#`; small modules
  (< ~60 lines) use no headings. Section prose states the
  mathematics of the next block; single-sentence fence-splits are
  free. Tree ratio ≈ 1 prose : 3.8 code.
- **Aggregators** contain only pragma, header, re-exports. Three
  shapes: data-type aggregators namespace operations under the
  type's name and export the bare type flat
  (`src/Core/Data/Nat.lagda.md:10-20` — consumers write `Nat.set`,
  `Nat.add.unitr`); stratum aggregators re-export flat, `hiding` to
  resolve collisions (`src/Core/Function.lagda.md:13-24`); a facade
  re-exports a curated selection when a module is the canonical
  door to another's content (`src/Core/Interval.lagda.md:16-22`).

## Naming

- **Kebab-case; capitalization by role**: predicates and proofs
  lowercase (`is-contr`, `left-cancellable`), including predicate
  records (`is-equiv`); bundled structures, classifiers, and traits
  capitalized (`Monoid`, `Lift`, `nType`). No camelCase.
- **Conversion lemmas are `source→target`** with the arrow in the
  name: `is-contr→is-prop`, `iso→equiv`, `path→square`.
- **Law vocabulary is compressed one-token**, trailing `l`/`r` for
  sidedness, no hyphen: `unitl unitr invl invr assoc comm idem
  cancell cancelr zeror`. Composite descriptors hyphenate:
  `ap-comp`, `fiber-comp`, `transport-∙`.
- **Lemma families live in namespace modules; case marks the
  kind**: lowercase modules are operation families
  (`module add` → `Nat.add.unitr`; `module pcom`, `module transp`);
  capitalized modules are type/subject interfaces
  (`module Equiv (e : A ≃ B)`, `module Emb`, `module Path`).
  Members are short names built for qualified access — `set : is-set
  Nat` consumed as `Nat.set`, never re-prefixed (`set`, not
  `nat-set`). The `∂`-namespace for interval combinators
  (`src/Core/Base.lagda.md:73-120`) is the same instinct at the
  symbol level.
- **Instances are `Class-Type`**: `Underlying-Σ`, `Discrete-Nat`;
  superclass fields likewise (`Semigroup-Monoid`).
- **Variables**: `x y z w` elements; `p q r s` paths; `α β` higher
  cells; `i j k l` interval variables (hcom binders take the next
  free letter); `φ` face formulas; `A B C` types. Levels: see Open
  rulings.

## Definitions and proofs

- **Fixity is declared adjacent to the operator** — never a
  collected block at the top. (Before vs after the definition:
  Core splits; see Open rulings.)
- **INLINE on small combinators and record constructors**:
  definitional one-liners carry `{-# INLINE … #-}` immediately
  after (`src/Core/Type.lagda.md:63-79`); record constructors get
  `{-# INLINE X.constructor #-}` on the record's exit row.
- **DISPLAY pragmas pin goal readability** wherever a definition
  would print as a raw primitive application; the companion idiom
  names the partial system in a definition-attached module so
  DISPLAY can match it (`src/Core/Kan.lagda.md:55-68`).
- **Copatterns for record values, never constructor application**
  (`⊤-is-contr .center = tt`) — also load-bearing for
  `InlineNoExactSplit`.
- **Projection style**: postfix on values (`e .fst`, `c .paths a
  i`), prefix when the projection is used as a function (`ap fst`).
- **`λ where` for partial systems**, one face per line, aligned;
  the cap/base face tends to come last.
- **Every `where`-helper carries a full type signature** and a
  semantic name; iso pieces are `fwd/bwd/sec/retr`. Reusable
  definition-scoped internals use a definition-attached
  `module X where` so they stay projectable
  (`src/Core/Kan.lagda.md:639-647`).
- **`private` for proof scaffolding only**; anything another module
  could plausibly need is public and top-level (or moved to its
  matching `Core.*` home, per Import and Placement Discipline).
- **`@0` on erased type parameters and law fields, never
  operations**; erased-argument variants get their own names
  (`ap-era`, `J0`).
- **Ternary-first (`pcom`) governs new proof-internal ≥3-fold
  composition** per root CLAUDE.md. Core's older text carries ~112
  binary `∙`-chain sites predating the ruling: those are baseline,
  NOT precedent — do not imitate them in new work.
- **Signature layout**: short signatures inline; long ones break
  with the colon opening the continuation and `→` starting
  continuation lines, indented 2.
- **Chain-reasoning blocks** (`Chain`) are reserved for long
  calculational displays; everything else composes directly.
- Local idiom, permitted not required: `outS do …` low-precedence
  application in the Kan/transport stratum only.

## Records

- **`no-eta-equality`** on every record except principled
  single-field wrappers where definitional eta is wanted (`Lift`,
  `Irr`, `Fin`, `Instance`) — exactly the CLAUDE.md constraint as
  practiced (43/47).
- **Field order**: superclass instance field, then data, then
  erased (`@0`) laws.
- **Exit row**: `open X public` (traits: `open X ⦃ … ⦄ public`
  hiding superclass fields), then `{-# INLINE X.constructor #-}`.
  Records meant only for qualified access skip the `open`
  (`is-qinv`).
- **Derived members live inside the record body** after `field`;
  consumer-facing projection interfaces are parameterized modules
  beside the type (`module Equiv (e : A ≃ B)`).

## Prose and comments

- **Prose documents the adjacent block** — what it states, the
  idea, the constraint the code can't show — with references made
  at the point of use ("following Rijke §13"; credit comments in
  the house forms per docs/provenance.md "Code citations"). Never
  process narration. (This is Public Module Style, as practiced.)
- **Comment register**: constraints and credit only; no
  `Note:/Key:/Important:/TODO` labels — Core has zero.
- **Probes and holes belong in `Test/`**, never in a public module;
  a WIP module's probe sections move out on promotion (the
  remaining `Core.Path.Composition` probes are scheduled cleanup,
  not precedent).

## API surface

- **What earns a public name**: the type, its operations, reusable
  lemmas, conversions, interface modules. Proof scaffolding,
  single-use fillers, and local abbreviations are `private`.
  Spelled aliases for operator types are public and cheap
  (`Equiv = _≃_`, `Emb = _↪_`) — name-aliases, not re-typed
  primitives.
- **`module _` for shared telescopes** whenever ≥2 definitions
  share one.
- **Instances live in `Impl` modules**, one concern per file, named
  `Class-Type`, re-exported under the type's `impl` namespace by
  the aggregator; inline `instance` blocks only where the instance
  is inseparable from the type.
- **Width**: 72 prose / 85 code, enforced on new and changed lines
  (`just lint changed`). Core itself carries 137 of the tree's 197
  baseline violations — the baseline is being driven down
  deliberately and is not license for new over-width lines.
- **Unicode is purposeful**: notation freely (`∂`, `⌞_⌟`,
  `Σ x ∶ A , B` — `∶` is U+2236), subscripts for corner variables,
  with spelled aliases for discoverability.
- `ind` is the canonical name for hand-rolled eliminators, inside
  the type's module scope.

## Open rulings (Core splits — flagged, not legislated)

1. Author/date headers in the opener: 11 files have them, 123 do
   not.
2. `--no-sized-types` in per-module pragmas (redundant with the
   global flag; present sporadically).
3. Universe-level names: `u v w` (majority) vs `ℓ ℓ'` (strong
   minority); candidate refinement — `u v w` for `Level`, `ℓ`
   reserved for interval-indexed `I → Level` — is currently a
   minority pattern.
4. Fixity before vs after the definition (or bless both).
5. Whether to schedule a ternary-first conformance sweep over
   Core's legacy `∙`-chains.
6. The cleanup path for WIP-module probe sections vs Public Module
   Style.

Provenance: distilled from
`notes/research/2026-07-13-core-styleguide-survey.md` (analyzer
norms survey; every convention cited there at file:line with
NORM/TENDENCY/INCONSISTENCY grades and re-runnable sweep counts).
