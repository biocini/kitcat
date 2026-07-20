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

- **Opener** (ruled 2026-07-14, superseding the 2026-07-13
  prose-header ruling): a leading YAML frontmatter block, then the
  first fence, OPTIONS pragma, blank line, `module … where`. Three
  registers, cleanly separated. **(1) frontmatter** — a `---` …
  `---` block at the very top, machine-readable metadata; required
  core `author` (string), `date` (`YYYY-MM`), `contents` (string),
  and any further keys tolerated unenforced (`tags`, `status`,
  `updated`, …) — that tolerance is the extensibility. **(2) the
  `contents:` tagline** — one plain line naming the module's content
  (structured and indexable; it replaces the old prose content
  sentence). **(3) synopsis prose** — optional documentation prose
  below the frontmatter, blank-line-separated, rendered as the
  docs-page intro; omit it for small modules.
  `src/Core/Path/Base.lagda.md:1-5` is the exemplar (frontmatter,
  blank, fence — no synopsis); `src/Core/Kan.lagda.md:1-6` shows the
  post-fence body shape. The frontmatter rule is uniform across
  tracked `src/` — library modules, `Gloss.*` certificates, and
  untimestamped `Test/` regression witnesses alike; timestamped
  `Test/` scratch is exempt. Everything before the first fence is
  ignored by Agda, so the block never affects the typecheck. A
  tolerant canary (`just lint frontmatter`) validates the core
  where a block is present, and frontmatter lines carry a 100-char
  width soft cap (`bin/lint`, wider than the 72 prose limit — a
  `contents:` tagline is one unwrappable line); the tree-wide
  conversion of the header-less and prose-header files is
  docs/roadmap.md target 6.
- **Pragma tracks the stratum**: default
  `--safe --erased-cubical --no-guardedness`; pure-MLTT foundation
  leaves use `--cubical-compatible`
  (`src/Core/Data/Nat/Base.lagda.md:5`); `--cubical` only where
  Glue is required, with the deviation justified in the opening
  prose (`src/Core/Univalence.lagda.md:3-8`). Ruled 2026-07-13: no
  flag redundant with the global `kitcat.agda-lib` set appears in
  a per-module pragma (the sporadic `--no-sized-types` lines are a
  scheduled cleanup).
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
  free letter); `φ` face formulas; `A B C` types. Levels (ruled
  2026-07-13): `u v w` for `Level`; `ℓ` is reserved for
  interval-indexed levels `ℓ : I → Level`
  (`src/Core/Base.lagda.md:33-34`). Core's `ℓ ℓ'`-for-`Level`
  minority sites are baseline, not precedent. In `Cat.*`, the
  domain names `o` (object level) and `h` (hom level) are
  sanctioned for category-shaped records (ruled 2026-07-13);
  auxiliary levels there follow the general rule.

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
- **Cubical-native proofs as a rule** (Lane, 2026-07-13): for path
  lemmas and path algebra — in `Core.*` especially, and ideally in
  any proof — prefer cubical-native proofs over J-based ones
  whenever feasible: the `Core.Kan` hcom/com infrastructure, an
  interval filler, a connection, or a definitional boundary fact
  (e.g. `sym (sym p) ≡ p` holds by `refl` cubically) beats a
  `J`-induction stating the same thing. Cubical-native proofs have
  strictly better computational behavior in cubical type theory —
  they compute where J-transports stick — and read closer to the
  geometry. The cubical-reasoning reference is the Bentzen entry
  (`resources/bentzen-naive-cubical/`), vendored for exactly this;
  `J` remains legitimate where no native route exists or the
  native route is materially worse.
- **Generic lemmas are extracted, never re-derived in place**
  (Lane, 2026-07-13, sharpening the Import and Placement
  Discipline for the proof pipeline): a generally-applicable lemma
  discovered mid-proof — path algebra, transport facts, reusable
  helpers — is landed in its matching `Core.*` module and imported,
  never left as a local re-derivation in the consuming module, a
  spike, or a Gloss certificate. The coder owns the extraction;
  the accuracy and mechanical reviews own catching a missed one.
  **Every Core addition passes a redundancy check first** (Lane,
  2026-07-13): search `Core.*` for an existing form — by type
  shape and by the naming grammar — before landing anything; a
  candidate that is beta-eta equal to an existing function is the
  wrapper defect (Hard Rules), and a candidate that holds
  DEFINITIONALLY in cubical (e.g. `sym (sym p) ≡ p` is `refl`)
  earns no lemma at all — use sites write the definitional form.
  Core is the stable API; additions are deliberate, deduplicated,
  and named per the grammar, never accreted.
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
- **Implicit universe parameters are earned by inference** (ruled
  2026-07-13): a `Level` parameter is implicit exactly when a
  later explicit argument's type determines it by unification
  (`ob : Type o` determines `o`); a universe occurring only in
  field types — or only in the record's own sort — is not
  inferable at type formation and is declared explicit. Core
  already practices this: `hMap (u : Level) {v} (X : Type v)`
  makes the field-only `u` explicit and infers `v` from `X`
  (`src/Core/Function/Partial/Fiber.lagda.md:39`). The ruling's
  exemplar is `category-structure {o} (h : Level) (ob : Type o)`
  (`src/Cat/Type.lagda.md`), corrected from an implicit `h`
  every use site had to brace-feed. A definition body that
  happens to solve the meta (a copattern clause pinning the
  field's level) is not inference — the signature must stand
  alone.

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
- **Width**: 72 prose / 100 code (code width raised from 85, ruled
  by Lane 2026-07-20), enforced on new and changed lines
  (`just lint changed`). The baseline is being driven down
  deliberately and is not license for new over-width lines.
- **Unicode is purposeful**: notation freely (`∂`, `⌞_⌟`,
  `Σ x ∶ A , B` — `∶` is U+2236), subscripts for corner variables,
  with spelled aliases for discoverability.
- `ind` is the canonical name for hand-rolled eliminators, inside
  the type's module scope.

## Performance

Coding guidance for typechecking performance in cubical Agda.
The through-line: conversion cost is governed by which terms the
checker treats as neutral, and the durable fix is structural — a
construction whose types keep conversion syntactic — never a seal
bolted onto a construction that leaks. The code below is
schematic: `Fib` is any family with `Fib-prop : ∀ c → is-prop
(Fib c)`, `Over` any family indexed by `Fib`-values, `_●_` any
operation with heavyweight implicit arguments. (Provenance: the
2026-07-20 optimization pass,
`notes/2026-07-20-displayed-triangle.md`, all norms
profile-verified.)

**Seal values that families ride; boundaries survive sealing.**
`opaque` keeps a body out of conversion, but a path's endpoints
still reduce, because `PathP` boundaries are type-directed: the
checker reads them off the stated type, not the body. So a proof
of an identification in a propositional fiber — a value consumers
only transport along, or index type families by at generic
interval points — is a good seal:

```agda
opaque
  σ : u ≡ v                     -- u v : Fib c
  σ = Fib-prop c u v

thread : PathP (λ i → Over (σ i)) u' v'   -- σ i stays neutral;
thread = …                                -- σ i0 ≐ u, σ i1 ≐ v
                                          -- by the type alone
```

Families over `σ` compare as neutral applications instead of
normalizing the `hcomp`/`transp` interior of `Fib-prop`'s body.
Corollary: sealing is useless when the *statement* leaks. A path
between paths whose declared face is itself a transparent proof
term hands that term to every family through boundary reduction,
seal or no seal (measured: no change):

```agda
opaque
  sq : Fib-prop c u v ≡ e   -- the i0 face is the transparent
  sq = …                    -- term: sq i0 ≐ Fib-prop c u v by
                            -- boundary reduction, so families
                            -- over sq normalize the body anyway
```

The fix is structural, not another seal — state the square
against the sealed face, so every face a family can extract is
neutral:

```agda
opaque
  sq : σ ≡ e
  sq = …
```

**Generalize over the path; do not `unfolding` to re-type.** The
scenario: a lemma proved over a canonical path (typically the
propositional-fiber identification) is needed over a sealed path
with the same endpoints. Re-checking the lemma inside `opaque
unfolding` makes the conversion normalize the seal's body at
every such site (seconds each, measured):

```agda
opaque
  unfolding σ                             -- misfactored: pays a
  threadᴰ : PathP (λ i → Over (σ i)) u' v'  -- full conversion
  threadᴰ = thread-canonical u' v'          -- against σ's body
```

Instead parameterize the lemma by the path — when the family is
pointwise propositional or contractible, the proof goes through
for an arbitrary path unchanged — and recover the canonical form
as an instance:

```agda
opaque
  thread[_] : (p : u ≡ v) → ∀ u' v' → PathP (λ i → Over (p i)) u' v'
  thread[ p ] u' v' =
    is-prop→PathP (λ i → Over-prop (p i)) u' v'

thread-canonical = thread[ Fib-prop c u v ]   -- the instance
threadᴰ          = thread[ σ ]                -- no unfolding: p
                                              -- is consumed as a
                                              -- neutral family
```

Reserve `opaque unfolding` for proofs that genuinely compute
through a body; if a block's only purpose is re-typing, the
abstraction is misfactored.

**Name the faces of ascribed fills.** A term that appears both in
a definition's type ascription and in its body — the usual shape
when a square-filling combinator's face is written inline as a
lambda — is elaborated twice, and the two elaborations are
compared by full structural conversion, re-solving the face's
implicit arguments each time:

```agda
face : PathP (λ m → PathP (λ i → B m i) b₀ b₁)
             top (λ i → w i ● n)          -- inline face: once in
face = is-prop→SquareP B-prop             -- the type…
         top refl (λ i → w i ● n) refl    -- …and again here
```

Binding the face to its own named, type-ascribed definition
elaborates it once; every later occurrence is compared by name:

```agda
bot : PathP (λ i → B i1 i) b₀ b₁
bot i = w i ● n

face : PathP (λ m → PathP (λ i → B m i) b₀ b₁) top bot
face = is-prop→SquareP B-prop top refl bot refl
```

Measured 14× on a face whose implicits carry fibered witness
structure. Faces whose terms are small elaborate cheaply either
way and may stay inline — profile before churning. Side faces
count the same as bottoms: an η-wrapped reversal of a named line
(`λ m → ρ (~ m)`) is still an inline face, elaborated in the
ascription and again in the fill (measured 240 ms → 37 ms + two
~30 ms named sides, and see the attribution norm below).

**Keep Kan fillers out of head position.** If a composition
operation plugs its left operand in head position — `(β ▿ α) γ =
β (… α …)` — then a filler slid into the β slot is an `hcom`
applied at function type: every conversion pushes the argument
into each face of the filler. In the α slot the same filler is
compared as a subterm. Measured on mirror whiskers of the same
slide: fill-left 74 ms against fill-right 23 ms, rising to
450 ms when the slid path is an `∙`-chain rather than a record
field. When the construction leaves a mirror choice, whisker
fills on the argument side; when the endpoints force the
orientation, accept the cost — naming the filled operand and
generalizing the whisker into a combinator both measured null.

**Project the propositionality path; do not transport by J.**
When the goal equates `fst`-shadows of proofs in a propositional
fiber and the operation in play preserves `fst` definitionally,
whisker the fiber's propositionality path by the operation and
project, instead of doing J on an endpoint:

```agda
slide-shadow : ∀ U V e
             → shadow (U ↝ e) (V ↝ e) ≡ shadow U V
slide-shadow U V e =
  sym (shadow-lc (λ i → Fib-prop c U V i ↝ e))
  -- not: J (λ _ e' → …) (…) — the J-form re-elaborates the
  -- family at the transported index (measured 278 → 169 ms at a
  -- two-sided family; the projection form is also J-free)
```

**Argument-position nesting is not the same disease.** A term
that occurs once, as an argument, with its expected type
propagated from the head's signature, pays its endpoint
conversions exactly once:

```agda
glue = comp-pathp F p (q ∙ r) P    -- the nested glue occurs
         (comp-pathp F q r Q R)    -- once; naming its sub-terms
                                   -- only redistributes cost
```

Naming sub-terms here measured slightly *worse* (the same
endpoint conversions, plus the ascriptions). Do not churn these.

**Profile, then keep only what pays.**

```sh
rm _build/<ver>/agda/src/Some/Module.agdai   # touch does not
agda --profile=definitions src/Some/Module.lagda.md   # invalidate
```

`--profile=definitions` attributes elaboration time per
definition. Every seal and every naming is justified by a
before/after profile; an experiment that moves nothing is
reverted, not kept on principle.

Two rules for reading the numbers. A conversion is billed to the
definition that first forces it, not to the one that owns it: an
inline face in a later fill re-bills the re-elaboration of the
lines it applies to those lines themselves (a slide read 264 ms
until the fill's sides were named; it then read 74 ms with no
change of its own), and fixing a hotspot can surface a new one
downstream that is the same conserved work under a new account.
So per-definition numbers rank suspects, but only the module
`Total` over repeated cold runs confirms a fix — totals here are
stable to ~1% between runs while individual attributions
reshuffle freely. And `Miscellaneous` is not import overhead:
the import floor is just deserialization (~0.3 s here, measured
by cold-checking a trivial module with the same imports); the
rest is the module's own signature elaboration, section
application, occurs checks, record positivity, and interface
serialization — `--profile=internal` decomposes it.

## Rulings

Ruled by Lane, 2026-07-14: the `.lagda.md` opener is a YAML
frontmatter block — required core `author` / `date` (`YYYY-MM`) /
`contents`, unknown keys tolerated, optional synopsis prose,
uniform across tracked `src/` (timestamped `Test/` scratch
exempt). This supersedes the 2026-07-13 "author/date headers
standard" ruling (the two-plain-lines format). See the Opener norm
above; the canary is `just lint frontmatter`, and the tree-wide
conversion sweep is docs/roadmap.md target 6.

Ruled by Lane, 2026-07-13 (now stated as norms above, with their
conformance sweeps scheduled in docs/roadmap.md Housekeeping): no
globally-redundant per-module flags; `u v w` for `Level` with `ℓ`
reserved for `I → Level`; the ternary-first conformance sweep over
Core's legacy `∙`-chains is GO; the WIP-module probe sections
migrate to `Test/` per Public Module Style; implicit universe
parameters are earned by inference (the category-structure
correction).

Still open (Core splits — flagged, not legislated):

1. Fixity before vs after the definition (or bless both).

Provenance: distilled from
`notes/research/2026-07-13-core-styleguide-survey.md` (analyzer
norms survey; every convention cited there at file:line with
NORM/TENDENCY/INCONSISTENCY grades and re-runnable sweep counts).
