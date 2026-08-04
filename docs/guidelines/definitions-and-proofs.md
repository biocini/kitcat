# Definitions and proofs

- **Fixity sits adjacent to the operator**, never in a collected
  block at the top. (Before vs after the definition: Core splits,
  see Open rulings.)
- **INLINE on small combinators and record constructors**:
  definitional one-liners carry `{-# INLINE … #-}` immediately
  after (`src/Core/Type.lagda.md:63-79`). Record constructors get
  `{-# INLINE X.constructor #-}` on the record's exit row.
- **DISPLAY pragmas pin goal readability** wherever a definition
  would print as a raw primitive application. The companion idiom
  names the partial system in a definition-attached module so
  DISPLAY can match it (`src/Core/Kan.lagda.md:55-68`).
- **Copatterns for record values, never constructor application**
  (`⊤-is-contr .center = tt`). This also prevents
  `InlineNoExactSplit` warnings.
- **Projection style**: postfix on values (`e .fst`, `c .paths a
  i`), prefix when the projection acts as a function (`ap fst`).
- **`λ where` for partial systems**, one face per line, aligned.
  The cap/base face tends to come last.
- **Every `where`-helper carries a full type signature** and a
  semantic name. Iso pieces are `fwd/bwd/sec/retr`. Reusable
  definition-scoped internals use a definition-attached
  `module X where` so they stay projectable
  (`src/Core/Kan.lagda.md:639-647`).
- **`private` for proof scaffolding only**. Anything another module
  could plausibly need is public and top-level (or moves to its
  matching `Core.*` home, per Import and Placement Discipline).
- **`@0` on erased type parameters and law fields, never
  operations**. Erased-argument variants get their own names
  (`ap-era`, `J0`).
- **Ternary-first (`pcom`) governs new proof-internal ≥3-fold
  composition** per root CLAUDE.md. Core's older text carries ~112
  binary `∙`-chain sites that predate the ruling. Those are
  baseline, NOT precedent. Do not imitate them in new work.
- **Cubical-native proofs as a rule** (Lane, 2026-07-13): for path
  lemmas and path algebra, in `Core.*` especially and ideally in
  any proof, prefer cubical-native proofs over J-based ones
  whenever feasible. The `Core.Kan` hcom/com infrastructure, an
  interval filler, a connection, or a definitional boundary fact
  (e.g. `sym (sym p) ≡ p` holds by `refl` cubically) beats a
  `J`-induction that states the same thing. Cubical-native proofs
  have strictly better computational behavior in cubical type
  theory (they compute where J-transports stick) and read closer
  to the geometry. The cubical-reasoning reference is the Bentzen
  entry (`resources/bentzen-naive-cubical/`), vendored for exactly
  this. `J` remains legitimate where no native route exists or the
  native route is materially worse.
- **Extract generic lemmas, never re-derive them in place** (Lane,
  2026-07-13, sharpening the Import and Placement Discipline for
  the proof pipeline): a generally-applicable lemma discovered
  mid-proof (path algebra, transport facts, reusable helpers)
  lands in its matching `Core.*` module for import. Never leave it
  as a local re-derivation in the consuming module, a spike, or a
  Gloss certificate. The coder owns the extraction. The accuracy
  and mechanical reviews own catching a missed one.
  **Every Core addition passes a redundancy check first** (Lane,
  2026-07-13): search `Core.*` for an existing form, by type shape
  and by the naming grammar, before landing anything. A candidate
  that is beta-eta equal to an existing function is a duplicate:
  take the existing one, unless the addition presents that
  construction in a vocabulary the development speaks and says so.
  A candidate that holds DEFINITIONALLY in cubical (e.g.
  `sym (sym p) ≡ p` is `refl`) earns no lemma at all: use sites
  write the definitional form. Core is the stable API. Additions
  are deliberate, deduplicated, and named per the grammar, never
  accreted.
- **Signature layout**: short signatures inline. Long ones break
  with the colon opening the continuation and `→` starting
  continuation lines, indented 2.
- **Chain-reasoning blocks** (`Chain`) serve long calculational
  displays only. Everything else composes directly. A proof term
  inside a step's `⟨ ⟩` does not count toward the width cap: let it
  run long rather than break it just to fit.
- Local idiom, permitted not required: `outS do …` low-precedence
  application in the Kan/transport stratum only.
