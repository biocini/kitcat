# Performance

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

Second corollary: sealing pays only where a consumer would
otherwise normalize the interior. A square consumed solely by
`fst`-projection at generic interval points, with type-directed
boundaries, measures null under a seal — its attribution is
first-forcer boundary conversion, which the seal cannot move
(measured on the displaced fiber squares).

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

**Name the chain every family rides.** A path composite that
indexes families in more than one type ascription — a fiber's
traversal chain, a glue tree's base composite — is a named
definition, and a displaced module aliases the level-0 name
(`ℓc = Q.ℓc`) instead of re-spelling the composite one level up.
Every inline spelling is elaborated at its site and compared
against its neighbours' by full structural conversion; on the
name, those comparisons short-circuit, and the cross-level
aliases align the displaced boundaries with the level-0
statements by name. This was the displaced hexagon's dominant
cost, not its Kan machinery: 13,723 → 8,628 ms cold in three
confirmed steps (−660 naming the glue subtrees, −2,934 the
level-1 chains, −1,024 the level-0 chains with aliases), and
−456 ms collecting the same move in the pentagon. Chains are
named at level 0 from the start in every new module; the
displaced layer never re-spells them. (Provenance:
`notes/2026-07-20-displaced-optimization.md`, all numbers
median-of-3 cold totals.)

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
Recurrence does not change the diagnosis: a small projection
lambda (`λ i → ŵ i .fst`) repeated across half a dozen fills is
still argument-position — the expected type is elaborated
per-site either way, so the naming saves a five-token term and
pays a signature (measured worse at twelve named shadows per
mirror). The naming norms above are for ascription positions;
what recurs in argument position stays inline.

**Profile, then keep only what pays.** Every seal and every naming
above is justified by a before/after profile, and an experiment that
moves nothing is reverted rather than kept on principle. The commands,
the cold-run discipline, and the three rules for reading an attribution
are in guidelines/profiling.md — read it before acting on any norm here.
