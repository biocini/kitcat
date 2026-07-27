# Inductive types

Operational reference for the general schema of inductive types and for the
first examples: `ℕ`, `𝟏`, `𝟘`, `bool`, coproducts `A + B`, dependent pair
types `Σ (x:A). B x`, cartesian products `A × B`, the integers `ℤ`, and
lists. Digested from Rijke, *Introduction to HoTT*, §"The natural numbers"
and §"More inductive types". Prerequisite:
dependent-type-theory.md (judgments, contexts, Π-types, λ-abstraction).
The proofs of equations on `ℕ` previewed here live in identity-types.md.

The one-sentence summary: an inductive type is specified by its
constructors; an induction principle says a (dependent) function out of it
is determined by its values on the constructors; computation rules say
those values are recovered *judgmentally*.

## Key definitions

### The four-rule pattern

Every inductive type `A` comes with four sets of rules:

1. **Formation**: how the type `A` is formed (e.g. `⊢ ℕ type`, no premises).
2. **Introduction** (the *constructors*): the structure `A` comes equipped
   with. Any finite number of constructors is allowed, even zero (`𝟘` has
   none).
3. **Elimination** (the *induction principle*): the data needed to
   construct a section of an arbitrary type family over `A`. The idea is
   always the same: to define `f : Π (x:A). B x`, specify the behaviour of
   `f` at each constructor of `A`. For constructors with recursive
   arguments (like `succ`), the inductive step also receives the values of
   `f` at those arguments.
4. **Computation rules**: one per constructor, asserting that the
   inductively defined section *agrees on the constructors* with the data
   used to define it. These hold **judgmentally** (`≡`).

Two equivalent presentations of an induction principle (shown
interderivable for `ℕ`): as an inference rule with premises for each
constructor, or as a constant/function `ind-A` taking one argument per
constructor-case and returning a section. Rule → function by weakening +
λ-abstraction; function → rule by application. We use the function form.

**Recursion vs induction.** *Induction* is the fully dependent
eliminator: the motive `B` is an arbitrary family over `A`. *Recursion*
is the special case where `B` is a constant family. Use recursion to
*define operations*; use induction to *prove properties*, since a property
of `x : A` is a family depending on `x`.

**Pattern matching.** A definition by induction can be presented by
writing one clause per constructor, e.g. `f 0 := p₀` and
`f (succ n) := pₛ n (f n)`. To recover the official `pₛ`, replace every
occurrence of the recursive call `f n` in the right-hand side by a fresh
variable `x : P n`. The displayed clauses are exactly the computation
rules, hence hold judgmentally — and they are *all* that is known about
the defined function. Proving things about it amounts to finding ways to
apply those judgmental equalities.

### The natural numbers `ℕ`

- Formation: `⊢ ℕ type` (in the empty context).
- Constructors: `0 : ℕ` and `succ : ℕ → ℕ`. (Formally annotated `0_ℕ`,
  `succ_ℕ` — every element has a unique type — but written `0`, `succ`.)
- Induction principle: for any family `P` over `ℕ`,

  `ind-ℕ : P 0 → ((Π (n:ℕ). P n → P (succ n)) → Π (n:ℕ). P n)`

  with **base case** `p₀ : P 0` and **inductive step**
  `pₛ : Π (n:ℕ). P n → P (succ n)`.
- Computation rules (judgmental):
  `ind-ℕ(p₀ , pₛ , 0) ≡ p₀` and
  `ind-ℕ(p₀ , pₛ , succ n) ≡ pₛ n (ind-ℕ(p₀ , pₛ , n))`.

**Addition.** `add : ℕ → (ℕ → ℕ)` is defined by induction on the
**second** argument: in context `m : ℕ`, put `P(n) := ℕ`, base
`add-zero m := m`, step `add-succ m n x := succ x`, i.e.
`add m := ind-ℕ(m , λn. λx. succ x) : ℕ → ℕ`, written `m + n := add m n`.
Judgmental equations (by the computation rules):

- `m + 0 ≡ m`
- `m + succ n ≡ succ (m + n)`
- hence also `n + 1 ≡ succ n` (since `n + 1 ≡ succ (n + 0) ≡ succ n`).

**Not** judgmental, and not derivable judgmentally by any means in the
theory: `0 + n ≡ n` and `succ m + n ≡ succ (m + n)`. These are only
available propositionally (see Key results). The mirror-image convention
(recursion on the first argument) would flip which pair is judgmental;
Rijke's convention is the one above.

**Multiplication** (exercise; standard solution in the same style, again
recursing on the second argument): `mul m 0 := 0` and
`mul m (succ n) := add m (mul m n)`, so judgmentally `m · 0 ≡ 0` and
`m · succ n ≡ m + m · n` (hence `m · 1 ≡ m`). Propositional only:
`0 · n = 0`, `1 · n = n`. The semiring laws of `mul` are an exercise in
the identity-types chapter.

**Further pattern-matching styles**: two-variable matching
(`add'` with four clauses covering `(0,0)`, `(0, succ n)`, `(succ m, 0)`,
`(succ m, succ n)`) and *iterated* matching such as Fibonacci
`F 0 := 0`, `F 1 := 1`, `F (succ (succ n)) := F (succ n) + F n`.
Iterated patterns do not correspond directly to `ind-ℕ`; see Reasoning
idioms.

### The unit type `𝟏`

- Constructor: `⋆ : 𝟏`.
- Induction: for any family `P` over `𝟏`, `ind-𝟏 : P ⋆ → Π (x:𝟏). P x`.
- Computation rule: `ind-𝟏(p , ⋆) ≡ p`. Pattern matching: `f ⋆ := p`.
- Non-dependent case: `ind-𝟏 : A → (𝟏 → A)`; `pt x := ind-𝟏 x : 𝟏 → A`.

### The empty type `𝟘`

- **No constructors**, hence no computation rules.
- Induction: for any family `P` over `𝟘`, `ind-𝟘 : Π (x:𝟘). P x`.
- Non-dependent case: `ex-falso := ind-𝟘 : 𝟘 → A` for any type `A`
  (*ex falso quodlibet* — from a contradiction, conclude anything).
- **Negation**: `¬A := A → 𝟘`, and `is-empty A := A → 𝟘`. A proof of `¬A`
  is a function turning a hypothetical `a : A` into an element of `𝟘`.

### The booleans `bool` (presented as an exercise)

- Constructors: `false : bool`, `true : bool`.
- Induction: `ind-bool : P false → (P true → Π (x:bool). P x)`, with
  judgmental `ind-bool(p₀ , p₁ , false) ≡ p₀`,
  `ind-bool(p₀ , p₁ , true) ≡ p₁`. Pattern matching: two clauses.
- Operations by recursion: `neg-bool false := true`,
  `neg-bool true := false`; `false ∧ y := false`, `true ∧ y := y`; etc.

### Coproducts `A + B`

- Constructors: `inl : A → A + B`, `inr : B → A + B`.
- Induction: for any family `P` over `A + B`,
  `ind-+ : (Π (x:A). P (inl x)) → ((Π (y:B). P (inr y)) → Π (z:A + B). P z)`.
- Computation rules: `ind-+(f , g , inl x) ≡ f x`,
  `ind-+(f , g , inr y) ≡ g y`. Pattern matching: `h (inl x) := f x`,
  `h (inr y) := g y`. Write `[f , g] := ind-+(f , g)`.
- The recursion instance `(A → X) → ((B → X) → (A + B → X))` is the
  elimination rule of disjunction: under propositions-as-types, `+` is
  (untruncated) "or". For the mere disjunction `∨`, see logic-truncation.md.
- **Functorial action**: for `f : A → A'`, `g : B → B'`, define
  `f + g : A + B → A' + B'` by `(f + g)(inl x) := inl (f x)`,
  `(f + g)(inr y) := inr (g y)`.

### Dependent pair types `Σ (x:A). B x`

For a family `B` over `A`:

- Constructor (pairing): `pair : Π (x:A). B x → Σ (y:A). B y`; write
  `(a , b) := pair a b`, where `a : A` and `b : B a` — the type of the
  second component *depends on* the first.
- Induction: for any family `P` over `Σ (x:A). B x`,
  `ind-Σ : (Π (x:A). Π (y:B x). P (x , y)) → Π (z : Σ (x:A). B x). P z`.
- Computation rule: `ind-Σ(g , (x , y)) ≡ g x y`. Pattern matching:
  `f (x , y) := g x y`.
- **Projections**, defined by Σ-induction:
  - `pr₁ : (Σ (x:A). B x) → A`, `pr₁ (x , y) := x` — needs only recursion.
  - `pr₂ : Π (p : Σ (x:A). B x). B (pr₁ p)`, `pr₂ (x , y) := y` — needs
    the *dependent* eliminator, since `B (pr₁ p)` depends on `p`.
  - Both compute on pairs: `pr₁ (a , b) ≡ a`, `pr₂ (a , b) ≡ b`.
- Currying/uncurrying: `ev-pair : (Π (z : Σ (x:A). B x). P z) →
  Π (x:A). Π (y:B x). P (x , y)`, `f ↦ λx. λy. f (x , y)`, is *currying*;
  `ind-Σ` is the converse, *uncurrying*.
- **Cartesian product** = Σ at a constant family: `A × B := Σ (x:A). B`.
  It inherits `ind-×` with `ind-×(g , (x , y)) ≡ g x y`. Under
  propositions-as-types, `×` is conjunction.

To **construct** in `Σ (x:A). B x`, supply a pair `(a , b)` — no
induction. To **use** an arbitrary `z : Σ (x:A). B x`, project (`pr₁`,
`pr₂`) or destructure via `ind-Σ`. There is no judgmental η-rule:
`z ≡ (pr₁ z , pr₂ z)` fails judgmentally (propositional version later).

### The integers `ℤ`

- `ℤ := ℕ + (𝟏 + ℕ)`, with `in-neg := inl : ℕ → ℤ`,
  `in-pos := inr ∘ inr : ℕ → ℤ`, and `-1_ℤ := in-neg 0`,
  `0_ℤ := inr (inl ⋆)`, `1_ℤ := in-pos 0`.
- **Derived** 5-case induction principle (not postulated — proved from
  the principles of `ℕ`, `𝟏`, `+`): to define `f : Π (k:ℤ). P k`, give
  `p₋₁ : P (-1_ℤ)`,
  `p₋ₛ : Π (n:ℕ). P (in-neg n) → P (in-neg (succ n))`, `p₀ : P 0_ℤ`,
  `p₁ : P 1_ℤ`, `pₛ : Π (n:ℕ). P (in-pos n) → P (in-pos (succ n))`;
  clauses `f (-1_ℤ) := p₋₁`,
  `f (in-neg (succ n)) := p₋ₛ n (f (in-neg n))`, etc.
- Example: `succ_ℤ` maps `-1_ℤ ↦ 0_ℤ`, `in-neg (succ n) ↦ in-neg n`,
  `0_ℤ ↦ 1_ℤ`, `1_ℤ ↦ in-pos 1`, `in-pos (succ n) ↦ in-pos (succ (succ n))`.
- Why this pedestrian definition: the classical `ℤ = (ℕ × ℕ)/~` needs
  quotient types, which pure Martin-Löf type theory lacks; see quotients.md.

### Lists `list A` (presented as an exercise)

- Constructors: `nil : list A`, `cons : A → (list A → list A)`.
- Induction (from the general pattern): from `p_nil : P nil` and
  `p_cons : Π (a:A). Π (l : list A). P l → P (cons a l)`, obtain
  `ind-list(p_nil , p_cons) : Π (l : list A). P l` with
  `ind-list(..., nil) ≡ p_nil`,
  `ind-list(..., cons a l) ≡ p_cons a l (ind-list(..., l))`.
- Exercise operations, all by recursion: `fold-list μ : list A → B`
  iterating `μ : A → B → B` over `b : B`; `map-list`, `length-list`,
  `sum-list`, `product-list`, `concat-list`, `flatten-list`,
  `reverse-list`.

## Key results

- **Interderivability** of the rule-style and function-style presentations
  of `ind-ℕ` (and likewise for every inductive type).
- **Judgmental laws of `add`**: `m + 0 ≡ m` and
  `m + succ n ≡ succ (m + n)`; corollary `succ n ≡ n + 1`. These two
  judgmental equalities are *all* the theory knows about `add`; every
  further law is proved by finding a way to apply them.
- **The six laws of addition** (proved in the identity-types chapter;
  stated here to fix the judgmental/propositional boundary):
  - `n + 0 = n` — **judgmental**, so `right-unit-law-add n := refl n`.
  - `m + succ n = succ (m + n)` — **judgmental**, so
    `right-successor-law-add m n := refl (succ (m + n))`.
  - `0 + n = n` — **propositional**, by induction on `n`: base `refl 0`
    (since `0 + 0 ≡ 0`); step `p ↦ ap succ p` (since
    `0 + succ n ≡ succ (0 + n)`). Officially
    `left-unit-law-add n := ind-ℕ(refl 0 , λp. ap succ p)`.
  - `succ m + n = succ (m + n)` — **propositional**, by induction on `n`
    (the recursion argument of `add`, *not* on `m`): base by refl since
    `succ m + 0 ≡ succ m ≡ succ (m + 0)`; step by `ap succ p` after
    computing both sides one layer.
  - `(m + n) + k = m + (n + k)` — **propositional**, by induction on `k`:
    base refl since `(m + n) + 0 ≡ m + n ≡ m + (n + 0)`; step
    `ap succ p` since both sides compute to successors.
  - `m + n = n + m` — **propositional**, by induction on `m`; base uses
    both unit laws, step uses the left successor law and `ap succ p`.
- **Contravariance of negation**: `(P → Q) → (¬Q → ¬P)`, by the term
  `λf. λq̃. λp. q̃ (f p)` — the model exercise in unfolding `¬` as `→ 𝟘`.
- **Cancelling an empty summand**: `is-empty B → ((A + B) → A)`, by
  `ind-+` with `id : A → A` on the left and `ex-falso ∘ b̃ : B → A` on the
  right, where `b̃ : B → 𝟘`. Symmetrically for `is-empty A`.
- **No double negation elimination in general**: no term of `¬¬A → A` is
  constructible from the rules alone. Constructible instead (exercises):
  the double-negation monad (`P → ¬¬P`, `(P → Q) → (¬¬P → ¬¬Q)`,
  `(P → ¬¬Q) → (¬¬P → ¬¬Q)`); DNE for decidable types
  `(P + ¬P) → (¬¬P → P)`; `¬¬` of classical tautologies such as
  `¬¬(P + ¬P)`; stability of `¬P`, `P → ¬¬Q`, `¬¬P × ¬¬Q`;
  `¬¬(P × Q) ↔ ¬¬P × ¬¬Q`; `¬¬(P → Q) ↔ (¬¬P → ¬¬Q)`; `¬(P × ¬P)`;
  `¬(P ↔ ¬P)`.

## Reasoning idioms

- **To define `f : Π (n:ℕ). P n`**: give `f 0 : P 0` and
  `f (succ n) : P (succ n)` in terms of `n` and `f n`; officially
  `ind-ℕ(f 0 , λn. λx. …)`. For an operation `ℕ → A` (recursion), same
  shape with constant `P`; the step has type `ℕ → A → A`.
- **Choose the induction variable so computation rules fire.** `add` and
  `mul` recurse on their *second* argument, so induct on the variable in a
  recursion position of the operations in your goal (on `k` for
  associativity, on `n` for the left successor law). Base cases then often
  close by `refl`, steps by one `ap succ`.
- **Check for judgmental equality before proving.** If both sides of a
  goal `a = b` compute to the same term, the proof is `refl` — half the
  laws of `add` fall this way. Never set up an induction for what is
  really a computation rule.
- **The `ap succ` step**: ℕ-algebra inductive steps almost always reduce,
  after judgmental computation of both sides, to turning `p : a = b` into
  `ap succ p : succ a = succ b`.
- **Two-step recurrences** (Fibonacci, halving rounded down): plain
  `ind-ℕ` only gives the value at the immediate predecessor. Encode via
  pairs: define `G : ℕ → A × A` by induction with `G 0 := (a₀ , a₁)`,
  `G (succ n) := (pr₂ (G n) , step (G n))`, then project. (Rijke's
  Fibonacci exercise.)
- **Eliminator cheat sheet.** Out of `𝟏`: give the value at `⋆`. Out of
  `𝟘`: nothing — `ex-falso`. Out of `bool`: values at `false` and `true`.
  Out of `A + B`: two functions `[f , g]`. Out of `Σ (x:A). B x`: a
  curried function `λx. λy. …` (uncurry). Out of `list A`: the `nil`
  value and the `cons` step.
- **To prove `¬A`**: assume `a : A` and construct an element of `𝟘`
  ("proof of negation"). To *use* `h : ¬A`: apply it to anything of type
  `A`, then finish with `ex-falso`.
- **To use `z : Σ (x:A). B x`**: destructure to `(x , y)` (officially
  `ind-Σ`) or project. Goals about `pr₁ z` for a *variable* `z` do not
  compute; Σ-induction reduces `z` to a pair first. To *construct* in a
  Σ-type: pair a witness with a proof.
- **Tailored induction principles**: a type built from inductive types
  (like `ℤ := ℕ + (𝟏 + ℕ)`) inherits a custom principle by composing the
  component ones. Derive and use it rather than unfolding the
  construction every time.

## Pitfalls

- **`≡` vs `=`**: only constructor computation rules are judgmental.
  `0 + n = n` is a theorem proved by induction; `0 + n ≡ n` is not
  derivable at all. Proofs about an inductive function can only use its
  defining judgmental equalities plus previously proved propositional
  lemmas.
- **Wrong-sided recursion expectations**: with Rijke's `add`, the terms
  `0 + n` and `succ m + n` are stuck — they do not compute. Do not wait
  for them to reduce; prove the left laws by induction. No definition via
  plain `ind-ℕ` makes both `m + 0 ≡ m` and `0 + n ≡ n` judgmental at once.
- **No judgmental η**: for `x : 𝟏` you cannot conclude `x ≡ ⋆`; for
  `z : Σ (x:A). B x` you cannot conclude `z ≡ (pr₁ z , pr₂ z)`. Both hold
  only propositionally, later, by the respective induction principles.
- **Pattern matching is a presentation, not a new rule.** Only
  single-constructor-layer patterns correspond directly to the official
  `ind`; iterated patterns (Fibonacci, division by two) need the pair
  encoding or a derived induction principle.
- **Proof of negation ≠ proof by contradiction.** Deriving `𝟘` from `A`
  proves `¬A`. Concluding `P` from `¬¬P` (DNE) is not valid in general;
  it needs extra input such as decidability `P + ¬P`.
- **Constructors are not yet known to be disjoint.** `inl x ≠ inr y` and
  `0 ≠ succ n` cannot be proved with this chapter's machinery — they need
  identity types plus a universe-valued family distinguishing the
  constructors (fundamental-theorem.md). Do not silently use
  injectivity/disjointness of constructors before that point.
- **`Σ` asserts a chosen witness, not mere existence.** `(a , b) :
  Σ (x:A). B x` picks a specific `a`; "there merely exists" requires the
  truncated `∃` (logic-truncation.md).
- **`pr₂` is genuinely dependent**: its type is `B (pr₁ p)`. Do not type
  it as `Σ (x:A). B x → B` unless the family is constant — and then you
  are really working with `A × B`.
- **`bool` is not a proposition**, and `𝟏`, `𝟘` are not yet known to be
  propositions at this stage; truncation-level facts (`bool`, `ℕ` are
  sets, via Hedberg) come later (truncation-levels.md).
- **Do not postulate computation rules for derived types.** Operations on
  `ℤ` must be defined through its derived 5-case induction principle (as
  `succ_ℤ` is); their defining equations then hold by the computation
  rules of `ℕ`, `𝟏`, and `+`.

## See also

- dependent-type-theory.md — judgments, contexts, Π-types, λ-calculus:
  the rules these inductive specifications plug into.
- identity-types.md — `=`, `refl`, `ap`, path induction; the six laws of
  `add` proved in full; the judgmental/propositional boundary in action.
- universes.md — type families defined by induction (e.g. `Eq-ℕ`),
  needed to distinguish constructors.
- fundamental-theorem.md — `Eq-ℕ`, characterizing `m = n` on ℕ;
  disjointness and injectivity of constructors (`inl`/`inr`, `0`/`succ`).
- truncation-levels.md — `𝟘`, `𝟏` as propositions; `bool`, `ℕ` as sets
  (Hedberg).
- funext.md — identifying inductively defined functions via homotopies.
- logic-truncation.md — `¬`, `¬¬`, decidability; `+` vs `∨`, `Σ` vs `∃`.
- quotients.md — set quotients; the classical `ℤ = (ℕ × ℕ)/~` that the
  coproduct definition here replaces.
- finite-types.md — `Fin k` built from `𝟘`, `𝟏`, and `+`; counting.
- number-theory.md — strong induction, decidability of `ℕ`, arithmetic
  built on this file's operations.
- w-types.md — well-founded trees: one type former subsuming all the
  inductive types in this file.
- circle.md — higher inductive types: the same four-rule pattern plus
  path constructors.
- groups.md — the group structure on `ℤ`; semiring laws of `ℕ` as
  algebraic structure.
