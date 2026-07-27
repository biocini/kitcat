# W-types

Operational reference for W-types `W (x:A). B(x)`: well-founded tree types,
the single type former that subsumes all ordinary inductive types. Digested
from Rijke, *Introduction to HoTT*, §"General inductive types".
Prerequisites: inductive-types.md, identity-types.md (`tr`, path induction),
fundamental-theorem.md (the proof method), funext.md and equivalences.md
(used throughout), univalence.md (multisets, Russell's paradox).

**Axiom warning.** This chapter sits *after* function extensionality and
univalence in the book; every result depending on them is flagged
**[funext]** / **[univalence]** below. Formation, the constructor, the
induction principle with its judgmental computation rule, the η-equivalence
and the emptiness criterion are pure MLTT. Nearly every *identity-type*
statement needs funext.

A W-type is specified by a type `A` of **symbols** (names of constructors)
and a family `B` over `A` giving each constructor's **arity** — the type
indexing its recursive arguments. Where an ordinary inductive type has
finitely many constructors of finite arity, a W-type has a *type* of
constructors whose arities are *types*. Elements are **well-founded trees**:
a node labelled `x : A` with a `B(x)`-indexed family of subtrees;
well-foundedness (no infinite descent) is exactly what induction expresses.

## Key definitions

### Formation, constructor, induction

For a family `B` over `A`, the W-type `W(A,B)` (also `W (x:A). B(x)`) is
the inductive type with one constructor

  sup : Π (x:A). (B(x) → W(A,B)) → W(A,B).

Read `sup x α` as "the tree with symbol `x` and subtree `α y` at `y : B(x)`".
Rijke prints the constructor as `tree` (source macro `\collect`); `sup` is
the traditional name, used here. He warns the supremum intuition is
misleading: `sup x α` has no supremum properties.

**Induction principle.** For any family `P` over `W(A,B)`, any step

  h : Π (x:A). Π (α : B(x) → W(A,B)). (Π (y:B(x)). P (α y)) → P (sup x α)

determines `ind-W h : Π (w:W(A,B)). P w` with **judgmental** computation
rule `ind-W h (sup x α) ≡ h x α (λy. ind-W h (α y))`. Pattern-matching
display `f (sup x α) := h x α (λy. f (α y))` exhibits the computation rule
directly. The inductive hypothesis gives `P` at *every* immediate subtree.

### Symbol, arity, components (all by recursion)

- `symbol : W(A,B) → A`, `symbol (sup x α) := x`;
  `arity : W(A,B) → 𝒰`, `arity (sup x α) := B(x)`;
  `component : Π (w:W(A,B)). arity w → W(A,B)`,
  `component (sup x α) := α`.
- **Constants**: for `x : A` with `h : B(x) → 𝟘`, the tree
  `cₓ(h) := sup (x, ex-falso ∘ h)` has no subtrees;
  `is-constant-W w := is-empty (B (arity w))`. Distinct symbols may have
  *equivalent* arities `B(x) ≃ B(y)` — symbols aren't recoverable from
  arities.

### Observational equality Eq-W (A and each B(x) in 𝒰)

  Eq-W (sup x α, sup y β) := Σ (p : x = y). Π (z:B(x)). α z = β (tr B p z)

Reflexivity: `refl-Eq-W (sup x α) := (refl x, refl-htpy α)`.

### Functorial action, elementhood, extensionality

- **Functoriality**: for `f : A' → A` and a family of **equivalences**
  `eₓ : B'(x) ≃ B(f x)`, define `W(f,e) : W(A',B') → W(A,B)` by
  `W(f,e) (sup x α) := sup (f x, W(f,e) ∘ α ∘ eₓ⁻¹)`.
- **Elementhood** (type-valued, not proposition-valued):
  `(x ∈ sup (a, α)) := Σ (y:B(a)). α y = x` — judgmentally `fib α x`.
- `W(A,B)` is **extensional** if
  `(x = y) → Π (z:W(A,B)). (z ∈ x) ≃ (z ∈ y)` is an equivalence for all
  `x y` (trees determined by their elements) — a defined *property*, not
  to be confused with the Eq-W characterization (see Pitfalls).
- A family `B` over `A` is **univalent** if
  `tr B : (x = y) → (B x ≃ B y)` is an equivalence for all `x y` —
  equivalently `B : A → 𝒰` is an embedding (`B` is the canonical family
  of a subuniverse).

### Multisets

For a universe `𝒰` with universal family `Ty`, `𝕄 𝒰 := W(𝒰, Ty)` is the
type of **multisets** (Aczel; Gylterud): "sets" with type-valued,
multiplicitous membership. Notation `{f(x) | x : A} := sup (A, f)`; its
**cardinality** is the type `A`, its **elements** the `f x`. Membership:
`(X ∈ {g(y) | y:B}) := Σ (y:B). g y = X`. Smallness:
`is-small-𝒰 A := Σ (X:𝒰). A ≃ X`; `{f(x)|x:A}` is **𝒰-small** if `A` is
𝒰-small and each `f x` is (recursively). **Universal tree** ("Yggdrasil"):
`Y-𝒰 := {i(X) | X : 𝕄 𝒰}` in `𝒰⁺`.

### Polynomial endofunctor (exercise; Awodey–Gambino–Sojakova)

`P_{A,B}(X) := Σ (x:A). X^(B(x))`, on maps `P_{A,B}(h)(x,α) := (x, h ∘ α)`.
A `P_{A,B}`-**algebra** is `(X, μ : P_{A,B}(X) → X)`; a **homomorphism** is
`Σ (h : X → Y). h ∘ μ_X ~ μ_Y ∘ P_{A,B}(h)`. `W(A,B)` is an algebra via
`ε (x,α) := sup x α`.

### Rank relations (exercise)

`(sup(a,α) ≼ sup(b,β)) := ∀ (x:B(a)). ∃ (y:B(b)). α x ≼ β y` and
`(x ≺ y) := ∃ (z ∈ y). x ≼ z`. `≼` is proposition-valued (truncated `∃`);
its poset reflection is the **rank poset** `ℛ(A,B)`.

## Key results

### The η-equivalence (axiom-free)

`η : W(A,B) → Σ (x:A). (B(x) → W(A,B))`, `η w := (symbol w, component w)`
is an equivalence, inverse `ε (x,α) := sup x α`; both homotopies hold
judgmentally on constructor forms (`η (sup x α) ≡ (x, α)`). Hence
axiom-free: `(sup x α = sup y β) ≃ ((x , α) = (y , β))` in the Σ-type.
What bare MLTT *cannot* do is reduce that to pointwise data — see Eq-W.

### Emptiness criterion (axiom-free)

Equivalent: (i) `Π (x:A). ¬¬(B x)`; (ii) `is-empty (W(A,B))`. (i)⇒(ii):
W-induction with motive `𝟘`; the step type is judgmentally
`Π (x:A). (B(x) → W(A,B)) → ¬¬(B x)`. (ii)⇒(i): from `h : B(x) → 𝟘` build
`cₓ(h)`. Moral: a W-type needs symbols of empty arity to get started; all
arities inhabited ⇒ empty W-type.

### ℕ as a W-type **[funext]**

With `P : bool → 𝒰`, `P false := 𝟘`, `P true := 𝟏` : `W(bool, P) ≃ ℕ`.
Derived constructors `z := sup (false, ex-falso)`,
`s x := sup (true, const x)`. `f : ℕ → N` by ℕ-recursion (`f 0 ≡ z`,
`f (succ n) ≡ s (f n)`); inverse `g` by W-induction:
`g (sup (false,α)) := 0`, `g (sup (true,α)) := succ (g (α ⋆))`.
`g (f n) = n` by ℕ-induction on judgmental computations; `f (g w) = w` by
W-induction, needing `ex-falso = α` (`α : 𝟘 → N`) and `const (α ⋆) = α`
(`α : 𝟏 → N`) — both **funext** (η for functions out of 𝟘, 𝟏).

Same pattern (one symbol per constructor, arity = recursive-argument type):
**oriented binary rooted trees** (`B false := 𝟘`, `B true := bool`);
**unoriented binary rooted trees** (`A := 𝟏 + BS₂`, `BS₂` the type of
2-element types, `B (inl x) := 𝟘`, `B (inr X) := X` — subtrees modulo
permutation); **oriented finitely branching trees** `W(ℕ, Fin)`;
**unoriented** ones `W(𝔽, 𝒯)`, `𝔽` the type of finite types. Lists etc.
follow the same pattern (not worked out in this section).

### Characterization of the identity type **[funext]**

**Theorem.** The canonical map `(x = y) → Eq-W (x,y)` (from reflexivity)
is an equivalence for all `x y`:

  (sup x α = sup y β) ≃ Σ (p : x = y). Π (z:B(x)). α z = β (tr B p z)
                      = Σ (p : x = y). α ~ β ∘ tr B p.

Proof: fundamental theorem — show `Σ (y:W(A,B)). Eq-W (x,y)` contractible
with center `(x, refl-Eq-W x)`; the contraction is by W-induction on `y`,
path induction on `p : x = y`, then **homotopy induction** on
`H : α ~ β` — an equivalent form of funext, hence the flag. Without funext
Eq-W is still reflexive and the map exists; it is not known to be an
equivalence. When `A` is a **set** every `p : x = x` is `refl`, so it
collapses to `(sup x α = sup x β) ≃ (α ~ β) ≃ (α = β)` — sup genuinely
injective up to homotopy (covers ℕ, bool, the ordinary encodings).

### Truncation levels **[funext]**

**Theorem.** If `A` is a `(k+1)`-type then so is `W(A,B)` — *no hypothesis
on `B`*. Proof: W-induction on both arguments; via Eq-W the identity type
is a Σ of the `k`-type `a = b` and a Π of `k`-types (IH). Corollaries:
`A` a set ⇒ `W(A,B)` a set; `A` a proposition ⇒ `W(A,B)` a proposition.

### Functorial action on fibers **[funext]**

**Lemma.** `fib W(f,e) (sup x α) ≃ fib f x × Π (b:B(x)). fib W(f,e) (α b)`.
Proof: rewrite the fiber via Eq-W, rearrange Σ, reindex along `eₓ`, finish
by distributivity of Π over Σ (choice — itself funext).

**Theorem.** If `f` is `k`-truncated, so is `W(f,e)`; in particular `f` an
equivalence (resp. embedding) ⇒ `W(f,e)` an equivalence (resp. embedding).
Recursive `k`-truncatedness of fibers via the lemma.

### Elementhood induction **[funext]**

**Theorem (∈-induction).** From
`h : Π (x:W(A,B)). (Π (y:W(A,B)). (y ∈ x) → P y) → P x` obtain
`i h : Π (x:W(A,B)). P x` with an *identification*
`i h x = h x (λy. λe. i h y)`. Construction: with
`□P x := Π y. (y ∈ x) → P y`, define `i'` into `□P` by pattern matching
(`i' h (sup a f) (f b) (b, refl) := h (f b) (i' h (f b))`), set
`i h x := h x (i' h x)`; the computation rule uses `eq-htpy` twice —
propositional, funext-flagged.

### Extensional W-types **[funext]**

**Theorem.** For an **inhabited** `W(A,B)`, equivalent:

1. `W(A,B)` is extensional (equality determined by membership).
2. `B` is a univalent family (`tr B : (x = y) → (B x ≃ B y)` an
   equivalence; `B : A → 𝒰` an embedding).

Proof sketch: by the fundamental theorem, extensionality ⇔ contractibility
of `Σ (y:W(A,B)). Π z. (z ∈ x) ≃ (z ∈ y)`; membership is a fiber, so this
becomes `Σ (b:A). Σ (β : B(b) → W). Π z. fib α z ≃ fib β z`, which
(families-of-equivalences exercise) is
`Σ (y:A). Σ (e : B x ≃ B y). α ~ e ∘ β`; the `Σ β. α ~ e ∘ β` part is a
fiber of the equivalence `β ↦ e ∘ β`, hence contractible, leaving
contractibility of `Σ (y:A). B x ≃ B y` — exactly "B univalent"
(fundamental theorem again). Inhabitedness: from `w : W(A,B)` form
`sup (x, const w)` with symbol `x`.

- **Vacuity**: empty W-types are vacuously extensional with `B` arbitrary
  (e.g. all `B x` inhabited) — inhabitedness is essential.
- **Examples**: ℕ-as-W-type, unoriented binary and finitely branching
  trees are extensional; the **oriented** versions are not (`[S,T]` and
  `[T,S]` have the same elements but are distinct). Minimal non-example:
  `A := 𝟏 + bool`, `B (inl _) := 𝟘`, `B (inr _) := 𝟏` — two unary
  constructors; `sup (inr false, const w)` and `sup (inr true, const w)`
  contain exactly the same `w` yet are distinct.

### Multisets and Russell's paradox **[univalence]**

- `𝕄 𝒰` is extensional: `Ty` is a univalent family exactly by univalence.
- For 𝒰-small multisets `X Y` in a univalent `𝒱`: `X = Y` and `X ∈ Y` are
  𝒰-small **[univalence]** (by induction via Eq-W; `A = B ≃ (A ≃ B)`).
- The inclusion `i : (Σ (X : 𝕄 𝒱). is-small-𝕄-𝒰 X) → 𝕄 𝒰`,
  `i({f(x)|x:A}) := {i(f(e⁻¹ y)) | y : B}` for the given `e : A ≃ B`,
  is an embedding; `i(X)` is 𝒱-small; `(i X ∈ Y) ≃ (X ∈ i Y)`.
- 𝒱-small types are closed under W-formation (via the functorial action).
- **Theorem (Russell).** A univalent universe `𝒰` is not 𝒰-small: no
  `U : 𝒰` with `𝒰 ≃ U`. Proof: assuming smallness, `Y-𝒰` is 𝒰-small, so
  the Russell multiset `R := {i(X) | X : 𝕄 𝒰, X ∉ X}` is 𝒰-small
  (comprehension preserves smallness; `X ∈ X` is small); take `R'` with
  `i R' = R`. Then `R ∈ R ≃ Σ X. (X ∉ X) × (i X = R)`
  `≃ Σ X. (X ∉ X) × (X = R')` (i embedding) `≃ R' ∉ R' ≃ R ∉ R`, and no
  type is logically equivalent to its own negation. ∎ Companion: no
  surjection `𝒰 ↠ U` either.

### W-types as initial algebras (exercise)

`(W(A,B), ε)` is the **homotopy-initial** `P_{A,B}`-algebra: for every
algebra `(X, μ)`, `hom ((W(A,B), ε), (X, μ))` is contractible. Needed
identity characterizations: `((x,α) = (y,β)) ≃ Σ (p:x=y). α ~ β ∘ tr B p`
in `P_{A,B}(X)` (Σ + funext), and an analogous one for homomorphisms.
**Moral: the W-induction principle *is* initiality; computation rules are
the homomorphism squares.**

### Exercises worth citing

- Each `B x` empty ⇒ `W(A,B) ≃ A` (only constants).
- `∈` is irreflexive on every W-type (second proof that `𝒰 ≄ U : 𝒰`).
- The strict order `<` generated by `(x ∈ y) → (x < y)` and
  `(y ∈ z) → (x < y) → (x < z)` is transitive, irreflexive; (for inhabited
  `W(A,B)` with some inhabited `B a`) `<` proposition-valued iff `∈` is
  iff `A` a set and all `B a` propositions. Satisfies **strong induction**
  (assume `P y` for all `y < x`); **no descending sequences**: no
  `x : ℕ → W(A,B)` with `x (n+1) < x n` — literal well-foundedness.
- Rank: `≼` a preorder; `(ℛ(A,B), ≺)` a well-founded, extensional strict
  order; each `B x` finite ⇒ `ℛ(A,B)` is empty, a singleton, or `(ℕ, ≤)`.

## Reasoning idioms

- **To prove `Π (w:W(A,B)). P w`**: W-induction on the `sup` constructor —
  fix `x : A`, `α : B(x) → W(A,B)`, IH `Π (y:B(x)). P (α y)`; prove
  `P (sup x α)`. Recursion = constant motive. The computation rule is
  judgmental: functions unfold on `sup` for free — check definitional
  simplification before proving.
- **To exhibit an element of `W(A,B)`**: find `x : A` with `h : B x → 𝟘`
  and use the constant `cₓ(h)`. To *use* `w : W(A,B)` when every `B x` is
  `¬¬`: W-induction toward `𝟘` (emptiness criterion).
- **To identify two trees** `sup x α = sup y β` **[funext]**: supply
  `p : x = y` plus `Π (z:B(x)). α z = β (tr B p z)` (`p := refl` when
  symbols agree). To *use* a tree path, project the Eq-W data. This one
  equivalence replaces both injectivity and disjointness of constructors:
  distinct symbols are separated by `¬(x = y)` in `A`.
- **To prove `W(A,B)` truncated**: only `A` matters. W-induct on both
  arguments and rewrite the goal identity type via Eq-W.
- **To show a tree map is an equivalence/embedding**: present it as
  `W(f,e)` and prove it of `f`; truncatedness passes through the
  functorial action via the fiber lemma.
- **To encode an ordinary inductive type as a W-type**: one symbol per
  constructor; arity `𝟘` for constants, `𝟏` unary, `bool` binary, `Fin n`
  for `n`-ary. Map out by ordinary induction, back by W-induction; one
  triangle is typically judgmental, the other needs funext (η for
  functions out of finite arities).
- **Membership is a fiber**: use `e : x ∈ sup(a,α)` by destructuring to
  `(y , p) : Σ (y:B(a)). α y = x`; prove it by exhibiting `y` with
  `α y = x` (often `refl`).
- **∈-induction (course-of-values)**: to prove `P x`, assume `P y` for all
  `y ∈ x` — use when the immediate-subtree IH is too weak. Its computation
  rule is only propositional.
- **Multiset notation** for `W(𝒰, Ty)`: write `{f(x) | x : A}`, argue with
  cardinality (= indexing type) and membership (= fibers); use univalence
  to identify multisets via componentwise correspondences.

## Pitfalls

- **sup injectivity is not a bare-MLTT theorem in usable form.**
  Axiom-free, `η` an equivalence gives
  `(sup x α = sup y β) ≃ Σ (p : x = y). tr (λx. B x → W(A,B)) p α = β` —
  but the second component is an *identity between functions*, which bare
  MLTT cannot convert to or from pointwise data in the useful direction.
  In particular, without funext you **cannot construct**
  `sup x α = sup x β` from a homotopy `α ~ β`: trees with
  pointwise-identical components may be unidentifiable. The clean
  characterization `≃ Σ (p : x = y). α ~ β ∘ tr B p` **needs funext**
  (homotopy induction in the proof). Flag **[funext]** on Eq-W and all
  downstream results (truncation, fiber lemma — also uses choice —
  functorial truncatedness).
- **Even with funext, tree identities carry symbol-path data.** Eq-W is a
  Σ over *all* `p : x = y`, including nontrivial `p : x = x` (this is
  exactly how unoriented/multiset structure arises). Only for `A` a set
  does it collapse to `α ~ β`; don't write
  `sup x α = sup x β ≃ (α ~ β)` otherwise.
- **"Extensional W-type" ≠ the Eq-W characterization.** Extensionality
  (membership determines equality) holds for inhabited W-types iff `B` is
  univalent — not automatic. Distinct symbols with equivalent arities
  break it (two unary constructors; `[S,T]` vs `[T,S]`); empty W-types are
  vacuously extensional. Never conclude `x = y` from "same elements"
  without verifying `B` univalent.
- **Membership is type-valued.** `x ∈ y` is a Σ/fiber, not a proposition —
  hence *multi*sets. Proposition-valued membership needs `A` a set and
  `B a` propositions. Irreflexivity holds regardless.
- **The ∈-induction computation rule is propositional** (via `eq-htpy`),
  unlike the judgmental W-computation rule; don't chain definitional
  unfoldings off it.
- **Emptiness criterion has double negation on the left**:
  `(Π x. ¬¬B x) ↔ is-empty (W(A,B))`. Empty arities *populate* the type;
  inhabited arities everywhere make it empty.
- **Functoriality needs equivalences on arities.** W-formation is
  contravariant in the arity (precomposition with `eₓ⁻¹`); a mere map
  `B'(x) → B(f x)` induces nothing.
- **η-equivalence ≠ η-rule.** No judgmental `w ≡ sup (symbol w) (component
  w)` is postulated for arbitrary `w`; that identification for variables
  is propositional, by W-induction.
- **Universe discipline for multisets.** `𝕄 𝒰` lives in `𝒰⁺`;
  `is-small-𝕄-𝒰` is *data* (chosen equivalences); extensionality of `𝕄 𝒰`
  and smallness of `X = Y`, `X ∈ Y` rest on **[univalence]** — hence so
  does Russell's theorem.
- **Initiality is homotopy initiality**: contractibility of the
  homomorphism type, proved with funext-level machinery — not a strict
  universal property.
- **W-types do not subsume everything.** No path constructors (circle,
  quotients, truncations — circle.md, quotients.md); no inductive
  families, inductive–inductive or inductive–recursive definitions. Given
  funext, all *ordinary* inductive types reduce to W — that is why
  W-types matter.

## See also

- dependent-type-theory.md — Π/Σ/λ-calculus substrate.
- inductive-types.md — the ordinary inductive types W-types subsume; same
  four-rule pattern.
- identity-types.md — `tr`, path induction, homotopy algebra.
- equivalences.md — embeddings, fibers, truncated maps; `η` an equivalence.
- fundamental-theorem.md — contractible-total-space method behind the Eq-W
  and extensionality theorems.
- funext.md — the axiom flagged throughout; homotopy induction; choice
  (Π-over-Σ) in the fiber lemma.
- truncation-levels.md — `W(A,B)` inherits `A`'s truncation level.
- universes.md — universal family `Ty`, smallness; `𝕄 𝒰` one universe up.
- univalence.md — makes `Ty` univalent, hence `𝕄 𝒰` extensional; Russell's
  theorem that `𝒰` is not 𝒰-small.
- logic-truncation.md — `∃`/`∀` in rank relations; `¬¬` in emptiness.
- finite-types.md — `Fin k`, `BS₂`, `𝔽`: finitely branching trees.
- quotients.md — poset reflection (rank poset); beyond W-types' reach.
- number-theory.md — strong induction on ℕ, analogue of ∈-induction.
- groups.md — `BS₂` as 2-element types / automorphisms of `bool`.
- circle.md — higher inductive types: constructors W-types cannot express.
