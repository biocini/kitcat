# Function extensionality

Function extensionality is the axiom that characterizes identity types of
Π-types: for `f g : Π (x:A). B(x)`, the canonical map
`htpy-eq : (f = g) → (f ~ g)` is an equivalence. In words: two functions are
identical iff they are homotopic: functions can only be distinguished by
their values. This is the *only* identity-type characterization in the book
not provable in bare Martin-Löf type theory — it is assumed as an axiom, on
par with (and in fact a consequence of) univalence. Flag every use in
informal proofs.

Why an axiom is needed (the neg-bool example): `neg-bool : bool → bool` is
defined by bool-induction, and bool-induction also constructs

  neg-neg-bool : Π (b : bool). neg-bool(neg-bool b) = b

(with `neg-neg-bool true := refl true`, `neg-neg-bool false := refl false`),
i.e. a homotopy `neg-bool ∘ neg-bool ~ id`. But bare MLTT provides *no rule*
to conclude `neg-bool ∘ neg-bool = id` from this. Pointwise identifications
are constructible by induction on the domain; identifications between
functions are not. Function extensionality closes exactly this gap.

## Key definitions

- **Homotopy**: `f ~ g := Π (x:A). f x = g x` for `f g : Π (x:A). B(x)`. A
  *structure* (a family of identifications), not a property.
- **htpy-eq** (also called `happly`): the canonical map
  `(f = g) → (f ~ g)` defined by path induction from
  `htpy-eq (refl f) := refl-htpy f`. Exists without any axiom.
- **Function extensionality principle at f**: for each
  `g : Π (x:A). B(x)`, the map `htpy-eq : (f = g) → (f ~ g)` is an
  equivalence.
- **The function extensionality axiom**: for every type family `B` over `A`
  and every `f g : Π (x:A). B(x)`, `htpy-eq` is an equivalence. Its inverse
  is written `eq-htpy : (f ~ g) → (f = g)`. Added to the theory as a rule:
  from `Γ ⊢ f g : Π (x:A). B(x)` conclude `Γ ⊢ funext : is-equiv (htpy-eq)`.
- **Weak function extensionality**: for every family `B` over `A`,
  `(Π (x:A). is-contr (B x)) → is-contr (Π (x:A). B x)` — a dependent
  product of contractible types is contractible.
- **Homotopy induction**: for any family `P(g, H)` over `g` and `H : f ~ g`,
  the evaluation map `s ↦ s(f, refl-htpy f)` of type
  `(Π (g : Π (x:A). B(x)). Π (H : f ~ g). P(g, H)) → P(f, refl-htpy f)`
  has a section.

## Key results

### Equivalent forms of funext

For a fixed `f : Π (x:A). B(x)`, the following are equivalent — this is a
direct instance of the fundamental theorem of identity types:

1. Function extensionality holds at `f` (htpy-eq is a family of equivalences).
2. The total space `Σ (g : Π (x:A). B(x)). f ~ g` is contractible.
3. Homotopy induction holds at `f`.

Per universe 𝒰: the function extensionality principle holds in 𝒰 iff the
weak function extensionality principle holds in 𝒰.

Proof of funext ⇒ weak funext: given centers `c x` and contractions `C x`,
take `c := λx. c x` as center of `Π (x:A). B x`; the contraction `c = f` is
obtained by applying eq-htpy to the homotopy `λx. C x (f x) : c ~ f`.

Proof of weak funext ⇒ funext: by (2) above it suffices to show
`Σ (g : Π (x:A). B x). f ~ g` contractible. It is a retract of
`Π (x:A). Σ (b : B x). f x = b` via `i := λ(g,H). λx. (g x , H x)` and
`r := λp. (λx. pr₁ (p x) , λx. pr₂ (p x))`; `r ∘ i` is *judgmentally* the
identity by the η-rules for Σ and Π. The latter type is a product of
contractible singletons, hence contractible by weak funext; retracts of
contractible types are contractible.

### Closure of k-types under Π (uses funext)

**Theorem.** For any family `B` over `A` and any `k ≥ −2`:

  (Π (x:A). is-trunc k (B x)) → is-trunc k (Π (x:A). B x).

Proof: induction on `k`. Base case `k = −2` is exactly weak funext. Inductive
step: to show `Π (x:A). B x` is `(k+1)`-truncated, show `f = g` is
`k`-truncated for all `f g`; by funext `f = g ≃ f ~ g`, and
`f ~ g := Π (x:A). f x = g x` is a Π of `k`-truncated types, hence
`k`-truncated by the inductive hypothesis; `k`-types are closed under
equivalence. **This is the standard way to prove a Π-type is truncated:
reduce to the fibers.**

- **Corollary.** If `B` is a `k`-type then `A → B` is a `k`-type for any `A`.
- **Corollary.** `¬A := A → 𝟘` is a proposition for every type `A` — and this
  needs funext *even when A is already a proposition*.

### Distributivity of Π over Σ ("type-theoretic choice", uses funext)

**Theorem.** For `C(x, y)` over `x : A` and `y : B x`, the map

  choice : (Π (x:A). Σ (y : B x). C(x, y)) → Σ (f : Π (x:A). B x). Π (x:A). C(x, f x)

given by `choice h := (λx. pr₁ (h x) , λx. pr₂ (h x))` is an equivalence.

The inverse is `choice⁻¹ (f, g) := λx. (f x , g x)`. One triangle identity is
*judgmental* (`choice (choice⁻¹ (f, g)) ≡ (f, g)` by the η-rule for Π), but
the other is not: `(pr₁ (h x) , pr₂ (h x)) ≢ h x` judgmentally, so
`choice⁻¹ ∘ choice ~ id` is constructed by funext applied to
`λx. eq-pair (refl , refl)`.

Consequences:

- `(A → Σ (y:B). C y) ≃ Σ (f : A → B). Π (x:A). C (f x)`.
- `Π (b:B). fib f b ≃ Σ (g : B → A). f ∘ g ~ id` for `f : A → B`.
- **Dependent functions are sections of projections:**
  `sec (pr₁) := Σ (h : A → Σ (x:A). B x). pr₁ ∘ h ~ id ≃ Π (x:A). B x`
  (proved by choice + Σ-swap + contractibility of
  `Σ (f : A → A). f ~ id`).

### Identity systems on Π-types (links funext to the fundamental theorem)

**Theorem.** Let `B` be a family over `A`, and for each `b : B a` let `E(b)`
be an identity system at `b`. Then for any `f : Π (x:A). B x`,
`g ↦ Π (x:A). E(f x, g x)` is an identity system at `f`. Proof: by the
fundamental theorem it suffices that
`Σ (g : Π (x:A). B x). Π (x:A). E(f x, g x)` be contractible; by choice this
is `Π (x:A). Σ (y : B x). E(f x, y)`, a product of contractible types,
contractible by weak funext.

This is the abstract machine behind the slogan "identifications of functions
are homotopies": taking `E` to be the identity type itself recovers funext;
taking other `E` yields custom characterizations.

### Universal properties (use funext for the inverse homotopies)

- **Dependent universal property of Σ** (currying): the map

    ev-pair : (Π (z : Σ (x:A). B x). C z) → Π (x:A). Π (y : B x). C(x, y)

  given by `f ↦ λx. λy. f (x , y)` is an equivalence; its inverse is the
  induction principle of Σ. The section homotopy is judgmental
  (`refl-htpy`); the retraction homotopy uses funext (twice) plus
  Σ-induction. Corollary: `(A × B → X) ≃ (A → (B → X))`.
- **Dependent universal property of identity types** (type-theoretic Yoneda
  lemma): for `B(x, p)` over `x : A` and `p : a = x`, the map

    ev-refl : (Π (x:A). Π (p : a = x). B(x, p)) → B(a, refl a)

  given by `f ↦ f (a , refl a)` is an equivalence; its inverse is based path
  induction. One homotopy is the computation rule of path induction; the
  other uses funext twice, then path induction on `p`.
- Left as exercises (same pattern): universal properties of `𝟘`
  (`is-empty A` iff `Π (x:A). P x` is contractible for all `P`), of `𝟏`
  (`is-contr A` iff evaluation at a point is an equivalence), of coproducts
  (`(A + B → X) ≃ (A → X) × (B → X)`), and of `ℕ`
  (`Σ (h : ℕ → X). (h 0 = x) × (h ∘ succ ~ f ∘ h)` is contractible).

### Precomposition with an equivalence (uses funext)

**Theorem.** For `f : A → B`, the following are equivalent:

1. `f` is an equivalence.
2. For every family `P` over `B`, the precomposition map
   `− ∘ f : (Π (y:B). P y) → Π (x:A). P (f x)` is an equivalence.
3. For every type `X`, `− ∘ f : (B → X) → (A → X)` is an equivalence.

(1)⇒(2): use that equivalences are coherently invertible
`(g, G : f ∘ g ~ id, H : g ∘ f ~ id, K : G · f ~ f · H)`; the inverse of
precomposition is `φ h := λy. tr P (G y) (h (g y))`, and both homotopies are
constructed with funext (one needs `K` plus `tr P (ap f p) ~ tr (P ∘ f) p`
and `apd h`). (2)⇒(3) is the constant family. (3)⇒(1): the fibers of
`− ∘ f` are contractible; at `X := A` the fiber over `id` yields a
retraction `h` of `f`; at `X := B` the fiber over `f` contains both
`(id , refl f)` and `(f ∘ h , p)`, so contractibility gives `id = f ∘ h`.

### Strong induction for ℕ (computation rules need funext)

**Theorem.** Given `p₀ : P 0` and
`p_S : Π (n : ℕ). (Π (m : ℕ). (m ≤ n) → P m) → P (n+1)`, there is

  strong-ind-ℕ (p₀, p_S) : Π (n : ℕ). P n

with computation rules (propositional):

  strong-ind-ℕ (p₀, p_S, 0)   = p₀
  strong-ind-ℕ (p₀, p_S, n+1) = p_S (n , λm. λp. strong-ind-ℕ (p₀, p_S, m)).

Construction (from ordinary induction): set
`P̃ n := Π (m : ℕ). (m ≤ n) → P m`. Build `p̃₀ : P̃ 0` and
`p̃_S : Π (n:ℕ). P̃ n → P̃ (n+1)` — the latter via the equivalence
`(m ≤ n+1) ≃ (m ≤ n) + (m = n+1)` and case analysis, using that `≤` is
proposition-valued. Ordinary ℕ-induction yields `s̃ : Π (n:ℕ). P̃ n`; define
`strong-ind-ℕ (p₀, p_S, n) := s̃ n n (refl-≤ n)`.

**Where funext enters:** the zero computation rule is judgmental. For the
successor rule, one reduces to showing
`s̃ n = λm. λp. s̃ m m (refl-≤ m)` — an identification of *functions* — which
is proved by funext followed by induction on `n`. Without funext the strong
induction principle would have no computation rule.

### Homotopy algebra and propositions from the exercises

- `inv-htpy : (f ~ g) → (g ~ f)`, `concat-htpy H : (g ~ h) → (f ~ h)`, and
  `concat-htpy' K : (f ~ g) → (f ~ h)` are all equivalences (via funext).
- `is-contr A` and `is-trunc k A` are propositions (uses funext).
- If `f` is an equivalence, its types of sections and of retractions are
  contractible; hence `is-equiv f` is a proposition, and for
  `e e' : A ≃ B` the canonical map `(e = e') → (e ~ e')` is an equivalence.
  Also `A ≃ B` is a `k`-type when `A` and `B` are.
- `is-equiv f ≃ path-split f ≃ is-coh-invertible f` (all are propositions).
- Postcomposition: `f : A → B` is `k`-truncated iff
  `f ∘ − : (X → A) → (X → B)` is `k`-truncated for every `X`; in particular
  `f` is an equivalence (resp. embedding) iff `f ∘ −` is.

## Reasoning idioms

- **To identify two functions** `f = g`: construct a homotopy
  `H : Π (x:A). f x = g x` (usually by induction on `x`), then apply
  `eq-htpy H`. State: "by function extensionality it suffices to show
  `f x = g x` for arbitrary `x : A`."
- **To use an identification** `p : f = g`: apply `htpy-eq p : f ~ g` and
  instantiate at a point. This direction is axiom-free.
- **To show `Π (x:A). B x` is contractible**: show each `B x` contractible
  and cite weak funext. The center is `λx. c x`; the contraction needs
  eq-htpy — do not pretend it is judgmental.
- **To show `Π (x:A). B x` is k-truncated / a proposition / a set**: reduce
  to the fibers via trunc-closure of Π. For `is-prop` goals of the form
  `Π (x:A). B x` this is the default first move.
- **To characterize the identity type of a Π-type**: answer "`f = g` is
  equivalent to `f ~ g`" (funext), or more generally build a pointwise
  identity system `Π (x:A). E(f x, g x)` and prove its total space
  contractible via choice + weak funext (fundamental-theorem method).
- **To prove a universal property** (an equivalence between function types):
  exhibit the inverse explicitly; one triangle often holds judgmentally by
  η/computation rules, the other typically requires funext plus induction on
  the source type. Check which homotopies are judgmental first.
- **To precompose with an equivalence** `e : A ≃ B`: freely replace
  `Π (y:B). P y` by `Π (x:A). P (e x)`; transport `tr P (G y)` mediates the
  inverse direction.
- **To lift an induction principle to its strong form**: apply ordinary
  induction to the family `P̃ n := Π (m ≤ n). P m`, then specialize at the
  reflexivity proof; expect to need funext for the computation rules.
- **Flag the axiom**: in informal proofs write "(by function
  extensionality)" at each use. A proof avoiding funext is strictly more
  informative.

## Pitfalls

- **Funext is not automatic.** It is independent of MLTT: `f ~ g` can be
  inhabited while `f = g` is unprovable without the axiom (neg-bool example).
  Never slide from "for all x, f x = g x" to "f = g" without citing funext.
- **Homotopy is data; identity is (via the axiom) equivalent data.**
  `H : f ~ g` is a family of identifications you can use pointwise directly;
  `p : f = g` only becomes usable pointwise through `htpy-eq`. Keep the two
  types distinct in your head even though they are equivalent.
- **η-rule ≠ funext.** The η-rule is judgmental: `f ≡ λx. f x`, identifying
  a function with its own η-expansion *by definition*; no axiom. Funext is
  propositional and identifies *two different definitions* agreeing on all
  inputs. Do not cite η when identifying `f` with `g`.
- **Σ has no judgmental η in this setup.** `(pr₁ z , pr₂ z) ≢ z`; only
  `eq-pair (refl , refl) : (pr₁ z , pr₂ z) = z` holds. This is exactly why
  the choice equivalence needs funext for one of its two homotopies.
- **Computation rules obtained via funext are propositional, never
  judgmental.** E.g. the strong-induction computation rules are
  identifications, not definitional unfoldings; anything defined through a
  funext-mediated uniqueness principle will not compute definitionally. Do
  not chain further judgmental simplifications off them.
- **`¬A` is a proposition — but only with funext.** Even `¬P` for `P` a
  proposition needs it, since the goal is a Π-type into 𝟘. Truncation-level
  goals whose *goal type* is a Π-type are funext-dependent almost by default.
- **Weak funext looks trivial but isn't.** From "every `B x` is contractible"
  you cannot *define* the contraction of `Π (x:A). B x` in bare MLTT; the
  contraction is an identification between functions and hence needs
  eq-htpy.
- **Orientation of the equivalence.** `htpy-eq : (f = g) → (f ~ g)` (apply,
  then instantiate); `eq-htpy : (f ~ g) → (f = g)` (the constructive
  direction used in proofs). Mixing them up inverts your proof.
- **Funext for functions ≠ univalence for types.** Don't reach for
  univalence when the goal is an identification of functions; don't reach
  for funext when the goal is an identification of types.

## See also

- `identity-types.md` — path induction, `refl-htpy`, groupoid laws used in
  homotopy algebra.
- `fundamental-theorem.md` — the three-way equivalence (family of
  equivalences / contractible total space / induction principle) behind the
  equivalent forms of funext; identity systems.
- `equivalences.md` — homotopies as sameness of maps; coherent
  invertibility (precomposition), retracts of contractible types.
- `truncation-levels.md` — `is-trunc k`, closure of k-types under Π;
  `is-equiv` / `is-contr` are propositions.
- `dependent-type-theory.md` — Π-types, λ-abstraction, the judgmental
  η-rule contrasted with funext.
- `inductive-types.md` — bool-induction (neg-bool), Σ-induction, ordinary
  ℕ-induction (input to strong induction); `w-types.md` for other
  extensionality principles.
- `universes.md` — universe-indexed statements of the axioms.
- `univalence.md` — implies funext; the other axiom characterizing an
  identity type (of 𝒰 rather than of Π).
- `logic-truncation.md` — `¬A` is a proposition; propositions-as-types
  reasoning depends on funext at every turn.
- `number-theory.md` — strong/ordinal induction on ℕ in practice; `≤` as a
  proposition-valued family.
- `quotients.md`, `finite-types.md`, `groups.md`, `circle.md` — downstream
  consumers: universal properties, isomorphisms of sets vs equivalences, and
  HIT universal properties all assume funext.
