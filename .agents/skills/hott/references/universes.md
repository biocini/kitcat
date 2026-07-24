# Universes

A **universe** is a type 𝒰 whose elements are *codes* for types, equipped with
a **universal type family** Ty that decodes each X : 𝒰 into an actual type
Ty(X), and closed under all the type formers (Π, Σ, identity types,
coproducts, 𝟘, 𝟏, ℕ) by operations on codes satisfying *judgmental*
computation rules. Universes serve two purposes in the book:

1. **Defining type families by induction.** The motive of an induction
   principle may be (constant at) a universe, so recursion into 𝒰 *constructs
   types*. This is how relations on ℕ such as `Eq-ℕ`, `≤`, `<` are defined,
   and it is the engine that proves constructor disjointness (`0 ≠ succ n`)
   and injectivity of `succ` — things recursion into a fixed type cannot do.
2. **Forming types of structured types** — e.g. the type of all groups is a
   Σ-type over a universe (developed in groups.md).

The level discipline is the **enough universes** postulate: never `𝒰 : 𝒰`,
but every finite list of types is contained in some universe; in practice work
with one 𝒰 and pass to 𝒰⁺ only when 𝒰 itself must be treated as a type.

## Key definitions

### Universes and the universal family

**Universe.** A universe is a type 𝒰 in the empty context, equipped with a
type family Ty over 𝒰 (the universal family). For X : 𝒰, read X as an
*encoding* of the type Ty(X); Ty(X) is "the type of elements of X".

**Closure structure.** 𝒰 comes equipped with operations on codes, each with a
*judgmental* decoding equation:

- `Π̌ : Π (X:𝒰). (Ty(X) → 𝒰) → 𝒰` with `Ty(Π̌(X,Y)) ≡ Π (x:Ty(X)). Ty(Y(x))`
- `Σ̌ : Π (X:𝒰). (Ty(X) → 𝒰) → 𝒰` with `Ty(Σ̌(X,Y)) ≡ Σ (x:Ty(X)). Ty(Y(x))`
- `Ǐ : Π (X:𝒰). Ty(X) → Ty(X) → 𝒰` with `Ty(Ǐ(X,x,y)) ≡ (x = y)`
- `∔ : 𝒰 → 𝒰 → 𝒰` with `Ty(X ∔ Y) ≡ Ty(X) + Ty(Y)`
- codes `𝟘̌, 𝟏̌, Ň : 𝒰` with `Ty(𝟘̌) ≡ 𝟘`, `Ty(𝟏̌) ≡ 𝟏`, `Ty(Ň) ≡ ℕ`

Because the equations are `≡`, decoding *computes*: `Ty(Σ̌(X,Y))` reduces, it
is not merely isomorphic to the Σ-type. No separate closure under `A → B` or
`A × B` is needed — they are special cases of Π and Σ. Note that Ǐ-closure
keeps identity types of small types small.

**Containment.** A type A in context Γ is a *type in 𝒰* (𝒰 *contains* A) when
𝒰 comes equipped with a code Ǎ : 𝒰 in context Γ with `Γ ⊢ Ty(Ǎ) ≡ A type`.
Informal convention: write A for the code Ǎ and also for Ty(Ǎ). Containment
is *structure* (a given code), not a proposition.

### Enough universes; base, successor, and join universes

Assuming a code Ŭ : 𝒰 with `Ty(Ŭ) ≡ 𝒰` is inconsistent (a variant of
Russell's paradox; the book derives the contradiction formally in the
univalence chapter, from 𝒰 being *equivalent to a type in* 𝒰). Instead:

**Postulate (enough universes).** For every finite list of types in context
`Γ₁ ⊢ A₁ type`, …, `Γₙ ⊢ Aₙ type`, there is a universe containing each Aᵢ.

- **Base universe 𝒰₀**: obtained from the empty list. Closed under all type
  formers; not specified to contain anything further.
- **Successor universe 𝒰⁺**: obtained from the list `⊢ 𝒰 type` and
  `X : 𝒰 ⊢ Ty(X) type`. Hence 𝒰⁺ has a code Ŭ with `Ty⁺(Ŭ) ≡ 𝒰`, and for
  each X : 𝒰 a code of Ty(X) in 𝒰⁺; the assignment of codes is an inclusion
  `i : 𝒰 → 𝒰⁺`. Iterating gives a tower 𝒰, 𝒰⁺, 𝒰⁺⁺, …, which need not be
  exhaustive: a type may lie outside every universe of the tower.
- **Join 𝒰 ⊔ 𝒱**: obtained from `X : 𝒰 ⊢ Ty(X) type` and `Y : 𝒱 ⊢ Ty(Y) type`.
  It contains everything in 𝒰 and in 𝒱, with maps `i : 𝒰 → 𝒰 ⊔ 𝒱` and
  `j : 𝒱 → 𝒰 ⊔ 𝒱`. **No relations between universes are postulated**:
  `(𝒰 ⊔ 𝒱) ⊔ 𝒲` and `𝒰 ⊔ (𝒱 ⊔ 𝒲)` are in general unrelated.

**Working discipline (typical ambiguity, Rijke-style).** Get by with a single
universe 𝒰; invoke 𝒰⁺ or joins only when a statement must treat 𝒰 itself as
a type (quantifying over all small types, forming `Σ (X:𝒰). …`). Levels stay
unannotated in prose; the invariant is that any finite collection of types in
play fits in some universe.

### Observational equality on ℕ

**Eq-ℕ : ℕ → (ℕ → 𝒰₀)** is the binary relation defined by double induction so
that the following hold judgmentally:

- `Eq-ℕ 0 0 ≡ 𝟏`
- `Eq-ℕ 0 (succ n) ≡ 𝟘`
- `Eq-ℕ (succ n) 0 ≡ 𝟘`
- `Eq-ℕ (succ n) (succ m) ≡ Eq-ℕ n m`

It is the algorithmic reading of equality on ℕ: inspect both arguments; equal
zeros are equal (`𝟏`), a zero and a successor are not (`𝟘`), and two
successors are equal iff their predecessors are. Landing in the *base*
universe suffices, since the values are built from 𝟘̌, 𝟏̌ and recursive calls.

### Ordering relations on ℕ (same template, from the exercises)

`≤ , < : ℕ → (ℕ → 𝒰₀)`, again by double induction into the universe:

- `0 ≤ n := 𝟏`; `(m+1) ≤ 0 := 𝟘`; `(m+1) ≤ (n+1) := (m ≤ n)`
- `0 < 0 := 𝟘`; `0 < (n+1) := 𝟏`; `(m+1) < 0 := 𝟘`; `(m+1) < (n+1) := (m < n)`

The book uses these to develop the poset structure of ℕ, antisymmetry,
transitivity, `(m ≤ n) + (n ≤ m)`, and interaction with `add`/`mul`
(exercises; see number-theory.md).

## Key results

**Reflexivity of Eq-ℕ.** `refl-Eq-ℕ : Π (n:ℕ). Eq-ℕ n n`, by induction on n:
`refl-Eq-ℕ 0 := ⋆` (since `Eq-ℕ 0 0 ≡ 𝟏`), and
`refl-Eq-ℕ (succ n) := refl-Eq-ℕ n`, which type-checks *because*
`Eq-ℕ (succ n) (succ n) ≡ Eq-ℕ n n` judgmentally.

**Eq-ℕ characterizes the identity type of ℕ (propositionally).**
For all m n : ℕ, `(m = n) ↔ Eq-ℕ m n`.

- `→`: path induction, using refl-Eq-ℕ at `refl m`.
- `←`: induction on m and n. Case (0,0): `refl 0`. Mixed cases: Eq-ℕ is 𝟘
  there, so `ex-falso`. Case (succ m, succ n): compose
  `Eq-ℕ (succ m) (succ n) ≡ Eq-ℕ m n →(IH) (m = n) →(ap succ) (succ m = succ n)`,
  where the first map is the *identity function* — valid only because the
  reduction `Eq-ℕ (succ m) (succ n) ≡ Eq-ℕ m n` is judgmental.

**Peano's seventh axiom — succ is injective.** `(m = n) ↔ (succ m = succ n)`.
Forward: `ap succ`. Converse: the composite
`(succ m = succ n) → Eq-ℕ (succ m) (succ n) ≡ Eq-ℕ m n → (m = n)`,
again with the middle map the identity function.

**Peano's eighth axiom — zero is not a successor.** `0 ≠ succ n` for all n:
the map `(0 = succ n) → Eq-ℕ 0 (succ n) ≡ 𝟘` is an instance of
`(m = n) → Eq-ℕ m n`.

**Remark (decidability).** Since Eq-ℕ is an algorithm, it can be used to show
equality on ℕ is *decidable*: a program deciding, for any m n, whether
m = n. (Stated as a remark here; used later to show ℕ is a set via Hedberg —
see truncation-levels.md.)

## Reasoning idioms

**Idiom 1 — To define a type family over an inductive type A, apply A's
induction principle with motive a universe.** A family over A is a map
`A → 𝒰`; "recursion into the universe" is induction with the constant motive
`λ_. 𝒰`. This is **large elimination**. The values you construct are *codes*,
assembled from the closure operations (𝟘̌, 𝟏̌, Π̌, Σ̌, …), and the decoding
equations make the resulting family compute judgmentally on constructors.

**Idiom 2 — The double-induction template for binary relations on ℕ.** To
define `R : ℕ → (ℕ → 𝒰)` with a first column `c : ℕ → 𝒰`, a value `Z : 𝒰` at
`(succ n, 0)`, and diagonal recursion `R (succ n) (succ m) ≡ R n m`:

- Outer induction on the first argument, motive `λ_. (ℕ → 𝒰)`.
- Base row `E₀ := c`, itself by induction on the second argument.
- Step `E_S : Π (n:ℕ). (ℕ → 𝒰) → (ℕ → 𝒰)`: given n and previous row X,
  define `E_S n X` by induction on the second argument with
  `E_S n X 0 := Z` and `E_S n X (succ m) := X m` (the step ignores its
  recursive hypothesis).
- Then `R 0 ≡ E₀` and `R (succ n) ≡ E_S n (R n)`; unfolding yields the four
  clauses as judgmental equalities.

Instantiations: Eq-ℕ (`c 0 := 𝟏`, `c (succ _) := 𝟘`, `Z := 𝟘`);
≤ (`c := λ_. 𝟏`, `Z := 𝟘`); < (`c 0 := 𝟘`, `c (succ _) := 𝟏`, `Z := 𝟘`).

**Idiom 3 — Constructor discrimination (no-confusion).** To show constructors
of an inductive type are disjoint (or injective), define a universe-valued
family that maps them to *different types* (e.g. 𝟏 vs 𝟘), then turn a
putative identification into a function between those types. The one-liner
for P8: `P : ℕ → 𝒰₀` by `P 0 := 𝟏`, `P (succ n) := 𝟘`; then p : 0 = succ n
gives `tr P p ⋆ : 𝟘`. The book packages this once and for all as Eq-ℕ plus
`(m = n) → Eq-ℕ m n`; the same pattern gives Eq-bool on bool, hence
`false ≠ true` (exercise).

**Idiom 4 — "Observational" families as the master plan for identity types.**
The identity type is generic; for a *specific* type, define what equality
should be as a type family and prove `(x = y) ↔ R x y`. Eq-ℕ is the first
instance; the fundamental theorem later upgrades such ↔ to equivalences
`(x = y) ≃ R x y` and becomes the principal characterization tool
(fundamental-theorem.md).

**Idiom 5 — Level checklist.** When writing `F : A → 𝒰`, check A and every
value of F live where claimed. Relations assembled from 𝟘/𝟏 and recursion fit
in 𝒰₀. The moment a type quantifies over a universe — `Π (X:𝒰). B X` or
`Σ (X:𝒰). B X` (structures like semigroups and groups) — it lives in 𝒰⁺,
never in 𝒰. Identity types of small types stay small (Ǐ-closure), so
propositions-as-types reasoning over small types causes no level bump.

**Why recursion into a fixed type cannot do this.** Induction with a fixed
motive C only produces elements of the one pre-existing type C; the *type of
the output cannot depend on the constructor*. Universe-valued recursion
outputs a different type per constructor, which is exactly what separates
them: no element of a fixed type can witness "0 is not a successor", but the
family P above turns any `0 = succ n` into a function `𝟏 → 𝟘`. In pure
Martin-Löf type theory without universes, `0 ≠ succ n` — even
`true ≠ false` — is unprovable. Large elimination is essential, not a
convenience.

## Pitfalls

1. **Never assume 𝒰 : 𝒰.** No code Ŭ : 𝒰 with `Ty(Ŭ) ≡ 𝒰`; a Russell-variant
   yields a contradiction. If you need 𝒰 as a type, move to 𝒰⁺.
2. **Code/type confusion.** X : 𝒰 is an element, not a type; Ty(X) is the
   type. Informal prose drops Ty — restore it whenever levels matter or when
   formalizing; a function expecting a type cannot be applied to X itself.
3. **Containment is structure, and `≡` is not a type.** "𝒰 contains A" means
   a code with `Ty(Ǎ) ≡ A` is *given*; it cannot be hypothesized, negated, or
   proved by induction inside the theory.
4. **No inter-universe relations are postulated.** Joins are not associative
   and towers need not be exhaustive. Do not silently identify a type in 𝒰
   with its image in 𝒰⁺ — go through the inclusion `i : 𝒰 → 𝒰⁺`.
5. **Don't attempt constructor disjointness by recursion into a fixed type.**
   The motive must be a universe; see "Why recursion into a fixed type…".
6. **Level leaks.** `Π (X:𝒰). B X` and `Σ (X:𝒰). B X` are types in 𝒰⁺, not
   𝒰. Any "theorem" whose proof requires 𝒰 to be small in itself is a level
   error, not a result.
7. **Compute before proving.** Goals headed by defined families reduce
   judgmentally: `Eq-ℕ (succ m) (succ n)` *is* `Eq-ℕ m n` — the identity
   function then does real work, as in P7. Conversely, the facts
   `(m = n) ↔ Eq-ℕ m n` are propositional and must be *proved* (path
   induction / induction on ℕ); do not claim them judgmental.

## See also

- dependent-type-theory.md — judgments, `≡` vs `=`, Π- and Σ-types that
  universes close over.
- inductive-types.md — the induction principles of ℕ, 𝟘, 𝟏, bool applied here
  with universe-valued motives.
- identity-types.md — path induction, `ap`, `tr`, used in the Eq-ℕ proofs.
- fundamental-theorem.md — upgrades `(m = n) ↔ Eq-ℕ m n` to an equivalence;
  the general machine behind observational equality.
- truncation-levels.md — Prop-𝒰 and Set-𝒰 built from universes; decidability
  of Eq-ℕ feeds Hedberg's theorem that ℕ is a set.
- logic-truncation.md — logic over small propositions; why `Prop-𝒰` needs a
  successor universe.
- univalence.md — identity types *of* a universe; smallness; the formal
  Russell-style contradiction from a self-contained universe.
- funext.md — needed later for closure of truncations under Π; independent
  axiom.
- groups.md — `Semigroup`/`Group` as `Σ (X:𝒰). …`, the second raison d'être
  of universes; such types live in 𝒰⁺.
- finite-types.md — `Fin k` as a family of small types; counting arguments
  use decidable equality.
- number-theory.md — uses ≤, <, dist-N, and decidability of equality on ℕ.
- circle.md — the universal cover is defined by recursion `S¹ → 𝒰` (via
  univalence), the HIT analogue of Idiom 1.
