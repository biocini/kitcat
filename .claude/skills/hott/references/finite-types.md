# Finite types

Digest of Rijke, *Introduction to HoTT*, §"Finite types",
plus the definition of the standard
finite types from §"The standard finite types".
The chapter answers: what is a finite type, when is cardinality well-defined,
and which constructions preserve finiteness — all *without* classical choice
principles.

Dependencies assumed here: equivalences, embeddings, fibers (`equivalences.md`);
sets, propositions, Hedberg's theorem (`truncation-levels.md`); propositional
truncation, decidability, global choice (`logic-truncation.md`); pattern
matching on inductive families (`inductive-types.md`).

**Axiom hygiene.** Everything in this chapter is proved *without funext and
without univalence*. Propositional truncation `‖-‖` is used as a postulated
type former (part of the ambient univalent foundations), and its universal
property is used constantly to eliminate `‖-‖` into propositions. Univalence
first becomes essential for the *identity types* of 𝔽 and for the binomial
types (flagged below).

## Key definitions

### The standard finite types — iterated coproduct, not a subtype of ℕ

Rijke's official definition is the **iterated-coproduct** one, a recursive
type family over ℕ:

    Fin 0      :=  𝟘
    Fin (k+1)  :=  Fin k + 𝟏

Conventions: `i := inl : Fin k → Fin (k+1)` and `⋆ := inr ⋆ : Fin (k+1)` (the
"point"). The "classical" definition `classical-Fin k := Σ (x:ℕ). x < k` is
mentioned and is equivalent to `Fin k` (an exercise), but it is **not** the
definition used — everything proceeds by the following induction principle.

**Induction principle of Fin.** To define `f : Π (k:ℕ). Π (x:Fin k). P k x`
it suffices to give, for each `k : ℕ`,

    g k  :  Π (x:Fin k). P k x → P (k+1) (i x)
    p k  :  P (k+1) ⋆

and the defining equations hold *judgmentally*: `f (k+1) (i x) ≡ g k x (f k x)`
and `f (k+1) ⋆ ≡ p k`. Definitions are presented by pattern matching on `i x`
and `⋆`; the judgmental equalities are the only handles one has on an
inductively defined map.

**The inclusion into ℕ.** `ι k : Fin k → ℕ` by `ι (i x) := ι x`, `ι ⋆ := k`.
It is bounded (`ι x < k`) and injective. So `Fin k` really is "the first k
naturals", but as a coproduct tower.

### Observational equality on Fin k

A binary family `Eq-Fin k : Fin k → Fin k → 𝒰₀`, defined recursively:

    Eq-Fin (i x) (i y)  :=  Eq-Fin x y      Eq-Fin (i x) ⋆  :=  𝟘
    Eq-Fin ⋆ (i y)      :=  𝟘               Eq-Fin ⋆ ⋆      :=  𝟏

Key facts (all axiom-free):

- `(x = y) ↔ Eq-Fin k x y` — identity is reflected into a small recursive
  family built from 𝟘 and 𝟏.
- `Eq-Fin k x y` is decidable (𝟘 and 𝟏 are decidable, recursion preserves
  decidability), hence **Fin k has decidable equality**.
- By Hedberg's theorem (`truncation-levels.md`), **Fin k is a set**.

### Countings, finiteness, cardinality

    count(A)       :=  Σ (k:ℕ). (Fin k ≃ A)          -- a counting is DATA
    is-finite(X)   :=  ‖ Σ (k:ℕ). (Fin k ≃ X) ‖      -- a mere proposition
    is-finite'(X)  :=  Σ (k:ℕ). ‖ Fin k ≃ X ‖        -- manifestly a proposition

    𝔽      :=  Σ (X:𝒰₀). is-finite X                 -- the type of finite types
    BS k   :=  Σ (X:𝒰₀). ‖ Fin k ≃ X ‖               -- k-element types

`(k, e) : count(A)` is pronounced "A has k elements". `𝔽` is the image of
`Fin : ℕ → 𝒰₀`; `BS k` is the connected component of `𝒰₀` at `Fin k`.

### Supporting notions

- `is-decidable X := X + ¬X`; a **decidable subtype** of A is
  `P : A → Prop-𝒰` with each `P x` decidable.
- A map `f : A → B` is **decidable** if every fiber `fib f b` is decidable;
  `A ↪d B` is the type of **decidable embeddings** (embeddings that are
  decidable maps).
- **Falling factorial** `(n)ₘ` by recursion: `(0)₀ := 1`, `(0)(m+1) := 0`,
  `(n+1)₀ := 1`, `(n+1)(m+1) := (n+1)·(n)ₘ`.
- **S(m,n)** counts surjections: `S(0,0) := 1`, `S(0,n+1) := 0`,
  `S(m+1,0) := 0`, `S(m+1,n+1) := (n+1)·S(m,n) + S(m,n+1)`. It equals
  `n! · Stirling(m,n)` (Stirling number of the second kind).

## Key results

### About countings (data-level closure)

- `count(Fin k)` canonically via `(k, id)`; countings transport along
  equivalences (`count(A)` and `A ≃ B` give `count(B)`).
- A has 0 elements iff A is empty; A has 1 element iff A is contractible.
- **A proposition has a counting iff it is decidable.** (Induction on k:
  k = 0 gives emptiness; successor gives the point `e ⋆`.)
- **Counting ⇒ decidable equality**, because Fin k has decidable equality
  and decidable equality transports along equivalences.
- **Coproducts:** `count(A) × count(B) ↔ count(A + B)`; forward via
  `Fin k + Fin l ≃ Fin (k+l)`.
- **Σ-types (the master counting theorem).** For `B` over `A`:
  (a) `count(A)`, (b) `Π (x:A). count(B x)`, (c) `count(Σ (x:A). B x)`.
  If (a) holds then (b) ⇔ (c). If (b) and (c) hold and `B` has a section,
  then (a) holds. Core computation: the fiber of `b ↦ (a,b)` over `(x,y)`
  is equivalent to `a = x`, a decidable proposition.
- **Subtype corollary:** for a counted type A and a subtype P,
  `count(Σ (x:A). P x) ↔ Π (x:A). is-decidable (P x)`.
- **Products:** counted A, B ⇒ counted `A × B`; conversely a counting of
  `A × B` yields maps `B → count(A)` and `A → count(B)`.

### Double counting — cardinality is well-defined

- **Proposition (maybe-equivalence).** For any types X, Y there is a map
  `(X + 𝟏 ≃ Y + 𝟏) → (X ≃ Y)`. Proof sketch: when `e (i x) = ⋆`, injectivity
  of `e` forces `e ⋆ ≠ ⋆`, yielding a `⋆-value(e,x) : Y` with
  `i (⋆-value) = e ⋆`; define `f : X → Y` by pattern matching on
  `e (i x) : Y + 𝟏` (sending `i y ↦ y` and `⋆ ↦ ⋆-value`); build `g : Y → X`
  dually from `e⁻¹`; verify invertibility by case analysis on whether
  `e⁻¹ (i y) = ⋆`, closing with injectivity of `i`.
- **Theorem (is-injective-Fin).** `(Fin k ≃ Fin l) → (k = l)`, by double
  induction on k and l: mismatched zero/successor cases give an element of
  𝟘; the successor/successor case strips one point by the previous
  proposition and applies the inductive hypothesis.
- **Consequence.** `is-finite'(X)` is a proposition: if `‖Fin k ≃ X‖` and
  `‖Fin l ≃ X‖` then (eliminating into the proposition `k = l`, since ℕ is
  a set) get `Fin k ≃ Fin l`, hence `k = l`. Also
  `is-finite(X) ↔ is-finite'(X)`, both propositions, hence `≃`.
- **Cardinality.** The unique k with `‖Fin k ≃ X‖` is `|X|`. Well-defined
  *number*, non-unique equivalence.
- **Corollary.** `𝔽 ≃ Σ (k:ℕ). BS k` (reassociate the Σ and use
  `is-finite ≃ is-finite'`).

### Finite choice and closure of finite types

- **Finite choice.** For A finite and `B` over A:
  `(Π (x:A). ‖B x‖) → ‖ Π (x:A). B x ‖`.
  Proof: the goal is a proposition, so assume a counting `Fin k ≃ A`; induct
  on k. Base case: Π over 𝟘 is contractible. Step: split
  `Π (x:Fin (k+1)). C x ≃ (Π (x:Fin k). C (i x)) × C ⋆` (dependent universal
  property of coproducts) and use `‖X × Y‖ ≃ ‖X‖ × ‖Y‖`.
- **Closure theorem for finite types.**
  1. `is-finite X × is-finite Y ↔ is-finite (X + Y)`.
  2. X, Y finite ⇒ `X × Y` finite; `X × Y` finite ⇒ `Y → is-finite X` and
     `X → is-finite Y`.
  3. For `B` over `A` with (a) A finite, (b) each `B x` finite, (c) `Σ B`
     finite: (a) ⇒ ((b) ⇔ (c)) — the (b)⇒(c) direction uses finite choice to
     get `‖ Π (x:A). count (B x) ‖`, then the counting theorem. If (b),(c)
     hold and B has a section, then (a). In general: (b),(c) imply (a)
     **iff A is a set and `Σ (x:A). ¬ B x` is finite** — split
     `A ≃ (Σ (x:A). ‖B x‖) + (Σ (x:A). ¬ B x)` and use global choice for
     decidable subtypes of a counted type (`‖Σ P‖ → Σ P`, least-witness
     selection), after showing each `B a` is a decidable subtype of the
     total space (the fiber of the fiber inclusion `i a` at `(x,y)` is
     `a = x`).
- Every finite type has decidable equality; every finite type is a set.

### Combinatorial equivalences (exercises, usable as facts)

- `Fin (n^m) ≃ (Fin m → Fin n)` and `Fin (n!) ≃ (Fin n ≃ Fin n)`; hence
  finite types are closed under `→` and under `A ≃ A`.
- Retracts: A a retract of B ⇒ `count(B) → count(A)`, hence finite types
  are closed under retracts.
- For `f : I → J` between finite types: `is-emb f`, `is-surj f`,
  `is-equiv f` are all decidable; more generally `Π (i:I). A i` is decidable
  for decidable `A i` over finite `I`.
- Quotients: for a surjection `f : A → B` with A finite, `B` is finite iff
  `B` has decidable equality. Π-finiteness: A finite and each `B x` finite
  ⇒ `Π (x:A). B x` finite.
- **Pigeonhole.** For `f : X → Y` with `|X| = m`, `|Y| = n`:
  `is-inj f → m ≤ n`; and `n < m → ∃ (x x':X). (x ≠ x') × (f x = f x')`.
  Corollary: no embedding `ℕ ↪ Fin k`.
- **Dedekind finiteness.** For finite X: every embedding `X ↪ X` is an
  equivalence, and every surjection `X → X` is an equivalence.
- **Embeddings counted:** `Fin ((n)ₘ) ≃ (Fin m ↪ Fin n)`; hence `A ↪ B` has
  `(n)ₘ` elements when `|A| = m`, `|B| = n`. Recursive heart:
  `((A+𝟏) ↪d (B+𝟏)) ≃ (𝟏 ↪d (B+𝟏)) × (A ↪d B)`.
- **Surjections counted:** `Fin (S(m,n)) ≃ (Fin m ↠ Fin n)`.
- **Escardó's equivalence:** `((A + 𝟏) ≃ (B + 𝟏)) ≃ (𝟏 ↪d (B + 𝟏)) × (A ≃ B)`.
  For 2-element X: `(A + B)^X ≃ A^X + X × (A × B) + B^X`.

### Binomial types (uses univalence)

Not part of this chapter, but the natural continuation: with
`𝒰_B := Σ (X:𝒰). ‖B ≃ X‖` (so `𝒰_{Fin n} = BS n`),

    (A choose B)  :=  Σ (X : 𝒰_B). (X ↪d A)             -- binomial type

Rijke proves (via the subtype classifier, hence **univalence**) that
`(A choose B) ≃ Σ (P : A → Decidable-Prop). ‖B ≃ Σ (a:A). P a‖` — decidable
subtypes of A merely equivalent to B — and that for `|A| = n`, `|B| = k`,
the binomial type has `n choose k` elements, with recursion
`(A+𝟏 choose B+𝟏) ≃ (A choose B+𝟏) + (A choose B)`. Decidable embeddings are
essential: ordinary embeddings give the wrong count.

## Reasoning idioms

- **"Assume the counting".** The master move of the whole chapter: to prove a
  *proposition* about a finite type A, eliminate `is-finite A` (the goal is a
  proposition, so truncation elimination is legitimate) to obtain an actual
  `e : Fin k ≃ A`. Never try to extract data from `‖-‖` when the goal isn't
  a proposition.
- **Transport to Fin k, then induct.** Once `e : Fin k ≃ A` is in hand,
  replace every statement about A by its transported version about Fin k
  (families `B x ↦ B (e x)`, etc.) and do induction on k.
- **Peel off the point.** The workhorse decomposition, right-distributivity
  of Σ over coproducts:
  `Σ (x:Fin (k+1)). B (e x) ≃ (Σ (x:Fin k). B (e (i x))) + B (e ⋆)`.
  Dually for Π: `Π (x:Fin (k+1)). C x ≃ (Π (x:Fin k). C (i x)) × C ⋆`.
  Most finiteness proofs are: base case (empty/contractible), peel, inductive
  hypothesis, closure under +.
- **Pattern-match on i and ⋆, and decide equality by recursion.** Definitions
  on Fin k are given by the two clauses `i x` / `⋆`, and the judgmental
  computation rules are the only interface. To contradict or decide `x = y`
  in Fin k, push the identification through `Eq-Fin` and compute: mixed cases
  land in 𝟘 (`ex-falso`), equal cases in 𝟏.
- **Compute the fiber to expose an identity type.** Both in the master
  counting theorem and the Σ-closure theorem, the fiber of a canonical map
  (`b ↦ (a,b)`, `a ↦ (a, s a)`, fiber inclusions) computes via
  Σ-of-identities and contractibility of singletons to a bare identity type
  `a = x` — decidable because the ambient type is counted. Recipe: unfold
  `fib`, reassociate Σ, contract singletons, read off.
- **Decidable subtypes are counted by pointwise decidability.** To count
  `Σ (x:A). P x` over a finite A, show `Π (x:A). is-decidable (P x)`.
- **Global choice via least witnesses.** For a decidable subtype P of Fin k
  (or of any counted type), `‖Σ P‖ → Σ P`: the type "x is in P and is a
  lower bound of P" is a proposition, so truncation elimination applies.
  Use it whenever a *mere* inhabitant of a decidable subtype of a finite
  type must become an actual one.
- **Count a structure type by recursion.** To show a type of combinatorial
  structures (functions, equivalences, embeddings, surjections) is finite
  with a prescribed cardinality, build an equivalence to `Fin r` where r is
  defined by the *same* recursion as the type's own decomposition
  (`n^m`, `n!`, `(n)ₘ`, `S(m,n)`).
- **Double counting as a reasoning principle.** Two countings of the same
  type yield `Fin k ≃ Fin l`, hence `k = l`: equate cardinalities by
  constructing an equivalence, not by computing with sizes.

## Pitfalls

- **is-finite is truncated; a counting is data.** `is-finite X` is a mere
  proposition — a type "can be finite in several ways" (e.g. `count(Fin k)`
  contains the k! permutations). The cardinality `|X| : ℕ` is well-defined
  (double counting), the equivalence is not. Confusing the two levels is the
  central error this chapter guards against.
- **Truncation placement matters.** `‖Σ (k:ℕ). Fin k ≃ X‖` (is-finite) vs
  `Σ (k:ℕ). ‖Fin k ≃ X‖` (is-finite′): logically equivalent, and both are
  propositions, but the proof that is-finite′ is a proposition needs
  is-injective-Fin. From `is-finite X` you may only eliminate into
  propositions.
- **Finite choice is not the axiom of choice.** It is a theorem requiring
  the *domain* to be finite; do not instantiate it with an arbitrary type,
  and do not invoke AC for it.
- **Converses are conditional.** `X × Y` finite does not imply X finite
  unless Y is inhabited (the conclusion is a function `Y → is-finite X`).
  Σ-finiteness: (b),(c) ⇒ (a) only with a section of B, or when A is a set
  and `Σ (x:A). ¬ B x` is finite. The naive converses fail.
- **A proposition is finite iff it is decidable.** You cannot prove an
  arbitrary proposition finite without deciding it; "finite" is stronger
  than "at most one element" (that would be `is-prop` alone).
- **Pigeonhole concludes mere existence.** The collision pair is under `∃`
  (a truncation); no explicit pair is produced.
- **Definitional vs propositional equalities on indices.**
  `Fin (k+1) ≡ Fin k + 𝟏` judgmentally, but `Fin (k+l) ≃ Fin k + Fin l` and
  `Fin (k·l) ≃ Fin k × Fin l` are proved equivalences, not definitional —
  rewrite with explicit transport, and expect index arithmetic to need the
  laws of Fin.
- **Finite ⇒ set, not conversely.** All finite types are sets (Hedberg +
  decidable equality), but sets like ℕ are not finite; techniques here
  (Fin-induction, peeling) are unavailable for infinite sets.
- **Decidability of `is-emb`/`is-surj`/`is-equiv` needs finite (or at least
  counted) domain and codomain** — the quantifiers range over the fibers,
  and deciding them is a finite Π over decidable types.
- **Identity types of 𝔽 are not computed in this chapter.** `BS k` is the
  connected component `𝒰_{Fin k}`; describing `((X,p) = (Y,q))` in 𝔽 needs
  univalence (`(X = Y) ≃ (X ≃ Y)`, so `BS k ≃ BAut (Fin k)`), beyond the
  axiom-free scope here. Binomial types likewise live in the univalence
  chapter.
- **The `⋆` overloading.** Rijke writes `⋆` both for the point of 𝟏 and for
  `inr ⋆ : Fin (k+1)`; remember `i : Fin k → Fin (k+1)` is `inl`, an
  embedding whose image misses exactly `⋆`.

## See also

- `inductive-types.md` — recursion/pattern matching on type families; the
  Fin induction principle is an instance.
- `identity-types.md` — transport, ap, singleton contractibility; the fiber
  computations used throughout.
- `equivalences.md` — equivalences, embeddings, fibers, retracts; the laws
  `Fin (k+l) ≃ Fin k + Fin l`, `Fin (k·l) ≃ Fin k × Fin l` live there.
- `fundamental-theorem.md` — characterizing identity via total spaces of
  fibers.
- `truncation-levels.md` — propositions, sets, Hedberg's theorem
  (decidable equality ⇒ set), contractibility (1-element types).
- `logic-truncation.md` — propositional truncation, decidability,
  `‖X × Y‖ ≃ ‖X‖ × ‖Y‖`, global choice and mapping `‖-‖` into sets.
- `number-theory.md` — Eq-Fin, decidable equality of Fin k, the inclusion
  `ι : Fin k → ℕ`; divisibility and ℕ modulo k+1.
- `univalence.md` — identity of 𝔽 and BS k as BAut; binomial types via
  decidable embeddings (axiom-flagged).
- `quotients.md` — Fin (k+1) as the quotient of ℕ by congruence mod k+1;
  surjections and decidable equality.
- `funext.md` — dependent universal properties used in Π-decompositions;
  Π-finiteness.
- `universes.md` — 𝒰₀, subuniverses, connected components of universes.
- `groups.md` — Aut(Fin n) as the symmetric group; group actions on
  decidable embeddings (orbits = binomial types).
- `dependent-type-theory.md` — Σ, Π, coproducts, distributivity.
- `w-types.md` — general inductive constructions (same library).
- `circle.md` — synthetic homotopy theory (same library).
