# Propositional truncation and univalent logic

Digest of Rijke, *Introduction to HoTT*, §"Propositional truncations"
and §"Image
factorizations". The first chapter
postulates the propositional truncation `‖A‖` — the *proposition* that A is
inhabited — and rebuilds logic on propositions (`∃ := ‖Σ‖`, `∨ := ‖+‖`). The
second applies it to construct the image of a map, characterize surjections,
and run Cantor's diagonal argument.

Dependencies assumed here: propositions, sets, embeddings, subtypes
(`truncation-levels.md`); equivalences, fibers (`equivalences.md`); the
fundamental theorem (`fundamental-theorem.md`); path algebra, transport,
`ap`/`apd` (`identity-types.md`); coproducts and Σ-types (`inductive-types.md`).

**Axiom hygiene.** Propositional truncation is **not derivable** in the bare
Martin–Löf type theory of the earlier chapters: Rijke adds it as **new rules**
(formation, constructors, induction — a higher inductive type), plus closure
of every universe under `‖-‖`. Treat "every type has a propositional
truncation" as a postulate on the same footing as univalence. Relative to
that postulate, the chapter's results are axiom-free **except**: Kraus's
theorem (T9) and the truncation-level strengthening of the surjection
characterization (I5) use **funext** (in this book funext is derived from the
univalence axiom, so the flag propagates). Cantor's theorem (I9) needs
nothing beyond the truncation postulate — it uses only `happly`, not funext.

## Key definitions

### Propositional truncation: the specification

A map `f : A → P` into a **proposition** P **is a propositional truncation**
of A when for every proposition Q the precomposition map

    (- ∘ f) : (P → Q) → (A → Q)

is an equivalence. This is the **universal property** of `f`. The fiber of
precomposition at `g : A → Q` is `Σ (h : P → Q). h ∘ f = g`, so the universal
property says: every `g : A → Q` into a proposition **extends uniquely**
along `f`.

**Simplified check** (used constantly). `X → Q` is a proposition when Q is,
and a map between propositions is an equivalence once a map back exists
(`truncation-levels.md` R3). So `f : A → P` is a truncation as soon as we
construct, for every proposition Q, a bare map

    (A → Q) → (P → Q).

### The postulate: truncation as a higher inductive type

Rijke postulates, for every type A, a type `‖A‖` (universes closed under it),
with one point constructor and one **path constructor**:

    η : A → ‖A‖                          (the unit)
    α : Π (x y : ‖A‖). x = y             (any two elements identified)

**Induction principle.** For a family Q over `‖A‖`, given
`f : Π (a:A). Q (η a)` and identifications `tr Q (α x y) u = v` for all
`x y : ‖A‖`, `u : Q x`, `v : Q y`, one obtains `h : Π (t:‖A‖). Q t` with
`h ∘ η ~ f`. Key remark: the transport condition holds **iff Q is
proposition-valued** (transport along `α x y` is an embedding, so
`tr Q (α x y) u = tr Q (α x y) v` gives `u = v` for all `u v : Q x`).
Consequence: **truncation induction only ever targets propositions**, and
there are no interesting computation rules — any identification in a
proposition holds automatically.

### Univalent logic: the connectives as propositions

    ⊤        :=  𝟏
    ⊥        :=  𝟘
    P ⇒ Q    :=  P → Q
    P ∧ Q    :=  P × Q
    P ∨ Q    :=  ‖P + Q‖
    P ⇔ Q    :=  (P → Q) × (Q → P)
    ¬ A      :=  A → 𝟘
    ∃ (x:A). P x   :=  ‖Σ (x:A). P x‖        (P a family of propositions)
    ∀ (x:A). P x   :=  Π (x:A). P x

Only `∨` and `∃` need truncation: propositions are already closed under `×`,
`→`, and Π over arbitrary index types (**funext** flag on the Π-closure; see
`truncation-levels.md` deferred results), but not under `+` or Σ.

### Mere equality

    mere-eq x y  :=  ‖x = y‖

An equivalence relation on any type (exercise): the proposition-valued shadow
of the identity type, forgetting *which* identification exists. On sets it
coincides with `=` (a proposition is its own truncation); on higher types it
is strictly coarser and does **not** imply `x = y`.

### Weakly constant maps

    is-weakly-constant f  :=  Π (x y : A). f x = f y

for `f : A → B`. Weaker than constant: `const b` comes with a chosen `b : B`;
weak constancy does not require B to be inhabited at all. Calibration:
`id : A → A` is **constant** iff A is contractible; **weakly constant** iff A
is a proposition.

### Morphisms over a common codomain; the image

For `f : A → X` and `g : B → X`, a **morphism from f to g over X** is

    hom-X f g  :=  Σ (h : A → B). f ~ g ∘ h
    (k , K) ∘ (h , H)  :=  (k ∘ h , H ∙ (K · h))

A commuting triangle `f ~ i ∘ q` with `i : I ↪ X` an embedding **satisfies the
universal property of the image of f** if precomposition
`hom-X i m → hom-X f m` is an equivalence for every embedding `m : B ↪ X`.

The **image** of `f : A → X` is defined by

    im f   :=  Σ (x:X). ‖fib f x‖
    i-f    :=  pr₁ : im f → X                      (image inclusion)
    q-f x  :=  (f x , η (x , refl (f x))) : im f
    I-f x  :=  refl (f x)   :   f ~ i-f ∘ q-f

### Surjections; power sets

    is-surj f  :=  Π (b:B). ‖fib f b‖              for f : A → B

"Every fiber is *merely* inhabited." Compare a **split epimorphism** (f with
a section): that gives actual fibers, and is strictly stronger.

    𝒫-𝒰 X  :=  X → Prop-𝒰                          (𝒰-power set of X)

## Key results

Tags T1–T11 (truncation chapter) and I1–I9 (images chapter) are local to this
file. All are relative to the truncation postulate; extra flags marked inline.

- **T1. `‖A‖` is a proposition.** Immediate from the path constructor `α`.
- **T2. `η : A → ‖A‖` satisfies the universal property.** By the simplified
  check, need `(A → Q) → (‖A‖ → Q)` for Q a proposition; that is exactly
  truncation induction into the constant proposition family Q (the transport
  obligation holds because Q is a proposition).
- **T3. Uniqueness / 3-for-2.** Given `f : A → P`, `f' : A → P'` into
  propositions: any two of {f is a truncation, f′ is a truncation,
  `P ≃ P′` (uniquely)} imply the third. Two truncations are equivalent via
  mutual UPs; `P ≃ P′` is a proposition, giving uniqueness.
- **T4. Functoriality.** `‖-‖ : (A → B) → (‖A‖ → ‖B‖)` by extending `η ∘ f`;
  `‖id‖ ~ id` and `‖g ∘ f‖ ~ ‖g‖ ∘ ‖f‖` by uniqueness of extensions.
- **T5. Universal properties of ∨ and ∃.** `i := η ∘ inl`, `j := η ∘ inr`, and
  for every proposition R:

      (P ∨ Q → R)  ≃  (P → R) × (Q → R)

  by composing the truncation UP with the coproduct UP. Similarly
  `ε a p := η (a , p)` and for every proposition Q:

      ((∃ (x:A). P x) → Q)  ≃  (Π (x:A). P x → Q)

  by composing the truncation UP with the Σ UP (currying). Both displayed maps
  are equivalences, not just logical equivalences.
- **T6. Drill equivalences** (exercises; both sides propositions, so `↔`
  upgrades to `≃`):

      ‖‖A‖‖ ≃ ‖A‖                  ‖A × B‖ ≃ ‖A‖ × ‖B‖
      ‖A‖ ∨ ‖B‖ ≃ ‖A + B‖          ∃ (x:A). ‖B x‖ ≃ ‖Σ (x:A). B x‖
      ¬¬‖A‖ ≃ ¬¬A                  ‖is-decidable A‖ ≃ is-decidable ‖A‖
      is-decidable A → (‖A‖ → A)   ¬¬(‖A‖ → A)

  (Product law: truncations f, g give a truncation f × g. Last entry: every
  type ¬¬-satisfies global choice.)
- **T7. Dependent universal property.** `f : A → P` (P a proposition) is a
  truncation iff for every family Q of **propositions** over P, precomposition
  `(Π (p:P). Q p) → (Π (x:A). Q (f x))` is an equivalence.
- **T8. Cheap recognitions of truncations.** (a) If `f : A → P` into a
  proposition has a retraction `g : P → A`, then f is a truncation; in
  particular `const ⋆ : A → 𝟏` is a truncation for inhabited A (so `‖A‖ ≃ 𝟏`
  then). (b) If A is already a proposition, `f : A → P` is a truncation iff it
  is an equivalence; `id : A → A` is a truncation, i.e. `‖A‖ ≃ A` for
  propositions.
- **T9. Kraus's theorem — mapping into sets.** **(flag: funext)** For A any
  type and B a **set**, the map

      (‖A‖ → B) → Σ (f : A → B). Π (x y:A). f x = f y
      g ↦ (g ∘ η , λx. λy. ap g (α x y))

  is an equivalence. So a weakly constant map into a set **extends uniquely**
  through `‖A‖`. Proof skeleton: uniqueness via truncation induction into the
  proposition `g x = h x` (B a set); existence by observing that
  `Σ (b:B). ‖Σ (x:A). f x = b‖` is a proposition (two elements `b`, `b′`
  satisfy `b = b′` via weak constancy after peeling the truncations — licensed
  because the goal `b = b′` is a proposition), then extending
  `x ↦ (f x , η (x , refl))` along η and projecting.
- **T10. Global choice is exceptional.** A type A **satisfies global choice**
  if there is a map `‖A‖ → A`. Decidability gives it (T6); flagship example:
  for a **decidable subtype** P of ℕ, `‖Σ (x:ℕ). P x‖ → Σ (x:ℕ). P x`, because
  `Σ (x:ℕ). P x × is-lower-bound-P x` ("the least witness") is a proposition —
  map into it by the truncation UP (well-ordering supplies the map on Σ, using
  decidability), then project. Same over `Fin k`. **(flag: univalence)** Not
  every type satisfies global choice — refuted later in the book.
- **T11. Impredicative encodings** (exercise). `‖A‖ ≃ Π (Q:Prop-𝒰). (A → Q) → Q`,
  and analogous System-F-style encodings for all connectives, e.g.
  `∃ (x:A). P x ≃ Π (Q:Prop-𝒰). (Π (x:A). P x → Q) → Q` and
  `‖a = x‖ ≃ Π (Q : A → Prop-𝒰). Q a → Q x`. **Caveat:** the encoding of `‖A‖`
  only satisfies the universal property for propositions (equivalent to ones)
  in 𝒰 — do not adopt it as the *definition* of truncation.

### Images

- **I1.** For any embedding `m : B ↪ X`, `hom-X f m` is a proposition:
  `hom-X f m ≃ Π (a:A). fib m (f a)`, a product of propositions (embeddings
  have propositional fibers; Π-closure **flag: funext**).
- **I2. Simplified image check.** Since both `hom-X` types are propositions,
  a triangle `f ~ i ∘ q` with i an embedding satisfies the image universal
  property as soon as there is a map `hom-X f m → hom-X i m` for every
  embedding m.
- **I3. Existence.** `i-f : im f → X` is an embedding (a subtype projection,
  since `‖fib f x‖` is a proposition) and satisfies the universal property of
  the image: for an embedding m, `fib i-f x ≃ ‖fib f x‖` maps into the
  proposition `fib m x` by the truncation UP.
- **I4. Uniqueness / 3-for-2.** For two triangles with embeddings i, i′: any
  two of {i has the image UP, i′ has the image UP, contractible type of
  equivalences `e : B ≃ B′` commuting over X} implies the third. The image is
  unique up to a **unique** equivalence over X.
- **I5. Surjection characterizations.** **(flag: funext)** For `f : A → B`,
  equivalent: (i) f is surjective; (ii) **dependent universal property of
  surjections**: for every family P of *propositions* over B, precomposition
  `(Π (b:B). P b) → (Π (a:A). P (f a))` is an equivalence — "any subtype of B
  containing all the `f a` contains all of B"; (iii) for each k ≥ −2 and
  every family P of (k+1)-truncated types over B, precomposition is a
  k-truncated map. For (iii) ⇒ (i), instantiate P at `b ↦ ‖fib f b‖`.
- **I6. Truncation = surjection into a proposition.** For `f : A → P` with P a
  proposition: f is a propositional truncation iff f is surjective. (The
  special case of I5 where the dependent UP collapses to T7.)
- **I7. Image = (surjection, embedding) factorization.** In a triangle
  `f ~ m ∘ q` with m an embedding: m satisfies the image UP iff q is
  surjective. **Corollary: every map factors, uniquely up to unique
  equivalence over X, as a surjection followed by an embedding** — the
  (effective epi, mono) factorization: `f ~ i-f ∘ q-f` with `q-f` surjective
  and `i-f` an embedding.
- **I8. Equivalence = surjective embedding** (exercise): f is an equivalence
  iff f is both surjective and an embedding.
- **I9. Cantor's theorem.** For any type X and universe 𝒰 there is **no
  surjection** `X → 𝒫-𝒰 X`. Proof pattern: given `f : X → (X → Prop-𝒰)`
  surjective, set `P x := ¬ (f x x)`. Goal `𝟘` is a proposition, so from
  `‖Σ (x:X). f x = P‖` it suffices to assume `(x , p) : Σ (x:X). f x = P`.
  `happly p` gives `f x y ↔ P y` for all y; at `y := x` this is
  `f x x ↔ ¬ (f x x)` — impossible (no proposition is equivalent to its own
  negation). Related exercise: **Lawvere's fixed-point theorem** — a
  surjection `A → (A → B)` forces every `h : B → B` to merely have a fixed
  point.

## Reasoning idioms

- **Golden rule — using a truncated hypothesis.** To prove a **proposition**
  Q from `h : ‖A‖`, it suffices to construct a map `A → Q` (T2: the universal
  property / elimination rule). Informally: "since Q is a proposition, we may
  assume an actual element of A." Always name why the goal is a proposition
  before peeling the truncation — that is the entire justification.
- **Proving an `∃` goal.** To prove `∃ (x:A). P x`, supply a witness `a : A`
  and a proof `p : P a`, then apply `η (a , p)`. The result is truncated:
  you proved mere existence, and downstream consumers can only extract the
  witness into proposition-valued goals (see Golden rule).
- **Using an `∃` hypothesis.** From `h : ∃ (x:A). P x` with goal Q a
  proposition, use T5: it suffices to give `Π (x:A). P x → Q`, i.e. assume
  `(x , p)` and prove Q. Pattern: "let x : A with p : P x be such that …"
  — valid *only because Q is a proposition*.
- **Proving a `∨` goal.** To prove `P ∨ Q`, prove P (then `η ∘ inl`) or prove
  Q (then `η ∘ inr`). You must pick a side — but consumers of the disjunction
  cannot tell which side you picked.
- **Using a `∨` hypothesis (case analysis).** To prove a proposition R from
  `P ∨ Q`, give both `P → R` and `Q → R` (T5). Case analysis into a
  non-proposition is **not** licensed.
- **Negation goals are propositions.** `𝟘` is a proposition, so to refute
  `‖A‖` (i.e. prove `‖A‖ → 𝟘`) it suffices to refute A. Cantor's proof (I9)
  is the template: turn `is-surj f` into an untruncated hypothesis because
  the goal is `𝟘`.
- **Surjective precomposition.** To prove `Π (b:B). P b` with P
  proposition-valued and f surjective, it suffices to prove
  `Π (a:A). P (f a)` (I5(ii)). "It suffices to check the property on the
  image of f." **(flag: funext)**
- **Mapping `‖A‖` into a set.** Use Kraus (T9): define `f : A → B` and prove
  `Π (x y:A). f x = f y`. The extension `‖A‖ → B` is then unique. Two-step
  discipline: construct, then verify weak constancy. **(flag: funext)**
- **Mapping `‖A‖` into an arbitrary type X.** Find a proposition P with a map
  `P → X` and factor `A → P` through the truncation, then compose. The
  canonical P is a Σ-type over X that happens to be a proposition — as in
  Kraus's proof (`Σ (b:B). ‖Σ (x:A). f x = b‖`) and the least-witness example
  (T10). Enriching the output with propositional data until the codomain is a
  proposition is *the* technique.
- **Functorial lift.** From `f : A → B` get `‖f‖ : ‖A‖ → ‖B‖` (T4) — no weak
  constancy needed, since `‖B‖` is a proposition.
- **Truncation of a proposition is free.** If A is already a proposition,
  `‖A‖ ≃ A` (T8b): erase and re-add truncations on known propositions without
  ceremony (this is why T6's `↔`s upgrade to `≃`).
- **"Merely" vocabulary.** Write "there merely exists" for ∃-statements and
  "merely inhabited" for surjectivity, keeping the Σ/∃ distinction audible.

## Pitfalls

- **Σ vs ∃ confusion.** `Σ (x:A). P x` is *structure*: a chosen witness with
  its proof. `∃ (x:A). P x := ‖Σ (x:A). P x‖` is a *truth*. Stating a theorem
  with Σ overstates it when mere existence is meant (the image fiasco:
  `A ≃ Σ (b:B). Σ (a:A). f a = b`); using ∃ where a witness is needed
  downstream strands the proof. Choose by what consumers must extract.
- **No witness extraction into general types.** Elimination from `‖A‖` only
  targets propositions (T2, T7), or sets via weakly constant maps (T9).
  `‖A‖ → A` is **global choice** (T10) — unavailable in general, refuted via
  univalence. Never write "let a : A be such that η a = h" for `h : ‖A‖`
  unless the goal is a proposition.
- **The path constructor makes all truncated proofs equal.** `α x y`
  identifies any two elements of `‖A‖`, so `η a = η a′` in `‖A‖` even when
  `a ≠ a′`. Nothing built from `‖A‖` may depend on which `a` was used — that
  is what weak constancy (T9) measures.
- **Kraus needs a set codomain.** Rijke's theorem (T9) is stated for B a
  **set**; it does *not* say a weakly constant `f : A → A` on an arbitrary
  type splits through `‖A‖`. And "constant" (chosen value) ≠ "weakly
  constant" (no chosen value; `id` on a proposition is the example).
- **`‖A‖` is not `¬¬A`.** `A → ¬¬A` only has the universal property for
  doubly-negated propositions `¬¬Q`; the full UP is unprovable, hence the
  postulate. Half the gap closes: `¬¬‖A‖ ≃ ¬¬A` (T6).
- **Surjective ≠ split epi.** `is-surj f` gives `‖fib f b‖`, not a section;
  no map `‖fib f b‖ → fib f b` exists in general. Available instead:
  surjective + embedding = equivalence (I8); propositional goals can be
  checked on the image (I5).
- **`is-surj f` is a proposition but `fib f b` data isn't.** Surjectivity is
  a property of f (Π of propositions); the fibers may carry higher structure.
  Factorize through `im f` (I7) when you need a subtype.
- **Decidability is data, not truth.** `is-decidable A := A + ¬A` is not a
  proposition in general; `‖is-decidable A‖ ≃ is-decidable ‖A‖` (T6). No LEM:
  `P ∨ ¬P` is not provable for arbitrary propositions.
- **Mere equality ≠ identity.** `‖x = y‖` is an equivalence relation on every
  type, but implies `x = y` only when `x = y` is already a proposition (e.g.
  on sets). Its refl/sym/trans come from η of the path operations.
- **Universe discipline in the impredicative encodings.** T11 quantifies over
  `Prop-𝒰`; the encoded truncation satisfies the UP only for propositions in
  that universe, and `Prop-𝒰` itself lives one universe up.
- **Don't over-apply the elimination rule.** "Goal is a proposition" must be
  *proved* (via `truncation-levels.md` techniques), and Π-closure of
  propositions itself carries a funext flag. In axiom-tracked work the flag
  is part of the argument.

## See also

- `truncation-levels.md` — propositions/sets/embeddings; its R3 powers the simplified UP checks; its axiom flags apply here.
- `equivalences.md` — fibers, contractibility; embeddings = propositional-fiber maps; split epis vs surjections (I8).
- `fundamental-theorem.md` — the equivalence engine behind I1–I4 (fiberwise equivalences over X).
- `identity-types.md` — transport, `ap`, `apd`; path algebra behind mere equality and weak constancy.
- `inductive-types.md` — coproduct/Σ universal properties composing with truncation's (T5); `𝟘`, `𝟏`, `bool`.
- `funext.md` — the axiom behind T9 and I5; Π-closure of propositions.
- `univalence.md` — propositional extensionality (sharpens T3/T6); refutes global choice (T10); `Prop-𝒰` is a set (I9).
- `quotients.md` — `‖A‖` as the quotient of A by the total relation (the intuition behind Kraus's theorem).
- `finite-types.md` — `Fin k`; decidable subtypes of finite types satisfy global choice (T10); ∃-stated finiteness.
- `number-theory.md` — well-ordering of ℕ behind the least-witness construction (T10).
- `circle.md` — HITs with loops; `‖A‖` is the degenerate HIT (path constructor between all points).
- `w-types.md` — ordinary inductive types, contrasted with the HIT pattern used to postulate truncation.
- `dependent-type-theory.md` — the underlying judgmental machinery the truncation rules extend.
