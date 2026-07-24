# The hierarchy of truncation levels

Digest of Rijke, *Introduction to HoTT*, §"Propositions, sets, and the higher
truncation levels". The chapter isolates
the bottom of the type hierarchy — contractible types (−2), propositions (−1),
sets (0), and general k-types — and proves the closure theorems and decision
procedures used to place a concrete type at a level.

Dependencies assumed here: contractibility, equivalences, fibers
(`equivalences.md`); the fundamental theorem (`fundamental-theorem.md`); path
algebra and path induction (`identity-types.md`); inductive types and
observational equality (`inductive-types.md`).

**Axiom hygiene.** Every theorem proved *in this chapter* is axiom-free: no
funext, no univalence, no propositional truncation. Several standard facts one
reaches for immediately — `is-prop A` being a proposition, closure of k-types
under Π, propositional extensionality — are **not** proved here; they are
collected under "Deferred results (axiom-flagged)". Do not cite this chapter
for them.

Most of ordinary mathematics takes place at level 0, the sets. Types at
higher levels, or at no finite level, belong to synthetic homotopy theory
(`circle.md`).

## Key definitions

### Propositions

    is-prop A  :=  Π (x y:A). is-contr (x = y)

A type is a **proposition** when its identity types are contractible: any two
elements are equal *in a canonical, contractible way*. Rijke's official
definition is this one; the chapter immediately proves it equivalent to

    is-prop' A  :=  Π (x y:A). x = y        ("any two elements are equal")

and in informal work the two are used interchangeably (SKILL.md uses the
latter). The equivalence is axiom-free.

    Prop-𝒰  :=  Σ (X:𝒰). is-prop X          (universe of small propositions)

Four equivalent conditions (Rijke's characterization proposition, all
axiom-free). For any type A, the following are logically equivalent:

1. A is a proposition (identity types contractible).
2. `is-prop' A`: any two terms of A can be identified.
3. `A → is-contr A`: A is contractible as soon as it is inhabited.
4. `const ⋆ : A → 𝟏` is an embedding.

Condition 3 is the operational workhorse: to prove `is-prop A` you may *assume
an inhabitant* and then show contractibility.

### Sets

    is-set A  :=  Π (x y:A). is-prop (x = y)
    Set-𝒰     :=  Σ (X:𝒰). is-set X         (= 𝒰^≤0)

A set is a type whose equality is a mere property: at most one identification
between any two elements. Also define

    axiom-K A  :=  Π (x:A). Π (p : x = x). refl x = p

### Subtypes

A family `B : A → 𝒰` is a **subtype** of A when each `B x` is a proposition;
then `B x` is a **property** of `x : A`. This is the type-theoretic
replacement for subsets: since terms have unique types, "subcollection of A"
must be a proposition-valued predicate varying over A.

### Embeddings (recalled from `equivalences.md`)

    is-emb f  :=  Π (x y:A). is-equiv (ap f : (x = y) → (f x = f y))

An embedding's identity types are exactly those of its image. Every
equivalence is an embedding.

### Truncation levels

The index type `𝕋` is inductive, with constructors `-2 : 𝕋` and
`succ-𝕋 : 𝕋 → 𝕋` (equivalent to the integers ≥ −2; the inclusion `ℕ → 𝕋`
sends `0 ↦ succ-𝕋 (succ-𝕋 (-2))`). Write `k+1` for `succ-𝕋 k`.

    is-trunc : 𝕋 → 𝒰 → 𝒰        (by recursion on k)
      is-trunc (-2)  A  :=  is-contr A
      is-trunc (k+1) A  :=  Π (x y:A). is-trunc k (x = y)

- A is **k-truncated**, or a **k-type**, if `is-trunc k A` is inhabited.
- A is a **proper (k+1)-type** if it is a (k+1)-type but not a k-type.
- `𝒰^≤k  :=  Σ (X:𝒰). is-trunc k X` — the universe of k-types.
- A map `f : A → B` is **k-truncated** if `fib f b` is k-truncated for each
  `b : B`.

Calibration: contractible = (−2)-type; proposition = (−1)-type; set = 0-type;
equivalence = (−2)-truncated map (via `is-equiv f ≃ is-contr-map f`);
embedding = (−1)-truncated map (R4/R14 below, not the definition).

*Universe subtlety* (Rijke's remark): `is-trunc k` is defined relative to a
universe but is independent of the choice (induction on k; the base case is
judgmental). Omit the universe annotation safely.

**Decidable equality** on A: an element of `Π (x y:A). (x = y) + ¬(x = y)`,
where `¬X := X → 𝟘`. A *function computing* a decision, not a mere truth.

## Key results

Results are tagged R1–R23 for cross-reference. All are axiom-free.

### Results on propositions

- **R1. Contractible ⇒ proposition.** `is-contr A → is-prop A` (uses: identity
  types of contractible types are contractible — exercise from the
  equivalences chapter). Hence `𝟏` is a proposition; `𝟘` too, by 𝟘-induction.
- **R2. Closure under equivalence.** For `e : A ≃ B`:
  `is-prop A ↔ is-prop B`. Proof: equivalences are embeddings, so `ap e` is an
  equivalence and contractibility transports across it.
- **R3. Equivalences between propositions are cheap.** For propositions P and
  Q, a map `f : P → Q` is an equivalence iff *there exists* a map `g : Q → P`.
  Hence `(P ≃ Q) ↔ (P ↔ Q)`. The homotopies `f ∘ g ~ id`, `g ∘ f ~ id` are
  automatic: any two elements of a proposition are equal. What univalence
  later adds is the step from `P ≃ Q` to `P =𝒰 Q` (see Deferred results).

### Results on embeddings and subtypes

- **R4. Embedding iff propositional fibers.** `f : A → B` is an embedding iff
  `fib f b` is a proposition for each `b : B`. Proof skeleton: by the
  fundamental theorem, f is an embedding iff `fib f (f y)` is contractible for
  each `y : A`; transport along `p : f y = b` gives
  `fib f (f y) ≃ fib f b`, reducing this to "each inhabited fiber is
  contractible", i.e. `Π (b:B). fib f b → is-contr (fib f b)` — condition (3)
  of propositionhood, fiberwise.
- **R5. Subtype projections are embeddings.** For a family B over A:
  `pr₁ : Σ (x:A). B x → A` is an embedding iff each `B x` is a proposition
  (since `fib pr₁ x ≃ B x`). **Corollary — subtype equality:** over a
  subtype P, `ap pr₁ : ((x , p) = (y , q)) ≃ (x = y)`. Equality in a subtype
  *is* equality of first components.

### Results on sets

- **R6. ℕ is a set.** `(m = n) ≃ Eq-ℕ m n` (observational equality, via the
  fundamental theorem) and `Eq-ℕ m n` is a proposition by double induction.
- **R7. Axiom K characterization.** `is-set A ↔ axiom-K A`.
  (⇒) `x = x` is a proposition, so any `p : x = x` equals `refl x`.
  (⇐) For `p q : x = y`: `p ∙ q⁻¹ : x = x`, so K gives `p ∙ q⁻¹ = refl x`,
  and path algebra yields `p = q`.
- **R8. The engine: propositional reflexive relations.** Let `R : A → A → 𝒰`
  with (i) each `R x y` a proposition, (ii) reflexivity `ρ : Π (x:A). R x x`,
  (iii) a family of maps `Π (x y:A). R x y → (x = y)`. Then *any* family
  `Π (x y:A). (x = y) → R x y` is a family of equivalences — and A is a set.
  Proof idea: path induction from `ρ x` gives `(x = y) → R x y`; composed
  with (iii), `R x y` is a retract of `x = y` (the round trip on `R x y` is
  the identity since `R x y` is a proposition). Hence `Σ (y:A). R x y` is a
  retract of the contractible singleton `Σ (y:A). (x = y)`, so contractible;
  the fundamental theorem makes the family an equivalence; finally
  `(x = y) ≃ R x y` is a proposition by R2.
- **R9. Hedberg's theorem: decidable equality ⇒ set.** Given
  `d : Π (x y:A). (x = y) + ¬(x = y)` and a universe 𝒰 containing A, define
  by coproduct induction `R' x y : ((x = y) + ¬(x = y)) → 𝒰` with
  `R' x y (inl p) := 𝟏`, `R' x y (inr p) := 𝟘`; set `R x y := R' x y (d x y)`.
  Then R is proposition-valued, reflexive (at `x x`: if `d x x` is `inl p`
  take `⋆`; if `inr np`, `ex-falso (np (refl x))`), and implies identity via
  `f (inl p) r := p`, `f (inr np) r := ex-falso r`. Apply R8.
- **R10. Consequences.** `bool` is a set (exercise: observational equality +
  R8). `Fin k` is a set (decidable equality — `finite-types.md`). `ℤ` is a
  set (exercise: coproducts of (k+2)-types). Posets have underlying sets
  (exercise).

### Results on truncation levels

- **R11. Cumulativity.** `is-trunc k A → is-trunc (k+1) A`. Base: contractible
  ⇒ proposition; step: identity types of (k+1)-types are k-types, apply the
  induction hypothesis fiberwise. **Corollary:** identity types of k-types are
  themselves k-types.
- **R12. Closure under equivalence.** If `e : A ≃ B` and B is a k-type, so is
  A. Induction on k; the step uses that `ap e` is an equivalence.
- **R13. Embedding into a (k+1)-type.** If `f : A → B` is an embedding and B
  is a (k+1)-type, so is A (identity types of A ≃ identity types of B; apply
  R12). In particular: embedded in a set ⇒ set; embedded in a proposition ⇒
  proposition.
- **R14. Truncated maps via ap.** `f : A → B` is (k+1)-truncated iff
  `ap f : (x = y) → (f x = f y)` is k-truncated for all `x y : A`.
  Generalizes R4 (k = −1: ap f (−2)-truncated ⇔ equivalence). Key
  computation: for `s t : fib f b`,
  `(s = t) ≃ fib (ap f) (pr₂ s ∙ (pr₂ t)⁻¹)` — by Σ-induction, the Σ-identity
  characterization, and path algebra.
- **R15. Σ-closure** (exercise). For B over a k-type A:
  `(Π (x:A). is-trunc k (B x))  ↔  is-trunc k (Σ (x:A). B x)`.
- **R16. Maps into k-types** (exercise). For `f : A → B` with B a k-type:
  `is-trunc k A  ↔  f is a k-truncated map`.
- **R17. Retracts** (exercise). If A is a retract of a k-type B (section i,
  retraction r, `H : r ∘ i ~ id`), then A is a k-type: identity types of A are
  retracts of identity types of B; truncation passes along retracts.
- **R18. Products** (exercise). `A × B` is (k+1)-truncated iff
  `B → is-trunc (k+1) A` and `A → is-trunc (k+1) B`. Hence for *inhabited*
  A and B: `A × B` is a k-type iff both are.
- **R19. Coproducts** (exercise). If A and B are (k+2)-types, so is `A + B`.
  For propositions P, Q: `P + Q` is a proposition iff `P → ¬ Q`; and
  `is-contr (P + Q) ↔ P ⊕ Q` where `P ⊕ Q := (P × ¬Q) + (Q × ¬P)`.
- **R20. The diagonal** (exercise). For `δ_A := λx. (x , x) : A → A × A`:
  `fib δ_A (x , y) ≃ (x = y)`; `is-equiv δ_A ↔ is-prop A`; and A is
  (k+1)-truncated iff `δ_A` is k-truncated.
- **R21. Fiber inclusions** (exercise). A is (k+1)-truncated iff for every
  family B over A and `a : A`, `i_a := λy. (a , y) : B a → Σ (x:A). B x` is
  k-truncated. Over a set, every fiber inclusion is an embedding.
- **R22. Isolated elements** (exercise). `a : A` is **isolated** if
  `Π (x:A). (a = x) + ¬(a = x)` — equivalently, `const a : 𝟏 → A` has
  decidable fibers. Then `a = x` is a proposition for every `x : A`, and
  `const a` is an embedding.
- **R23. Arithmetic embeddings** (exercises). `add m : ℕ → ℕ` is an embedding,
  giving `(m ≤ n) ≃ Σ (k:ℕ). m + k = n`; `mul m` is an embedding for `m > 0`,
  so divisibility `d ∣ n` is a proposition for `d > 0`. Injective maps into
  sets are embeddings, with automatically-a-set domains.

### Deferred results (axiom-flagged — NOT proved in this chapter)

True and used constantly, but proved later. Track the flags:

- **`is-prop A` is a proposition** — needs **funext** (`funext.md`); likewise
  `is-set A` and `is-trunc k A`. (Identifying two elements of `is-prop A`
  means identifying dependent functions — exactly what funext licenses.)
- **k-types closed under Π** — needs **funext**: if each `B x` is a k-type,
  so is `Π (x:A). B x`. Base case (Π of contractibles is contractible) is
  weak funext, which is equivalent to funext.
- **`is-equiv f` is a proposition** — needs **funext**. Only then are two
  equivalences `A ≃ B` equal iff their underlying maps are equal
  (subtype-style reasoning on `Σ (f : A → B). is-equiv f`).
- **Propositional extensionality**: `(P ↔ Q) → (P =𝒰 Q)` — needs
  **univalence** (`univalence.md`); R3 reaches only `P ≃ Q`. With univalence,
  `Prop-𝒰` itself is a set.
- **Refutation of global axiom K / UIP** — needs **univalence**:
  `(bool =𝒰 bool) ≃ (bool ≃ bool)` has two distinct elements (`id`,
  `neg-bool`), so the universe is not a set.

### Axiom K / UIP discussion

- `axiom-K A := Π (x:A). Π (p : x = x). refl x = p`; uniqueness of identity
  proofs is `UIP A := Π (x y:A). Π (p q : x = y). p = q`. UIP A is *literally*
  `is-set A`; R7 shows the seemingly weaker axiom K is equivalent to it
  (self-loops suffice, via the `p ∙ q⁻¹` trick).
- Path induction **cannot** prove axiom K: it needs a free endpoint, and
  `p : x = x` has both endpoints fixed. Bare Martin–Löf type theory neither
  proves nor refutes "all types are sets".
- If all types satisfied K, type theory would be set-level: every identity
  type a proposition, identity proofs unique, no higher structure. Consistent
  on its own (assumed in some older formalizations), but **incompatible with
  univalence**, which exhibits universes with non-trivial identity types.
  Univalent foundations is precisely the refusal of global axiom K.

## Reasoning idioms

- **Locate the goal on the hierarchy first.** If the goal is a proposition,
  *any* inhabitant suffices — simplify the goal aggressively (replace by an
  equivalent type, transport, unfold) before constructing anything.
- **To show A is a proposition**, try in order: (a) give `Π (x y:A). x = y`
  directly; (b) give `A → is-contr A` — assume an inhabitant, then show
  contractibility; (c) exhibit `A ≃ P` for a known proposition P (R2);
  (d) embed A into a proposition (R13).
- **Equivalences between propositions: maps back and forth only.** Never build
  homotopies by hand when both sides are propositions — R3 makes them
  automatic.
- **To show A is a set: find decidable equality, apply Hedberg** (R9). It
  dispatches `ℕ`, `bool`, `Fin k`, `ℤ`, `ℚ`, lists over sets, etc. — build
  the decision by induction, reusing observational equality. No decidability?
  Use R8: a reflexive, proposition-valued relation implying identity (the
  Eq-ℕ pattern). Fallbacks: exhibit `A ≃ S` or an (injective) map `A ↪ S`
  into a known set S (R12, R13, R23).
- **Subtype equality reduces to base equality.** To identify
  `(x , p) = (y , q)` in `Σ (x:A). P x`, prove only `x = y` (R5). Applies to
  `Prop-𝒰`-valued data, equivalences-as-pairs, and anything packaged as
  "base + proposition".
- **To show f is an embedding**: show fibers are propositions, or `ap f` is
  an equivalence; if the codomain is a set, plain injectivity suffices (R23).
- **Shift map truncation one level**: f is (k+1)-truncated iff `ap f` is
  k-truncated (R14) — iterate to reduce map statements to path spaces.
- **To show A is a k-type (k ≥ 0)**: show identity types are (k−1)-types and
  recurse; or use closure under ≃, embeddings, retracts, Σ (fibers at level
  k), or Π (**funext — flag it**).
- **Interchangeability of proofs.** Two elements of a proposition are equal:
  never case-split on *how* a propositional hypothesis was proved.
- **Hedberg's hypothesis is computational** — a dependent function returning
  `inl`/`inr`. Write it as a decision algorithm by structural recursion, not
  as classical case analysis.

## Pitfalls

- **`is-prop A` is `Π (x y:A). x = y` — NOT `Π (x:A). x = x`.** The latter is
  inhabited by `λx. refl x` for *every* type and says nothing. Two
  independently quantified endpoints are essential.
- **k-types are not closed under Σ in general.** Closure needs a k-truncated
  base *and* k-truncated fibers (R15). Dropping the fiber condition destroys
  the bound: `Σ (x:𝟏). B x ≃ B ⋆` is arbitrary though 𝟏 is contractible, and
  `Σ (X:𝒰). X` has no finite truncation level (with univalence). Σ can
  *raise* the level; Π (given funext) cannot.
- **"Assume an inhabitant" ≠ "choose a canonical one."** `A → is-contr A`
  gives contractibility from an *arbitrary* inhabitant; no preferred element
  may be supposed.
- **Embedding ≠ injective in general.** `is-emb f` is coherent structure on
  all path spaces; bare injectivity implies embedding only when the codomain
  is a set.
- **Hedberg needs genuine decidable equality.** A mere proposition
  `‖(x = y) + ¬(x = y)‖` supplies no decision function. Deciding equality for
  one pair proves nothing global (but one isolated point gives local
  structure: R22).
- **Don't silently use the deferred results.** `is-prop A` a proposition,
  Π-closure of k-types, `is-equiv f` a proposition: **funext**. `P = Q` from
  `P ↔ Q`: **univalence**. In axiom-tracked proofs the flags are part of the
  statement.
- **Levels are cumulative lower bounds.** Every k-type is a (k+1)-type (R11);
  "A is a (k+1)-type" does not deny k-truncation — "proper (k+1)-type" says
  that. If asked for "0-type" of a proposition, cumulativity already applies.
- **The hierarchy starts at −2**: contractible = −2, proposition = −1,
  set = 0. Sanity-check `is-trunc` statements against
  `is-trunc (k+1) A ⟺ identity types of A are k-truncated`.
- **Retract closure needs full data** (`i`, `r`, `H : r ∘ i ~ id`). A bare
  pair of maps without the homotopy is not a retract (R17).
- **Path induction cannot touch self-loops.** Needing `p = refl x` for
  `p : x = x` is axiom K — independent of the bare theory. First prove the
  type is a set (Hedberg, embedding, R8); then K is free (R7).
- **`Prop-𝒰` and `𝒰^≤k` live one universe up** from 𝒰; they are not small.
  Mind universe levels when quantifying over propositions.

## See also

- `identity-types.md` — path induction, transport, `ap`, groupoid laws, the
  Σ-identity characterization (R7, R8, R14).
- `equivalences.md` — contractibility, fibers, `is-equiv`; embeddings defined;
  contractibles closed under equivalences and retracts.
- `fundamental-theorem.md` — the fundamental theorem: engine behind R4 and R8;
  `Eq-ℕ` and observational equality (R6).
- `universes.md` — universe levels; families into 𝒰 (Hedberg's `R'`); `𝒰^≤k`
  as a subtype of a universe.
- `funext.md` — the deferred Π-side: `is-prop`/`is-trunc` are propositions,
  Π-closure of k-types, `is-equiv` is a proposition.
- `logic-truncation.md` — propositions as the home of logic; `‖A‖`, `∃`, `∨`;
  when to truncate vs. use raw Σ.
- `univalence.md` — propositional extensionality; `Prop-𝒰` is a set;
  refutation of global axiom K.
- `inductive-types.md` — `𝟘`, `𝟏`, `bool`, coproducts, `ℕ`; the induction
  principles behind decision procedures.
- `finite-types.md` — `Fin k`; decidable equality of finite types; counting.
- `quotients.md` — set quotients: imposing equality to force a type to level 0.
- `groups.md` — groups are sets by definition; subtypes in action (subgroups).
- `circle.md` — S¹ as the first proper 1-type; `Ω S¹ ≃ ℤ`; life above level 0.
- `number-theory.md` — decidable equality in practice; `≤` and divisibility as
  propositions on ℕ (R23).
