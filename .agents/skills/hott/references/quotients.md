# Set quotients

Digest of Rijke, *Introduction to HoTT*, §"Set quotients".
The chapter constructs the quotient
A/R of a type by an equivalence relation as the type of equivalence classes —
literally the image of R : A → (A → Prop-𝒰) — proves **effectiveness**
((q x = q y) ≃ R x y) via the fundamental theorem, proves the **universal
property**, and fixes the size problem with the **replacement axiom**.
Applications: congruence quotients ℕ → Fin (k+1), the rationals as reduced
fractions, set truncations ‖A‖₀ as quotients by x,y ↦ ‖x = y‖.

Dependencies: `fundamental-theorem.md`, `equivalences.md` (embeddings,
surjections, image factorization), `truncation-levels.md`,
`logic-truncation.md`, `funext.md`, `univalence.md` (propositional
extensionality), `universes.md` (smallness, successor universes).

**Axiom hygiene.** This chapter is axiom-heavy — a change from earlier ones.
*Everything* below uses **funext** and **univalence** (via propositional
extensionality (P = Q) ≃ (P ↔ Q)); **propositional truncation** is native to
the statements. The **replacement axiom** is newly assumed here and is the
chapter's only route to 𝒰-smallness of A/R, ‖A‖₀, 𝔽, 𝒰_A — flag it wherever
smallness is invoked. Nothing on this page is axiom-free unless stated.

## Key definitions

### Equivalence relations

    Eq-Rel-𝒰(A) := Σ (R : A → A → Prop-𝒰). reflexive R × symmetric R × transitive R
    reflexive  R := Π (x:A). R x x                          (ρ)
    symmetric  R := Π (x y:A). R x y → R y x                (σ)
    transitive R := Π (x y z:A). R x y → R y z → R x z      (τ)

R is **proposition-valued**: R x y : Prop-𝒰. Since Π into propositions is a
proposition (funext), the ρστ-data is a mere property of R — Eq-Rel-𝒰(A) is a
subtype of A → A → Prop-𝒰, and equality of relations is pointwise ↔ (funext +
propositional extensionality).

### Equivalence classes and the quotient

    is-equivalence-class P := ∃ (x:A). ∀ (y:A). P y ↔ R x y     (P : A → Prop-𝒰)
    A/R    := Σ (P : A → Prop-𝒰). is-equivalence-class P
    [x]_R  := R x                     (witness x : ∀ y. R x y ↔ R x y)
    q_R    := λx. [x]_R : A → A/R

By funext + propositional extensionality, is-equivalence-class P ≃ ‖fib R P‖,
so **A/R is the image of R : A → (A → Prop-𝒰)**: the factorization
R ~ i_R ∘ q_R has i_R : A/R ↪ (A → Prop-𝒰) an embedding and q_R surjective.
A/R is a set: Prop-𝒰 is a set (univalence), A → Prop-𝒰 is a set (funext), and
subtypes of sets are sets.

### Locally small types

    is-locally-small-𝒰 A := Π (x y:A). is-small-𝒰 (x = y)

(is-small-𝒰 X := Σ (X':𝒰). X ≃ X', a proposition by univalence.) A map is
locally 𝒰-small if its fibers are. Facts: (1) 𝒰-small ⇒ locally 𝒰-small;
(2) propositions are locally 𝒰-small for any 𝒰; (3) a univalent universe 𝒰 is
locally 𝒰-small, since (A = B) ≃ (A ≃ B) : 𝒰 [univalence]; (4) Π over a
𝒰-small base of locally 𝒰-small types is locally 𝒰-small — hence A → Prop-𝒰
is locally 𝒰-small, since (P = Q) ≃ (P ↔ Q) : 𝒰 [funext, univalence].

### The replacement axiom (assumed)

**Axiom (replacement).** For every universe 𝒰 and every map f : A → B from a
𝒰-small type A into a locally 𝒰-small type B, the image im f is 𝒰-small.

The type-theoretic analog of ZF replacement ("the image of a set is a set");
mild, since provable once universes are closed under suitable higher inductive
types. Consequences (each an image of a small type into a locally small
codomain):

- 𝒰_A := Σ (X:𝒰). ‖X ≃ A‖ (the component of A in 𝒰) is 𝒰-small — image of
  const_A : 𝟏 → 𝒰.
- 𝔽 := Σ (X:𝒰). ‖Σ (k:ℕ). X ≃ Fin k‖ (all finite types) is 𝒰-small — image
  of Fin : ℕ → 𝒰.
- **A/R is 𝒰-small** — image of R : A → (A → Prop-𝒰).

### The universal property

For q : A → B into a **set** B with H : Π (x y:A). R x y → (q x = q y), define

    q* : (B → X) → Σ (f : A → X). Π (x y:A). R x y → (f x = f y)
    q* h := (h ∘ q, λx y r. ap h (H x y r))

q **is a set quotient of R** (satisfies the universal property) if q* is an
equivalence for every set X. Two observations: the property is quantified over
**sets only**; and since X is a set, the R-compatibility component is a
proposition (funext) — extending along q is a *property* of f, not structure.

### Partitions, representatives, set truncations

    𝒫⁺-𝒰(A)          := Σ (Q : A → Prop-𝒰). ‖Σ (a:A). Q a‖      (inhabited subtypes)
    is-partition P   := Π (x:A). is-contr (Σ (Q : 𝒫⁺-𝒰(A)). P Q × Q x)
    Partition-𝒰,𝒱(A) := Σ (P : 𝒫⁺-𝒰(A) → Prop-𝒱). is-partition P

Every element lies in a *unique* block. A family C : A → 𝒰 is a **choice of
unique representatives** if

    is-choice-of-representatives C := Π (x:A). is-contr (Σ (y:A). C y × R x y)

f : A → B into a set B is a **set truncation** if (− ∘ f) : (B → X) → (A → X)
is an equivalence for every set X. A type is **connected** if

    is-conn A := is-contr ‖A‖₀        (map connected: all fibers connected)

## Key results

R1. **Effectiveness** (prp:eq-quotient, cor:eq-quotient). For P an equivalence
class, the canonical map ([x]_R = P) → P x is an equivalence; hence

    ([x]_R = [y]_R) ≃ R x y.

Proof: fundamental theorem — Σ (P : A/R). P x is contractible with center
([x]_R, ρ x). For the contraction, P(x) yields (∃-elimination into the
proposition goal) a y with P = [y]_R and R x y; then [x]_R = [y]_R since by
funext + prop-ext it suffices Π z. R x z ↔ R y z, which σ and τ supply.
[funext, univalence, truncation]

R2. **Size of the raw construction.** Prop-𝒰 lives in the successor universe
𝒰⁺, so the subtype A/R ≤ (A → Prop-𝒰) is a 𝒰⁺-type as constructed (likewise
in any 𝒱 ⊇ 𝒰, A). **Replacement** makes A/R essentially 𝒰-small. [replacement]

R3. **The quotient theorem** (thm:quotient_up). For q : A → B into a set B
(B not assumed in 𝒰), TFAE:
(i) q respects R and satisfies the universal property;
(ii) q is **surjective and effective**: (q x = q y) ≃ R x y for all x y;
(iii) R extends along q to an embedding i : B ↪ (A → Prop-𝒰) satisfying the
image universal property of R.
Notable step in (ii)⇒(iii): with B outside 𝒰, i b a := (b = q a) is not
𝒰-valued; but surjectivity + effectiveness make B locally 𝒰-small (is-small-𝒰
is a proposition — check on representatives), so set i b a := pr₁ (s(b,a)).
[funext, univalence, truncation]

R4. **Corollary.** q_R : A → A/R is surjective, effective, and a set quotient:
the image construction delivers the universal object.

R5. **Equivalence relations = surjections into sets** (thm:eqrel-surj):

    Eq-Rel-𝒰(A) ≃ Σ (X : Set-𝒰). (A ↠ X).

Forward: quotient (needs **replacement** to land A/R back in Set-𝒰). Backward:
the **kernel** K_f x y := (f x = f y), proposition-valued because X is a set.
Round trips use effectiveness and the univalence computation of equality in
the RHS as Σ (e : Y ≃ X). e ∘ g ~ f. Moral: every surjection into a set is the
quotient by its own kernel. [replacement, univalence, funext]

R6. **Equivalence relations = partitions** (thm): Eq-Rel-𝒰(A) ≃ Partition-𝒰,𝒱(A)
for 𝒱 containing A and every type of 𝒰. Forward: blocks are the equivalence
classes; contractibility of "the block containing x" reduces to Q = R x.
Backward: R_P x := the unique block containing x (the center of contraction);
symmetry/transitivity come from contractibility. [univalence, funext]

R7. **Choice of representatives gives the quotient without replacement**
(thm:choice-of-representatives). If C is a choice of representatives with
centers (h x, c x, r x), then q x := (h x, c x) : A → Σ (x:A). C x is a set
quotient of R: Σ (x:A). C x is a set with ((x,c) = (y,d)) ≃ R x y, q is
effective, and pr₁ : Σ (x:A). C x → A is a **section** of q (q is split
surjective). Since Σ (x:A). C x sits at A's own level, no replacement is
needed — the preferred construction whenever canonical forms exist.

R8. **Worked examples.**

- *Congruence:* x ↦ [x]_{k+1} : ℕ → Fin (k+1) is effective and split
  surjective, hence (R3) the set quotient of x ≡ y (mod k+1). Choice of reps:
  C y := fib (nat-Fin) y for the inclusion nat-Fin : Fin (k+1) → ℕ.
- *Rationals:* fractions Q := ℤ × Σ (y:ℤ). y ≠ 0 with
  (x,y) ~ (x',y') := (x·y' = x'·y); the reduced-fraction predicate
  C(x,y) := (y > 0) ∧ (gcd(x,y) = 1) is a choice of representatives
  (normalize sign, divide out the gcd). ℚ := Σ ((x,y):Q). C(x,y), with
  (x,y) ↦ x/y the quotient map. Note: **ℤ itself is not a quotient here** —
  it is built earlier as an inductive type; ℚ is the quotient.
- *Set truncation:* quotient by x,y ↦ ‖x = y‖ (R9).

R9. **Set truncation theorem** (thm:set-truncation). For f : A → B into a set
B, TFAE:
(i) f is a set truncation: (− ∘ f) : (B → X) ≃ (A → X) for every set X;
(ii) **dependent universal property**: for every family X of sets over B,
    (− ∘ f) : (Π (b:B). X b) ≃ (Π (a:A). X (f a));
(iii) f is surjective and (f x = f y) ≃ ‖x = y‖ for all x y.
Corollaries: every A : 𝒰 has η : A → ‖A‖₀ with ‖A‖₀ : Set-𝒰 [**replacement**
applied to the quotient by x,y ↦ ‖x = y‖]; η is surjective and
(η x = η y) ≃ ‖x = y‖. Interpretation: ‖A‖₀ is the **set of connected
components** of A. Connected types are inhabited: ‖A‖ ≃ (‖A‖₀ → ‖A‖) when
‖A‖₀ is contractible.

R10. **Connected = set truncation** (thm:unit-set-truncation-connected).
f : A → B into a set is a set truncation iff f is connected (every fiber has
contractible ‖·‖₀). Forward uses the dependent universal property (R9 ii).

R11. **Uniqueness of the quotient** (exercise). The type
Σ (X:𝒰). Σ (f : A ↠ X). Π (x y:A). (f x = f y) ≃ R x y is contractible: a
quotient is pinned down uniquely as soon as it is surjective and effective.

R12. **Higher truncations** (remark). For every k there is η : A → ‖A‖ₖ with
(‖A‖ₖ → X) ≃ (A → X) for every k-type X; the chapter refers to the HoTT book
ch. 7 for the general (HIT) construction.

## Reasoning idioms

I1. **Define f : A/R → B (B a set):** give f̄ : A → B on representatives plus
R-compatibility H : Π (x y:A). R x y → (f̄ x = f̄ y). The equivalence q* yields
h : A/R → B with h ∘ q ~ f̄, and the type of extensions is contractible
(unique up to a unique identification). Computation on points: h [x]_R = f̄ x —
propositionally, via the homotopy.

I2. **Prove a proposition P b for all b : A/R:** q is surjective and
precomposition with a surjection is an equivalence on proposition-valued
families, so it suffices to prove P (q a) for all a : A. "WLOG the element is
a representative" — *only* for proposition-valued goals. (Used repeatedly
inside R3's proof.)

I3. **Prove q x = q y in a quotient:** show R x y (effectiveness R1, backward
direction). **Extract information from q x = q y:** you get R x y, nothing
stronger. Both directions are propositional — never judgmental.

I4. **Prove R = S for two equivalence relations:** by funext + propositional
extensionality, suffices Π (x y:A). R x y ↔ S x y.

I5. **Define out of ‖A‖₀ into a set X:** just give f : A → X — no
compatibility needed, since any map into a set respects ‖x = y‖ (truncate
‖x = y‖ into the proposition f x = f y, then ap). Dependent case (R9 ii): to
get Π (b:‖A‖₀). X b for a family of sets, give Π (a:A). X (η a).

I6. **Prove η x = η y in ‖A‖₀:** exhibit any identification x = y (then
‖x = y‖ holds and effectiveness applies). The identity type of the set
truncation is *exactly* "merely equal".

I7. **Build a quotient without replacement (canonical forms):** exhibit a
choice of representatives C with normalization h : A → A, C (h x), R x (h x),
and contractibility of Σ (y:A). C y × R x y per class. The quotient is the
subtype of canonical forms, q is normalization, pr₁ is its section
(ℚ-as-reduced-fractions, ℕ → Fin (k+1)); the quotient stays at A's level.

I8. **Show a set X is the quotient A/R:** either exhibit a surjective
effective f : A ↠ X ((f x = f y) ≃ R x y) and invoke uniqueness R11, or show
X satisfies the same universal property. With only a surjection, the
conclusion is X ≃ A/K_f — quotient by the kernel, not by your favorite R.

I9. **Eliminate ∃-defined structure:** is-equivalence-class P is an ∃; to use
it toward a proposition goal, immediately assume a concrete x with
∀ y. P y ↔ R x y (standard ∃-elimination, `logic-truncation.md`).

I10. **Work with surjections via their kernels:** to compare quotients
(A/R ≃ A/S), compare kernels: R x y ↔ S x y (I4). Surjections into sets are
classified by their kernels (R5).

## Pitfalls

P1. **A/R is not small without replacement.** As constructed,
A/R ≤ (A → Prop-𝒰) : 𝒰⁺. Any step that needs A/R : 𝒰 — iterating quotients,
R5's equivalence, ‖−‖₀ : 𝒰 → Set-𝒰, 𝒰_A and 𝔽 small — must invoke the
replacement axiom, or use a choice of representatives (R7) to bypass it. Flag
the axiom when you use it.

P2. **q x = q y is R x y — not judgmental, not automatic.** [x]_R ≡ R x holds
definitionally as subtypes, but an identification q x = q y exists only
propositionally, constructed through funext + univalence (effectiveness).
Never try `refl` to close a quotient equality; never compute through it.

P3. **The universal property quantifies over sets only.** R-compatible maps
A → X do *not* determine maps A/R → X for a general (higher) type X. Set
quotients add no higher structure — A/R is always a set. For higher targets
use higher quotients/HITs (e.g. S¹, `circle.md`); the replacement axiom itself
is justified by closure of universes under such HITs.

P4. **Surjectivity is truncated:** is-surj q := Π b. ‖fib q b‖ supplies no
choice of preimages B → A. "Pick a preimage" is legitimate only inside a
proposition-valued goal (I2), or with a genuine section (R7's pr₁, split
surjections like ℕ → Fin (k+1)).

P5. **Compatibility is data but a mere proposition** when the target is a set
(funext: Π into a proposition). So "unique extension" means the extension type
is contractible; no coherence choices to track. But compatibility must still
be *constructed* — a bare f̄ : A → B never extends on its own.

P6. **Choice of representatives is extra structure, often unavailable.** When
it exists, quotient = subtype of A (low universe level, no replacement). When
it doesn't — e.g. for ‖A‖₀ — insisting on representatives is a choice
principle: the exercise bool/∼_P (true ∼ false iff P) shows AC implies LEM
using exactly such a quotient. Don't assume canonical forms exist.

P7. **‖A‖₀ ≠ ‖A‖.** η x = η y iff ‖x = y‖ (merely equal): the set truncation
remembers connected components. The propositional truncation identifies
everything. Connected means ‖A‖₀ contractible — stronger than ‖A‖ inhabited
(which it then implies).

P8. **Kernels need set targets.** K_f x y := (f x = f y) is proposition-valued
only because X is a set. To "quotient" by a type-valued relation, first
truncate it propositionally (as in ‖x = y‖ for set truncations) or use HIT
quotients — outside this chapter's scope.

P9. **Effectiveness is a condition, not a vibe.** For a surjection into a set,
(f x = f y) ≃ R x y must be proved (otherwise f is only the quotient by K_f).
R3 (ii)↔(i) says effectiveness *is* the universal property — use whichever
side is cheaper.

P10. **Universe bookkeeping in partitions:** R6 needs two universes, with 𝒱
containing A and all of 𝒰. And 𝒫⁺-𝒰(A) requires inhabited blocks
(‖Σ (a:A). Q a‖) — a partition into possibly-empty blocks is not this notion.

## See also

- `fundamental-theorem.md` — contractible-total-space engine behind R1 and R3.
- `equivalences.md` — embeddings, surjections, fibers, image factorization;
  sections and retracts (R7, R5).
- `truncation-levels.md` — propositions, sets, subtypes; A/R is a set as a
  subtype of the set A → Prop-𝒰.
- `logic-truncation.md` — ∃, ‖A‖, surjectivity as ‖fib‖; elimination into
  propositions (I2, I9).
- `funext.md` — equality of relations/subtypes via pointwise ↔ (I4).
- `univalence.md` — propositional extensionality; univalent universes locally
  small; equality of structured types as equivalences (R5).
- `universes.md` — is-small, 𝒰⁺; home of the size problem and replacement.
- `identity-types.md` — ap, transport; identity types of subtypes and Σ-types.
- `inductive-types.md` — bool (the ∼_P exercise), ℕ (congruence), coproducts.
- `finite-types.md` — Fin (k+1) as the quotient of ℕ mod k+1; 𝔽 small by
  replacement.
- `number-theory.md` — congruence mod k, gcd, coprimality feeding ℚ; ℤ as the
  base ring (not a quotient).
- `groups.md` — downstream: quotient groups via congruence relations; kernels
  of homomorphisms.
- `circle.md` — higher quotients/HITs when the universal property must hold
  into arbitrary types, not just sets (P3).
- `dependent-type-theory.md` — Π/Σ/λ grammar used throughout.
- `w-types.md` — contrast: W-types build well-founded trees; quotients impose
  equations.
