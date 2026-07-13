# Rijke — Introduction to Homotopy Type Theory

The library's **foundational reference**: the underlying formalism
of kitcat is univalent mathematics, and this is the standard text
for it. Every role that reasons mathematically — analyzer, coder,
reviewer, researcher, ingest, writer — draws on it for the idiom.

## Citation

Egbert Rijke. *Introduction to Homotopy Type Theory*.
arXiv:2212.11082 [math.LO], December 2022.
<https://arxiv.org/abs/2212.11082>. (A revised version of the
author's lecture notes; later published by Cambridge University
Press, 2025.)

## Vetting

PROVISIONAL. Ingested 2026-07-12 by Claude (Opus 4.8) at Lane's
direction (R7 — the foundational-source standard), via the
ingestion protocol: the arXiv LaTeX e-print fetched directly
(`curl https://arxiv.org/e-print/2212.11082`), the canonical
artifact hashed, and the source tree read for the section map
below. The document hash was checked stable across two independent
fetches. This entry becomes vetted only on Lane's confirmation; no
load-bearing citation rests on a PROVISIONAL entry.

## Files

Canonical format: **LaTeX source** (an arXiv e-print). All vendored
and derived forms are gitignored; only this README is tracked.

- `rijke-hott.tar.gz` — the canonical artifact (the arXiv e-print
  source tarball). This is the file the hash below is of.
- the extracted LaTeX tree beside it — `hott-intro.tex` (the main
  file: `\input`s the parts), the three part files
  (`chapter-type-theory.tex`, `chapter-univalent-foundations.tex`,
  `chapter-circle.tex`), and one `.tex` per lecture (mapped below),
  plus `bibliography.bib` and `cambridge7A.cls`.

Grep the lecture `.tex` for a definition; jump with
`sed -n 'A,Bp' <lecture>.tex`.

## Document hash

sha256 of the canonical artifact (the e-print tarball), stable
across independent arXiv fetches:

```
562be57f5f652004b7f0a816a9196b417f661e1f21f203e7a99f1fa034cb628d  rijke-hott.tar.gz
```

Fallback if the gzip wrapper ever varies — sha256 of the inner
(uncompressed) tar, `gunzip -c rijke-hott.tar.gz | shasum -a 256`:

```
51ad7e31941f4959b8241c3e6c5518dac0cb750a87f731bc27cbe17a41a70b7f
```

## Section map

Three parts (`hott-intro.tex:170–172`), each `\input`ing one
`.tex` per lecture. Every lecture below lists its subsections and
its load-bearing definitions and theorems with the line in the
named `.tex` file, so a citation resolves at `<lecture>.tex:LINE`.
(Line numbers are of the vendored e-print source, hashed below.)

### Part I — Martin-Löf’s Dependent Type Theory (`chapter-type-theory.tex`)

#### `dtt.tex` — Dependent type theory

Develops the raw syntax of Martin-Löf dependent type theory: the four judgment forms, contexts as lists of variable declarations, type families and their sections, and the six sets of structural inference rules (conversion, substitution, weakening, generic element) that make derivations.

*Subsections:* Judgments and contexts in type theory (`:7`), Type families (`:79`), Inference rules (`:109`), Derivations (`:310`)

Key items:
- Definition — The four kinds of judgment in Martin-Löf type theory (A type; a : A; type equality; element equality, in context) `:32`
- Definition — Context — a finite list of variable declarations, each well-formed given the earlier ones `:59`
- Definition — Type family (indexed type): B(x) a type in context Γ, x : A `:83`
- Definition — Section of a type family — an element b(x) : B(x) in context Γ, x : A `:98`
- Definition — Fiber B(a) and value b(a): substitution of a term for the family's variable `:273`
- Definition — The structural rules — the six sets of inference rules underlying type dependency `:111`
- Definition — Variable conversion rules (stated once via a generic judgment thesis 𝒥) `:216`
- Definition — The substitution rule (generic judgment 𝒥 substituted along a : A) `:253`
- Definition — The weakening rule — extending the context by a fresh variable preserves judgments; constant/trivial family `:282`
- Definition — The generic element / variable rule — the hypothetical x : A is an element; provides the identity function `:302`

#### `pi.tex` — Dependent function types

Introduces dependent function types (Π-types) through their four principal rules — formation, introduction (λ-abstraction), elimination (evaluation), and computation (β/η) — then specializes to ordinary function types A→B and derives the identity function, composition, and the category laws (associativity and unit laws) for functions.

*Subsections:* The rules for dependent function types (`:8`), Ordinary function types (`:104`)

Key items:
- Definition — Π-formation rule (dependent function type ∏(x:A) B(x)) `:26`
- Definition — λ-abstraction (Π-introduction rule) `:46`
- Definition — evaluation (Π-elimination rule) `:71`
- Definition — β- and η-rules (Π-computation rules) `:87`
- Definition — ordinary function type A→B ≐ ∏(x:A) B `:115`
- Definition — identity function id_A : A→A `:225`
- Definition — composition of functions g∘f `:273`
- Lemma — associativity of function composition `:320`
- Lemma — left and right unit laws for composition (lem:fun_unit) `:350`

#### `nat.tex` — The natural numbers

Specifies ℕ as the archetypal inductive type via its four rule-sets (formation, introduction with zero and successor, induction principle, computation rules), then constructs addition by induction on ℕ and introduces pattern matching as the idiom for recursive definitions.

*Subsections:* The formal specification of the type of natural numbers (`:19`), Addition on the natural numbers (`:152`), Pattern matching (`:239`)

Key items:
- Definition — ℕ-formation rule (ℕ is postulated to be a type in the empty context) `:28`
- Definition — introduction rules: the zero element zeroℕ : ℕ and the successor function succℕ : ℕ → ℕ `:40`
- Definition — the induction principle indℕ (the type-theoretic elimination rule for ℕ: base case p₀ and inductive step pS) `:69`
- Remark — indℕ presented as a function; interderivability with the ℕ-ind rule `:89`
- Definition — computation rules for ℕ (base case indℕ(p₀,pS,zeroℕ) ≐ p₀ and inductive step indℕ(p₀,pS,succℕ n) ≐ pS(n, indℕ(...,n))) `:120`
- Definition — addition addℕ : ℕ → (ℕ → ℕ) defined by induction on the second variable (defn:addN) `:162`
- Remark — 0+n and succℕ(m)+n are not judgmental equalities; identifying them requires the identity type `:227`
- Definition — pattern matching as a presentation of definitions by the induction principle of ℕ `:263`

#### `inductive.tex` — More inductive types

Introduces the unit, empty, coproduct, integer, dependent-pair (Sigma), and cartesian-product types as inductive types via their constructors, induction principles, and computation rules, alongside negation and the propositions-as-types reading.

*Subsections:* The idea of general inductive types (`:7`), The unit type (`:17`), The empty type (`:50`), Coproducts (`:122`), The type of integers (`:200`), Dependent pair types (`:262`)

Key items:
- Definition — the unit type (1) with its induction principle `:23`
- Definition — the empty type (0) with its induction principle `:55`
- Definition — negation of types and is-empty (A -> 0) `:70`
- Proposition — negation is contravariant: (P -> Q) -> (not Q -> not P) `:93`
- Definition — the coproduct A + B with inl/inr and its induction principle `:125`
- Remark — functorial action of coproducts f + g `:158`
- Definition — the integers Z := N + (1 + N) `:208`
- Remark — the induction principle for the integers Z `:231`
- Definition — the dependent pair type (Sigma-type) with pairing and its induction principle `:269`
- Definition — the projection maps pr1 and pr2 `:292`
- Definition — the cartesian product A x B as a Sigma-type `:333`

#### `identity.tex` — Identity types

Introduces the identity type as an inductive family generated by refl, its path-induction principle, the groupoidal structure of types (concatenation, inversion, associativity, unit and inverse laws), the action on paths of functions, transport and dependent action on paths, and the contractibility of the total space of the identity type — closing with the addition laws on the natural numbers as a worked application.

*Subsections:* The inductive definition of identity types (`:13`), The groupoidal structure of types (`:76`), The action on identifications of functions (`:214`), Transport (`:276`), The uniqueness of refl (`:317`), The laws of addition on ℕ (`:350`)

Key items:
- Definition — the identity type and its induction principle (path induction / identification elimination) `:15`
- Definition — concatenation of identifications (transitivity) `:80`
- Definition — inverse operation on identifications (symmetry) `:107`
- Definition — the associator for concatenation `:135`
- Definition — left and right unit laws for concatenation `:164`
- Definition — left and right inverse laws for identifications `:182`
- Definition — the action on paths of a function (ap), with ap-id and ap-comp `:222`
- Definition — transport along an identification (tr_B) `:282`
- Definition — the dependent action on paths (apd) `:301`
- Proposition — contractibility of the total space of the identity type (uniqueness of (a,refl)) `:327`

#### `universes.tex` — Universes

Introduces type-theoretic universes (a type U with a universal family closed under the type formers), the "enough universes" postulate and its tower/join constructions, then uses universe-valued families to define observational equality on the naturals and characterize the identity type of N, proving Peano's seventh and eighth axioms.

*Subsections:* Specification of type theoretic universes (`:13`), Assuming enough universes (`:85`), Observational equality of the natural numbers (`:168`), Peano's seventh and eighth axioms (`:255`)

Key items:
- Definition — universe (type U with universal family Ty, closed under the type formers) `:31`
- Definition — enough universes (postulate: every finite list of types is contained in some universe) `:99`
- Definition — successor universe U+ (and the tower U, U+, U++, ...) `:123`
- Definition — observational equality Eq-N on the natural numbers (universe-valued binary relation by double induction) `:180`
- Lemma — Eq-N is reflexive (refl-Eq-N) `:214`
- Proposition — (m = n) <-> Eq-N(m,n): observational equality characterizes the identity type of N `:229`
- Theorem — succ-N is injective / Peano axiom P7: (m=n) <-> (succ m = succ n) `:265`
- Theorem — Peano axiom P8: zero is not a successor (0 != succ n) `:289`

#### `modular-arithmetic.tex` — Modular arithmetic via the Curry-Howard interpretation

Develops the Curry-Howard interpretation of logic (∃/∀ as Σ/Π) by building divisibility, the congruence relations on ℕ, the standard finite types Fin k, the effective split-surjective quotient map ℕ → Fin(k+1), and the cyclic groups ℤ/k as abelian groups.

*Subsections:* The Curry-Howard interpretation (`:7`), The congruence relations on $\N$ (`:155`), The standard finite types (`:214`), The natural numbers modulo $k+1$ (`:300`), The cyclic groups (`:491`)

Key items:
- Definition — divisibility on ℕ (d ∣ n as a Σ-type) — the flagship Curry-Howard translation of ∃ `:19`
- Definition — typal binary relation; reflexive/symmetric/transitive; (typal) equivalence relation `:159`
- Definition — congruence modulo k (x ≡ y mod k := k ∣ dist(x,y)) `:181`
- Proposition — the congruence relation modulo k is an equivalence relation `:192`
- Definition — the standard finite types Fin k (recursive: Fin 0 := ∅, Fin(k+1) := Fin k + 1) `:230`
- Proposition — the inclusion natFin : Fin k → ℕ is injective `:287`
- Definition — split surjective (is-split-surjective f := Π(b:B) Σ(a:A) f(a)=b) — Curry-Howard surjectivity `:314`
- Definition — the quotient/reduction map [-]_{k+1} : ℕ → Fin(k+1) `:346`
- Theorem — effectiveness of the mod-(k+1) quotient map: [x]=[y] ↔ x ≡ y mod k+1 `:451`
- Theorem — the quotient map [-]_{k+1} : ℕ → Fin(k+1) is split surjective `:471`
- Definition — the cyclic groups ℤ/k (ℤ/0 := ℤ, ℤ/(k+1) := Fin(k+1)) `:494`
- Theorem — addition on ℤ/k satisfies the abelian group laws `:556`

#### `number-theory.tex` — Decidability in elementary number theory

Develops decidability in constructive number theory: decidable types and decidable equality, decidability of divisibility, the well-ordering principle of ℕ, the greatest common divisor defined by well-ordering, the infinitude of primes, and the Boolean reflection principle.

*Subsections:* Decidability and decidable equality (`:9`), Constructions by case analysis (`:126`), The well-ordering principle of ℕ (`:268`), The greatest common divisor (`:321`), The infinitude of primes (`:442`), Boolean reflection (`:542`)

Key items:
- Definition — decidable type (is-decidable A := A + ¬A) `:11`
- Definition — has-decidable-equality (decidable identity types) `:62`
- Lemma — decidability transports along a logical equivalence A ↔ B `:71`
- Theorem — divisibility d ∣ x is decidable on ℕ `:116`
- Corollary — bounded dependent product of decidable families is decidable `:254`
- Definition — lower bound and upper bound of a family over ℕ `:274`
- Theorem — well-ordering principle of ℕ (least witness of a decidable family) `:290`
- Definition — greatest common divisor (is-gcd characterization) `:333`
- Definition — gcd defined via the well-ordering principle `:401`
- Theorem — infinitude of primes (a prime exceeds every n) `:519`
- Theorem — Boolean reflection principle `:561`

### Part II — The Univalent Foundations of Mathematics (`chapter-univalent-foundations.tex`)

#### `equivalences.tex` — Equivalences

Introduces homotopies and the groupoid/whiskering structure on them, defines equivalence as a bi-invertible map (section + retraction) and relates it to having an inverse, and characterizes the identity types of Sigma-types via observational equality.

*Subsections:* Homotopies (`:12`), Bi-invertible maps (`:154`), Characterizing the identity types of $\Sigma$-types (`:313`)

Key items:
- Definition — homotopy (f ~ g) as a family of pointwise identifications `:36`
- Proposition — homotopies satisfy the groupoid laws (assoc, unit, inverse up to homotopy) `:99`
- Definition — whiskering operations on homotopies (h . H and H . f) `:139`
- Definition — sections, retractions, and is-equiv (equivalence as a bi-invertible map) `:158`
- Remark — has-inverse(f) (invertible map) versus is-equiv(f), and why they differ `:206`
- Proposition — is-equiv(f) implies has-inverse(f) (every equivalence can be given an inverse) `:225`
- Corollary — the inverse of an equivalence is again an equivalence `:248`
- Definition — Eq-Sigma: observational equality on Sigma-types `:348`
- Definition — pair-eq : (s = t) -> Eq-Sigma(s,t) `:374`
- Theorem — pair-eq is an equivalence (characterization of identity types of Sigma-types) `:382`

#### `contractible.tex` — Contractible types and contractible maps

Develops contractibility (is-contr) and singleton induction, then defines contractible maps (fibers), and proves the two-way equivalence between being an equivalence and being a contractible map via coherently invertible maps.

*Subsections:* Contractible types (`:20`), Singleton induction (`:58`), Contractible maps (`:131`), Equivalences are contractible maps (`:210`)

Key items:
- Definition — is-contr (contractible type: center + contraction) `:22`
- Theorem — total space of the identity type Σ(x:A) a=x is contractible `:42`
- Definition — singleton induction (ev-pt has a section) `:64`
- Theorem — A is contractible iff A is pointed and satisfies singleton induction `:89`
- Definition — fiber of a map fib(f,b) := Σ(a:A) f(a)=b `:134`
- Definition — contractible map is-contr(f) := all fibers contractible `:189`
- Theorem — any contractible map is an equivalence `:196`
- Definition — coherently invertible map (g,G,H,K with the extra coherence) `:226`
- Proposition — any coherently invertible map has contractible fibers `:239`
- Lemma — has-inverse(f) → is-coh-invertible(f) `:321`
- Theorem — any equivalence is a contractible map `:362`

#### `fundamental.tex` — The fundamental theorem of identity types

Develops the fundamental theorem of identity types — a type family with a point is an identity system iff its total space is contractible iff the canonical family of maps out of the identity type is a family of equivalences — and applies it to characterize identity types of ℕ, embeddings, disjointness of coproducts, and the structure identity principle.

*Subsections:* Families of equivalences (`:16`), The fundamental theorem (`:144`), Equality on the natural numbers (`:222`), Embeddings (`:289`), Disjointness of coproducts (`:336`), The structure identity principle (`:425`)

Key items:
- Definition — the total map tot(f) of a family of maps `:19`
- Lemma — fiber of tot(f) is the fiber of f(pr1 t) at pr2 t `:31`
- Theorem — f is a family of equivalences iff tot(f) is an equivalence `:61`
- Definition — (unary) identity system on A at a `:152`
- Theorem — the fundamental theorem of identity types (fam-of-equivs / contractible total space / identity system) `:181`
- Theorem — characterization of the identity type of the natural numbers (m=n) ≃ EqN(m,n) `:242`
- Definition — embedding: is-emb(f) via ap f being an equivalence `:293`
- Theorem — identity types of coproducts / disjointness of coproducts `:345`
- Theorem — the structure identity principle `:450`

#### `hierarchy.tex` — Propositions, sets, and the higher truncation levels

Builds the h-level (truncation) hierarchy from the bottom up: propositions and sets as the first two levels above contractibility, embeddings and subtypes as their map-level counterparts, Hedberg's theorem, and the general is-trunc hierarchy with its closure properties.

*Subsections:* Propositions (`:21`), Subtypes (`:96`), Sets (`:191`), General truncation levels (`:288`)

Key items:
- Definition — is-prop (proposition: a type with contractible identity types) `:24`
- Proposition — characterizations of is-prop (prop iff all-elements-equal, etc.) `:45`
- Proposition — map between propositions is an equivalence iff a map back exists (P≃Q ↔ P↔Q) `:80`
- Definition — subtype / property (a proposition-valued type family) `:111`
- Theorem — f is an embedding iff every fiber is a proposition `:151`
- Definition — is-set (set: a type with propositional identity types) `:194`
- Theorem — set criterion: a prop-valued reflexive relation implying identity makes A a set `:228`
- Theorem — Hedberg's theorem (decidable equality implies set) `:261`
- Definition — is-trunc: the h-level / truncation hierarchy defined by recursion on k `:312`
- Proposition — truncation levels are cumulative: a k-type is a (k+1)-type `:343`
- Theorem — f is (k+1)-truncated iff ap_f is k-truncated on all identity types `:386`

#### `funext.tex` — Function extensionality

Develops the function extensionality axiom and its equivalent forms (including weak funext), then applies it: closure of h-levels under Π, type-theoretic choice and identity systems on Π-types, the dependent universal properties of Σ- and identity types, precomposition by an equivalence, and strong induction on ℕ.

*Subsections:* Equivalent forms of function extensionality (`:28`), Identity systems on Π-types (`:153`), Universal properties (`:282`), Composing with equivalences (`:378`), The strong induction principle of ℕ (`:462`)

Key items:
- Proposition — the three equivalent forms of function extensionality at f (htpy-eq is an equivalence / total space of homotopies is contractible / homotopy induction), via the fundamental theorem `:32`
- Theorem — function extensionality ⟺ weak function extensionality (a Π of contractible types is contractible) `:63`
- Definition — the Function Extensionality axiom (htpy-eq : (f=g) → (f ~ g) is an equivalence; inverse eq-htpy) `:111`
- Theorem — a Π of a family of k-types is a k-type (h-levels close under Π) `:132`
- Theorem — type-theoretic choice: distributivity of Π over Σ is an equivalence `:157`
- Theorem — identity systems on Π-types (Eq-Pi from pointwise identity systems) `:262`
- Theorem — the dependent universal property of Σ-types (ev-pair is an equivalence) `:297`
- Theorem — the dependent universal property of identity types / type-theoretic Yoneda lemma (ev-refl is an equivalence) `:350`
- Theorem — f is an equivalence iff precomposition by f is an equivalence `:382`
- Theorem — strong induction principle for the natural numbers `:468`

#### `propositional-truncation.tex` — Propositional truncations

Specifies the propositional truncation of a type by its universal property (precomposition into propositions is an equivalence), constructs it as a higher inductive type with its induction principle, uses it to interpret disjunction and existential quantification, and (via Kraus's theorem) extends weakly constant maps into sets.

*Subsections:* The universal property of propositional truncations (`:14`), Propositional truncations as higher inductive types (`:103`), Logic in type theory (`:256`), Mapping propositional truncations into sets (`:342`)

Key items:
- Definition — is a propositional truncation (universal property: precomposition ∘f : (P→Q)→(A→Q) is an equivalence for every proposition Q) `:22`
- Proposition — propositional truncation is unique up to equivalence (3-for-2 property of propositional truncations) `:56`
- Lemma — ∥A∥ is a proposition `:146`
- Definition — induction principle of the propositional truncation ∥A∥ `:178`
- Theorem — η : A → ∥A∥ satisfies the universal property of the propositional truncation `:213`
- Definition — disjunction P ∨ Q := ∥P+Q∥ `:263`
- Definition — existential quantification ∃_{x:A} P(x) := ∥Σ_{x:A} P(x)∥ `:292`
- Definition — weakly constant map (is-weakly-constant(f) := Π_{x,y:A} f(x)=f(y)) `:390`
- Theorem — Kraus: a weakly constant map into a set B extends uniquely along η, i.e. (∥A∥→B) ≃ Σ_{f:A→B} Π_{x,y} f(x)=f(y) `:424`

#### `images.tex` — Image factorizations

Constructs the image of a map via propositional truncation as the least embedding through which the map factors — proving its universal property and uniqueness — then develops surjective maps, the unique surjection-then-embedding factorization, and Cantor's diagonal theorem.

*Subsections:* The image of a map (`:12`), Surjective maps (`:205`), Cantor's diagonal argument (`:351`)

Key items:
- Definition — morphism from f to g over X (hom-slice hom_X(f,g)) `:20`
- Definition — universal property of the image of a map `:38`
- Definition — the image im(f) := Σ(x:X) ‖fib_f(x)‖, with image inclusion i_f `:96`
- Theorem — the image inclusion i_f satisfies the universal property of the image `:132`
- Theorem — uniqueness of the image up to equivalence (two-of-three property) `:157`
- Definition — surjective map, is-surj(f) := Π(b:B) ‖fib_f(b)‖ `:209`
- Proposition — dependent universal property of surjective maps (surjectivity characterized by precomposition equivalence) `:226`
- Theorem — m satisfies the image universal property iff q is surjective `:284`
- Corollary — every map factors uniquely as a surjection followed by an embedding `:332`
- Definition — the U-power set P_U(X) := X → Prop_U `:356`
- Theorem — Cantor's theorem: no surjection X → P_U(X) `:363`

#### `finite-types.tex` — Finite types

Develops finite types in univalent mathematics: countings (Fin k ≃ A) and their closure properties, the double-counting theorem that Fin k ≃ Fin l forces k = l, and the propositionally-truncated notion of finiteness with a well-defined cardinality and its closure under coproducts, products, and Σ.

*Subsections:* Counting in type theory (`:3`), Double counting in type theory (`:129`), Finite types (`:240`)

Key items:
- Definition — cnt(A) — countings of a type (Σ(k:ℕ) Fin k ≃ A) `:7`
- Theorem — closure of countings under coproducts and Σ (thm:count) `:39`
- Corollary — countings and cartesian products (cor:count-prod) `:112`
- Proposition — Maybe is injective: (X+1 ≃ Y+1) → (X ≃ Y) (prp:is-injective-maybe) `:138`
- Theorem — double counting: (Fin k ≃ Fin l) → (k = l) (thm:is-injective-Fin) `:219`
- Definition — is-finite(X), the type 𝔽 of finite types, and BS_k (defn:finite) `:244`
- Theorem — is-finite' is a proposition and equals is-finite; cardinality |X| `:272`
- Corollary — 𝔽 ≃ Σ(k:ℕ) BS_k `:307`
- Proposition — principle of finite choice (prp:finite-choice) `:324`
- Theorem — closure of finite types under coproduct, product, and Σ `:346`

#### `univalence.tex` — The univalence axiom

Introduces the univalence axiom as the characterization of a universe's identity type, deriving its equivalent forms (equivalence induction), propositional extensionality, Voevodsky's theorem that univalence implies function extensionality, the object/subtype classifiers, and the failure of global choice.

*Subsections:* Equivalent forms of the univalence axiom (`:11`), Propositional extensionality (`:110`), Univalence implies function extensionality (`:177`), Maps and families of types (`:245`), Classical mathematics with the univalence axiom (`:345`), The binomial types (`:464`)

Key items:
- Theorem — univalence in three equivalent forms: equiv-eq is an equivalence / Sigma(B, A≃B) contractible / equivalence induction `:14`
- Axiom — the univalence axiom (all universes are univalent; eq-equiv is the inverse of equiv-eq) `:49`
- Theorem — propositional extensionality: iff-eq is an equivalence, so Prop_U is a set `:143`
- Lemma — post-composition by an equivalence is an equivalence (via equivalence induction) `:180`
- Theorem — univalence implies function extensionality (Voevodsky) `:198`
- Theorem — object classifier: Sigma(X:U, X→A) ≃ (A→U) via fibers `:249`
- Theorem — subuniverse classifier (families with fiberwise structure P classify maps into U_P) `:295`
- Corollary — subtypes of A are equivalently embeddings X↪A, i.e. Sigma(X, X↪A) ≃ (A→Prop_U) `:319`
- Corollary — no global choice function Prod(A:U, ‖A‖→A) — incompatible with univalence `:395`

#### `set-quotients.tex` — Set quotients

Constructs the quotient of a type by an equivalence relation as its type of equivalence classes, proves the universal property of set quotients and its equivalent characterizations (surjective + effective, image factorization), tames size via the replacement axiom, and applies the machinery to partitions, unique representatives (the rationals), and set truncation.

*Subsections:* Equivalence relations and the replacement axiom (`:14`), The universal property of set quotients (`:146`), Partitions (`:395`), Unique representatives of equivalence classes (`:486`), Set truncations (`:609`)

Key items:
- Definition — equivalence relation (prop-valued reflexive/symmetric/transitive R : A → A → Prop_U) `:16`
- Definition — equivalence class and the set quotient A/R as the type of equivalence classes ([x]_R = R(x), q_R) `:26`
- Proposition — characterization of the identity type of A/R: ([x]_R = P) ≃ P(x) `:48`
- Corollary — effectivity of the quotient map: ([x]_R = [y]_R) ≃ R(x,y) `:76`
- Definition — locally U-small type/map (identity types are U-small) `:97`
- Axiom — the replacement axiom (image of a U-small type into a locally U-small type is U-small) `:122`
- Definition — universal property of the set quotient (unique extension of R-invariant maps into sets) `:159`
- Theorem — three equivalent characterizations of a set quotient: universal property ⇔ surjective + effective ⇔ image factorization of R `:189`
- Theorem — Eq-Rel_U(A) ≃ Σ(X : Set_U) A ↠ X (equivalence relations ≃ surjections into sets) `:350`
- Theorem — unique representatives give the quotient: q : A → Σ(x:A) C(x) is a set quotient `:499`
- Definition — set truncation (f : A → B into a set B universal for maps into sets) `:622`
- Theorem — equivalent characterizations of set truncation: universal ⇔ dependent universal ⇔ surjective + effective for ‖x=y‖ `:632`

#### `groups.tex` — Groups in univalent mathematics

Builds the type of all groups (via semigroups and monoids), proves isomorphic groups are equal using the fundamental theorem of identity types and the structure identity principle, then defines homotopy groups via iterated loop spaces and proves them abelian for n≥2 by the Eckmann-Hilton argument.

*Subsections:* The type of all groups (`:12`), Group homomorphisms (`:107`), Isomorphic groups are equal (`:176`), Homotopy groups of types (`:267`), The Eckmann-Hilton argument (`:380`), Concrete versus abstract groups in univalent mathematics (`:523`)

Key items:
- Definition — semigroup (set + associative binary operation) `:22`
- Lemma — is-unital(G) is a proposition (being unital is a property, not structure) `:48`
- Definition — is-group / group (unital semigroup with inverses) `:59`
- Definition — group homomorphism (operation-preserving map) `:109`
- Definition — is-iso / isomorphism of (semi)groups `:146`
- Lemma — a homomorphism is an iso iff its underlying map is an equivalence (lem:grp_iso) `:178`
- Theorem — iso-eq is a family of equivalences for semigroups (via fundamental theorem + structure identity principle) `:202`
- Theorem — isomorphic groups are equal (iso-eq is an equivalence) `:244`
- Definition — loop space and iterated loop space Ω^n `:283`
- Definition — n-th homotopy group π_n and the fundamental group π_1 `:301`
- Theorem — Eckmann-Hilton: p∙q = q∙p for double loops `:477`
- Theorem — truncated generalization of the fundamental theorem of identity types (thm:truncated-fundamental) `:580`

#### `W-types.tex` — General inductive types

Develops general inductive types via W-types (well-founded trees): their construction, observational/identity characterization, truncation levels, functorial action, the elementhood and well-founded induction relation, extensionality, and the multiset model culminating in Russell's paradox that a univalent universe is not small.

*Subsections:* The type of well-founded trees (`:10`), Observational equality of W-types (`:164`), Functoriality of W-types (`:255`), The elementhood relation on W-types (`:320`), Extensional W-types (`:404`), Russell's paradox in type theory (`:488`)

Key items:
- Definition — W-type W(A,B) (well-founded trees) with constructor tree/collect `:12`
- Definition — observational equality relation EqW on W(A,B) `:197`
- Theorem — EqW characterizes the identity type of W(A,B) (canonical map is an equivalence) `:208`
- Theorem — if A is a (k+1)-type then so is W(A,B) (W-types preserve truncation level) `:240`
- Definition — functorial action W(f,e) of a map plus family of equivalences on W-types `:259`
- Theorem — if f is k-truncated then W(f,e) is; in particular equivalences and embeddings are preserved `:301`
- Definition — elementhood relation \in on W(A,B) `:330`
- Theorem — well-founded induction principle for the elementhood relation on W-types `:340`
- Definition — extensional W-type (canonical map to shared-elements equivalence) `:419`
- Theorem — characterization of extensionality for an inhabited W-type (equivalent conditions) `:429`
- Definition — type of multisets M_U := W(U, Ty) `:502`
- Theorem — Russell's paradox: a univalent universe U cannot be U-small `:693`

### Part III — The circle: synthetic homotopy theory (`chapter-circle.tex`)

#### `circle.tex` — The circle

Introduces the circle S¹ as a higher inductive type: its induction principle, the (dependent) universal property identifying maps out of S¹ with free loops, and the coherent H-space multiplicative structure on the circle.

*Subsections:* The induction principle of the circle (`:7`), The (dependent) universal property of the circle (`:83`), Multiplication on the circle (`:248`)

Key items:
- Definition — dependent action on generators dgen_{S¹} `:26`
- Definition — the circle S¹ (base, loop) and its induction principle `:40`
- Remark — identifications in Σ(u:P(base)) tr_P(loop,u)=u as commuting squares `:57`
- Theorem — the dependent universal property of the circle (dgen_{S¹} is an equivalence) `:102`
- Theorem — the universal property of the circle (maps S¹→X ≃ free loops Σ(x:X) x=x) `:181`
- Corollary — contractibility of maps S¹→X realizing a given loop `:228`
- Definition — H-space structure and coherent unit laws `:258`
- Theorem — the H-space (multiplicative) structure on the circle `:284`

#### `circle-universal-cover.tex` — The universal cover of the circle

Uses univalence to build the universal cover of the circle as a family of sets S¹→Set via descent data, proves the dependent universal property of the integers, shows the universal cover is an identity system (so the circle is a 1-type), and derives the group isomorphism π₁(S¹)≅ℤ.

*Subsections:* The universal cover of the circle (`:8`), Working with descent data (`:100`), The (dependent) universal property of the integers (`:238`), The fundamental group of the circle (`:371`)

Key items:
- Definition — descent data for the circle: the type family D(X,e) from (X, e:X≃X) `:18`
- Definition — the universal cover E := D(ℤ, succ) of the circle `:71`
- Lemma — segment of the helix: path lifting of loop in the total space `:84`
- Proposition — sections of A over S¹ are equivalently fixed points of e:X≃X `:145`
- Corollary — families of maps out of the universal cover as succ/e-equivariant maps ℤ→X `:209`
- Lemma — ℤ-induction (elim-ℤ) from a base point and an equivalence e_k:B(k)≃B(k+1) `:246`
- Proposition — dependent universal property of ℤ (uniqueness/contractibility) `:297`
- Corollary — universal property of ℤ used for the fundamental group (ev₀ an equivalence) `:359`
- Theorem — the universal cover of the circle is an identity system at base `:377`
- Corollary — the circle is a 1-type and not a 0-type `:397`
- Proposition — fundamental theorem of identity types augmented with a binary operation `:417`
- Theorem — the fundamental group of the circle: π₁(S¹)≅ℤ `:446`

## What the source establishes

A self-contained development of dependent type theory and univalent
foundations from first principles: the identity type and path
induction; equivalences and the fundamental theorem; the h-level
hierarchy; function extensionality, propositional truncation, and
the univalence axiom; and a first higher inductive type (the
circle) with the ℤ computation of its loop space. It fixes the
vocabulary and proof idioms kitcat's own developments use —
`is-contr`/`is-prop`/`is-set`, `is-equiv` via contractible fibers,
transport and `ap`, the fundamental theorem — so a kitcat
construction can cite the standard definition rather than restate
it. Everything recorded here is the source's own content, stated in
its own terms; a kitcat result is machine-checked only when its
module or `Gloss.*` certificate says so.
