# Partial Algebraic Structures in Univalent Category Theory

## A Homotopy-Theoretic Interpretation of the Magmoid–Groupoid Hierarchy

---

## 1. Introduction

This report develops a homotopy type theory (HoTT) interpretation of the hierarchy of algebraic structures with partial binary operations studied by Jonsson in _On Group-Like Magmoids_. Jonsson's hierarchy

> magmoid → semigroupoid → prepoloid → poloid → pregroupoid → groupoid

classifies structures by progressively stronger conditions on a partial binary operation: associativity, existence of local units, uniqueness of local units, existence and uniqueness of inverses. In the classical (set-level) setting, a poloid is precisely a small category in the sense of Ehresmann (1957), and a groupoid is a groupoid in the usual sense.

We pursue two goals. First, we translate the hierarchy into the language of univalent category theory, identifying the homotopy-theoretic content of each level. The central observation is that the hierarchy tracks the **progressive contractibility of the source and target witness types**, which we identify with conditions on the h-level of a natural mapping space. Second, we connect this analysis to the framework of **wild categories with families** (wild cwfs) as developed in the study of 2-coherent internal models of homotopical type theory, and use this connection to identify where braided (as opposed to symmetric) exchange structure can arise.

The mathematical content draws on the following principal sources:

- Jonsson, _On Group-Like Magmoids_ (the algebraic hierarchy).
- Ahrens, Kapulkin, and Shulman, _Univalent categories and the Rezk completion_, [arXiv:1303.0584](https://arxiv.org/abs/1303.0584) (univalent category theory).
- The theory of 2-coherent internal models of homotopical type theory, developing wild categories with families after Dybjer's _Internal type theory_ and Kraus's subsequent work on internal models (wild cwfs, 2-coherence).
- Hasegawa, _A quantum double construction in Rel_, [arXiv:0711.4042](https://arxiv.org/abs/0711.4042), and related work on braided lambda calculus (braided structural rules).
- The HoTT Book (Univalent Foundations Program, 2013) for foundational definitions and results.

Throughout, we work in the setting of homotopical Martin-Löf type theory (MLTT) with function extensionality and a univalent universe 𝒰.

---

## 2. Preliminaries

### 2.1. Homotopy levels

We recall the stratification of types by homotopy level (h-level), following the HoTT Book, Chapter 7.

A type A is **contractible** (h-level −2) if isContr(A) :≡ Σ(c : A) × Π(x : A), c = x.

A type A is a **mere proposition** (h-level −1) if isProp(A) :≡ Π(x y : A), x = y.

A type A is a **set** (h-level 0) if isSet(A) :≡ Π(x y : A), isProp(x = y).

A type A is an **n-type** (h-level n) if its identity types are all (n−1)-types. We write n-type for the universe of n-types.

For types A and B, the **mapping space** or **function type** A → B inherits the h-level of B: if B is an n-type, then A → B is an n-type for any A. This fact is central to the analysis that follows.

### 2.2. Wild categories

We use the notion of _wild category_ as a controlled relaxation of precategory, following the framework of 2-coherent internal models.

A **wild category** 𝒞 consists of:

- A type Ob 𝒞 of objects.
- For all x, y : Ob 𝒞, a _type_ Hom(x, y) of morphisms (not required to be a set).
- A composition operation g ∘ f for compatible morphisms, together with an **associator** α(f,g,h) : (h ∘ g) ∘ f = h ∘ (g ∘ f).
- Identity morphisms id_x for all objects x, together with **unitors** λ_f : id ∘ f = f and ρ_f : f ∘ id = f.

No further coherence conditions are required in the base definition. A wild category is **2-coherent** if it additionally has **triangle coherators** (filling the unitor-associator triangle) and **(associator-)pentagonators** (filling Mac Lane's pentagon). These are the two conditions familiar from bicategory theory.

The key distinction from a precategory (in the sense of Ahrens–Kapulkin–Shulman) is that hom-types are not required to be sets. Equalities between morphisms serve as **2-cells**, and higher equalities as higher cells. These cells are not axiomatized but arise from the ambient homotopical type theory. In particular, the interchange law

> (g ▷ γ) · (δ ◁ f') = (δ ◁ f) · (g' ▷ γ)

holds in all wild categories, as a consequence of the functoriality of ap.

A wild category has two distinguishable directions: the **categorical direction** (the 1-cells, i.e. morphisms) and the **typal direction** (the higher cells, arising from identity types). This distinction, made explicit in the study of Segal spaces by Rezk and by Joyal–Tierney, is central to the analysis that follows.

### 2.3. Univalence for wild categories

A morphism f : Hom(x, y) in a wild category is a **wild equivalence** if it is biinvertible (has both a section and a retraction). The type of wild equivalences is denoted x ≃_𝒞 y.

For objects x, y : Ob 𝒞, there is a canonical map

> idtowildequiv : (x =_{Ob 𝒞} y) → (x ≃_𝒞 y)

constructed by transporting id_x along an equality.

A wild category is **univalent** if idtowildequiv is an equivalence for all x, y. This subsumes both 1-categorical univalence (when hom-types are sets) and the univalence axiom (when 𝒞 is a universe 𝒰).

---

## 3. The Jonsson Hierarchy: Arrow Reformulation

We first summarize the translation of Jonsson's hierarchy from "internal-hom" presentation (a single carrier set P with a partial binary operation) to "arrow" presentation (objects, morphisms, source and target maps), before giving the homotopy-theoretic interpretation.

### 3.1. Magmoids and directed graphs

A **magmoid** is a set P equipped with a partial binary operation (x, y) ↦ xy, written xy↓ when defined. In arrow presentation, this corresponds to a directed graph with a partial composition: a type Mor of morphisms with a partial operation ∘, but no specified objects, no source/target maps, and no axioms.

At this level, there is no intrinsic notion of "source" or "target" for a morphism. The composability relation xy↓ is the only structure.

### 3.2. Semigroupoids and semicategories

A **semigroupoid** is a magmoid satisfying associativity: whenever both sides are defined,

> (xy)z = x(yz).

In arrow presentation, this is a **semicategory**: objects are latent, witnessed by composability, but there are no identity morphisms. Associativity provides coherence for iterated composition but does not determine source and target.

### 3.3. Prepoloids and protocategories

A **prepoloid** is a semigroupoid in which every element x has a **local left unit** λ_x (satisfying λ_x · x = x) and a **local right unit** ρ_x (satisfying x · ρ_x = x).

In arrow presentation, a prepoloid is a semicategory equipped with a type of _proto-identity_ witnesses for each morphism. For a morphism f, define the type of **left unit witnesses**:

> LUnit(f) :≡ Σ(λ : Mor) × (λ ∘ f = f).

In a prepoloid, LUnit(f) is merely inhabited for all f. However, it may have multiple inhabitants. Jonsson exhibits (Example 7.2) a two-element semigroup where both elements serve as local left units for one of them.

We refer to a prepoloid as a **protocategory**: a semicategory with (possibly non-unique) local identities.

### 3.4. Poloids and small categories

A **poloid** is a prepoloid in which the local units satisfy a matching condition: xy↓ if and only if ρ_x = λ_y, and the effective units are two-sided and unique.

**Proposition** (Jonsson, Prop. 6.2–6.4). In a prepoloid with unique local units:

1. Each proto-identity e satisfies λ_e = e = ρ_e (proto-identities are idempotent).
2. λ_{f ∘ g} = λ_f and ρ_{f ∘ g} = ρ_g (source/target respect composition).
3. f ∘ g is defined if and only if ρ_f = λ_g (the matching condition).

**Theorem** (Jonsson, Theorem 8.1; cf. Ehresmann 1957). Every prepoloid with unique local units admits a **restricted multiplication** P[𝔪] under which it becomes a poloid. A poloid is precisely a small category.

In the arrow reformulation: the passage from prepoloid to poloid is the passage from "source and target witnesses exist" to "source and target witnesses are unique," allowing the definition of source and target as functions s, t : Mor → Ob with the matching condition t(f) = s(g) for composability.

### 3.5. Pregroupoids and von Neumann regularity

A **pregroupoid** is a prepoloid in which every element x has a **preinverse** x̄ satisfying

> x x̄ x = x  and  x̄ x x̄ = x̄.

This is von Neumann regularity. In arrow presentation, the type of **inverse witnesses** for a morphism f is

> Inv(f) :≡ Σ(f̄ : Mor) × (f ∘ f̄ ∘ f = f) × (f̄ ∘ f ∘ f̄ = f̄).

A pregroupoid has Inv(f) merely inhabited for all f.

**Proposition** (Jonsson, Prop. 7.5). In a pregroupoid, preinverses are unique if and only if idempotents commute.

### 3.6. Groupoids

A **groupoid** in Jonsson's sense is a pregroupoid in which every preinverse is a **strong preinverse**: f ∘ f̄ and f̄ ∘ f are two-sided units (i.e., identity morphisms).

**Theorem** (Ehresmann–Schein–Nambooripad). Every pregroupoid with unique preinverses admits a restricted multiplication under which it becomes a groupoid. This is the classical ESN theorem, establishing a correspondence between inverse semigroups and groupoids.

### 3.7. Rosetta Stone

| Jonsson (internal-hom) | Arrow presentation                          | Status of source/target             |
| ---------------------- | ------------------------------------------- | ----------------------------------- |
| Magmoid                | Directed graph + partial composition        | Nonexistent                         |
| Semigroupoid           | Semicategory                                | Latent (witnessed by composability) |
| Prepoloid              | Protocategory (local units)                 | Ambiguous (non-unique witnesses)    |
| Poloid                 | Small category                              | Fully determined                    |
| Pregroupoid            | Regular semicategory (von Neumann inverses) | Determined by idempotents           |
| Groupoid               | Small groupoid                              | Determined by inverses              |

---

## 4. The Mapping Space Interpretation

### 4.1. Source and target as projection maps

In the standard formulation of a (pre)category, a morphism f : Hom(A, B) has source A and target B by construction — the typing is the sourcing. We now consider what happens when this identification is weakened.

Given a wild category with hom-types Hom(x, y), a **source projection** for the hom type at objects x, y is a map

> s : Hom(x, y) → Ob.

Similarly for a target projection t. The **mapping space** of all such projections is the function type

> Hom(x, y) → Ob.

The h-level of this mapping space is determined by the interaction of two factors:

**From the codomain.** If Ob is an n-type, then Hom(x, y) → Ob is an n-type for any domain. This gives an upper bound: the mapping space is at most as complex as the object type.

**From the domain.** The homotopy type of Hom(x, y) determines how much room there is for maps to vary. A contractible hom type admits essentially one map into any target (up to homotopy). A hom type with non-trivial loops admits maps that can "probe" the identity structure of Ob, producing genuine variability in the mapping space.

The two contributions interact: the mapping space can only be as complex as the lesser of what the domain can probe and what the codomain can support.

### 4.2. The h-level stratification of the hierarchy

We now reinterpret Jonsson's hierarchy as conditions on the mapping space (Hom(x,y) → Ob), or more precisely, on the connected components of this space containing the source and target projections.

**Poloid (= precategory).** The source projection s and the target projection t each inhabit a **contractible** connected component of the mapping space. That is: not only are s and t well-defined maps, but the space of maps homotopic to s (respectively t) is contractible. Source and target are determined up to a unique identification.

**Prepoloid.** The connected component of each projection is **inhabited but not contractible**. There exist maps homotopic to s, and the space of homotopies carries non-trivial structure. Different ways of assigning sources to the morphisms in Hom(x, y) are related by identifications that are themselves data.

**Semigroupoid.** No projection maps are assumed. The mapping space is unconstrained.

**Magmoid.** No composition axioms and no projection structure. The mapping space is irrelevant because there is no composition to decompose.

This reformulation makes precise how the hierarchy tracks the **crystallization of the object set**: from nonexistent (magmoid) through latent (semigroupoid) and ambiguous (prepoloid) to fully determined (poloid).

### 4.3. Function extensionality and coherent source identification

By function extensionality, the identity type between two projection maps s, s' : Hom(x, y) → Ob is

> (s = s') ≃ Π(f : Hom(x,y)), s(f) = s'(f).

A path between projections is therefore a **coherent family** of identifications of source assignments, compatible across the entire hom type. This coherence is guaranteed by function extensionality and does not need to be imposed as an additional axiom.

Furthermore, the hom type's own isomorphism structure contributes through the following mechanism. An automorphism φ : Hom(x, y) ≃ Hom(x, y) acts on projection maps by precomposition: s ↦ s ∘ φ. A non-trivial automorphism (one not equal to the identity) can thereby generate a non-trivial loop in the mapping space:

> s ∘ φ ≠ s  but  s ∘ φ ∼ s (related by a path).

Thus **symmetries of the hom type generate variability in source/target assignments**. The h-level of Aut(Hom(x,y)) bounds the complexity of the loops in the mapping space.

The automorphism group Aut(y) of the mediating object y in a composition f ∘ g acts by transport on Hom(y, z). This action is defined via composition with elements of Aut(y), and its coherence is entirely determined by the h-level of the hom types. There is no independent "isomorphism axis" — the richness of the automorphism action is a consequence of, not independent from, the h-level of the hom types.

---

## 5. The Wild CwF Connection

### 5.1. Wild categories with families

We now connect the preceding analysis to the framework of **wild categories with families** (wild cwfs), which provide internal models of homotopical dependent type theory.

A **typed term structure** on a wild category 𝒞 (valued in a universe 𝒰) consists of:

- A presheaf Ty : Ob 𝒞 → 𝒰 of **types**, with a substitution action A[σ] : Ty(Γ) for A : Ty(Δ) and σ : Sub(Γ, Δ), satisfying A[id] = A and A[τ ∘ σ] = A[τ][σ].
- A presheaf Tm : (Γ : Ob 𝒞) → Ty(Γ) → 𝒰 of **terms**, with a substitution action a[σ] satisfying analogous functoriality conditions.

A **context extension structure** on a typed term structure (Ty, Tm) provides:

- For each context Γ and type A : Ty(Γ), an extended context Γ.A with a **display map** p_A : Sub(Γ.A, Γ) and a **generic term** v_A : Tm(A[p_A]).
- An **extension operation** (σ ▷ a) : Sub(Γ, Δ.A) for σ : Sub(Γ, Δ) and a : Tm(A[σ]).
- **β-rules:** p_A ∘ (σ ▷ a) = σ and v_A[(σ ▷ a)] = a (up to transport).
- **η-rule:** p_A ▷ v_A = id_{Γ.A}.
- **Composition rule:** (τ ▷ a) ∘ σ = (τ ∘ σ) ▷ (a[σ]) (up to transport).

A **wild cwf** is a wild category 𝒞 equipped with a terminal object and a typed term structure with context extension.

### 5.2. The fundamental structural lemma

The key structural result, holding for _all_ wild cwfs (even non-coherent ones), is:

**Lemma** (Substitutions into extended contexts are pairs). For all contexts Γ, Δ and types A : Ty(Δ), there is an equivalence of types

> Sub(Γ, Δ.A) ≃ Σ(σ : Sub(Γ, Δ)) × Tm(A[σ]).

The forward map sends σ to (p_A ∘ σ, v_A[σ]) (up to transport), and the reverse map sends (σ, a) to σ ▷ a.

This equivalence is precisely the **source/fiber decomposition** of the hom type that we identified in §4. A substitution into an extended context factors as a base substitution (the "source projection") together with a term (the "fiber data"). The display map p_A _is_ the source projection.

### 5.3. The display map as source projection

The display map p_A : Γ.A → Γ is the canonical "source projection" in the cwf setting. The structural lemma says that this projection has the right universal property: precomposition with p_A is (half of) an equivalence.

The h-level of the fiber Tm(A[σ]) over a base substitution σ directly controls how uniquely the factoring is determined:

- If Tm(A[σ]) is contractible for all σ, the display map is an equivalence and the extension is trivial.
- If Tm(A[σ]) is a mere proposition, the factoring is unique when it exists.
- If Tm(A[σ]) is a set, there can be multiple factorings, but the identity type between factorings is propositional.
- If Tm(A[σ]) is a 1-type, factorings can differ in ways that themselves carry data.

This maps directly onto the Jonsson conditions.

### 5.4. The two-axis picture

The wild cwf framework makes explicit that there are two independent axes of variation:

**Categorical axis (Jonsson's hierarchy).** How well-determined are source and target? This is governed by the algebraic conditions — associativity, existence and uniqueness of local units, invertibility. The progression is: no composition axioms (magmoid) → associativity (semigroupoid) → local units (prepoloid) → unique local units + matching (poloid) → inverses (groupoid).

**Typal axis (h-level of hom types).** How much higher structure do the hom types carry? This is governed by the truncation level. The cases are:

- Hom-types are **sets**: precategory (in the AKS sense). All 2-cell data is propositional.
- Hom-types are **1-types**: the regime of "2-cwfs," conjecturally including the container higher model of type theory (Altenkirch–Kaposi).
- Hom-types are **unconstrained types**: full wild category. The universe cwf 𝒰 lives here.

In a **1-cwf**, both axes are maximally constrained: the categorical structure is a category (poloid), and the hom-types are sets. In the **universe cwf** 𝒰, the categorical structure is still strictly associative and unital (composition of functions satisfies the laws definitionally), but the hom-types are unconstrained (function types A → B are general types).

### 5.5. Coherence conditions: type triangulators and pentagonators

When the underlying wild category is 2-coherent, further coherence can be demanded of the type presheaf, improving it to what might be called a **wild weak (2,1)-presheaf**.

A typed term structure has **type triangulators** if for all morphisms σ and types A, the triangles

> A[id ∘ σ] →[comp] A[id][σ] →[substid] A[σ]

and

> A[id ∘ σ] →[ap(λ)] A[σ]

commute, and similarly for the right unitor. It has **type pentagonators** if the evident pentagon for triple substitution composition commutes.

These conditions are analogous to the conditions for a pseudofunctor between weak (2,1)-categories. In the Jonsson hierarchy, they correspond to the conditions under which the source/target assignments (embodied by the type presheaf) respect the associativity and unit structure of the underlying wild category.

---

## 6. Composition, Transport, and the Source of Braiding

### 6.1. On-the-nose vs. transported composition

In a wild cwf (or, more generally, in any wild-categorical setting with hom-type formers), composition of morphisms f : Hom(x, y) and g : Hom(y, z) is well-typed by construction: the mediating object y is literally the same in both types. We call this **on-the-nose composition**.

The more general situation is when we have f : Hom(w, x) and g : Hom(y, z) with a separate identification e : x ≅ y (an isomorphism in the wild category) or, in the univalent case, a path e : x = y. The composite is then formed as

> f ; tr(g, e)

where tr(g, e) : Hom(x, z) denotes the transport of g along e, recasting g as having source x.

In the on-the-nose case, the isomorphism e is morally refl (or the identity isomorphism), and tr(g, e) ≡ g. The composite is just f ; g and is determined.

In the transported case, e is genuine data, and a different choice of isomorphism e' : x ≅ y yields a different transported morphism tr(g, e') and hence a potentially different composite f ; tr(g, e').

### 6.2. The automorphism action

Given two isomorphisms e, e' : x ≅ y, the composite e⁻¹ ∘ e' : Aut(y) is an automorphism of y. This automorphism acts on g : Hom(y, z) by transport, relating tr(g, e) to tr(g, e') in Hom(x, z). The relation propagates through composition.

Thus the structure governing how different composites of the same morphisms (via different identifications of the mediating object) relate to each other is

> Aut(y) acting on Hom(y, z) by transport.

This is the mapping space story of §4, now with the mechanism made explicit. The variability in the source projection Hom(x, z) → Ob — which assigns "the mediating object" to a composite — is parameterized by the automorphism group of that mediating object.

### 6.3. Exchange and the two-transport problem

Consider a context extended by two types: Γ.A.B. There are two display maps:

> p_B : Γ.A.B → Γ.A    and    p_A ∘ p_B : Γ.A.B → Γ.

The **exchange operation** — reordering to Γ.B'.A' (for appropriate B', A') — requires composing transports along two isomorphisms, one for each type in the context. The two transports can be performed in either order: transport A first then B, or B first then A.

Each order yields a composite that is well-characterized by its own universal property. The relationship between the two orders is witnessed by a 2-cell: the **exchange witness**. The character of this witness — whether it is symmetric (self-inverse) or merely braided (invertible but not self-inverse) — depends on the hom-type structure.

In a standard wild category, the 2-cells are identity types, and the interchange law is symmetric (by the Eckmann–Hilton argument applied to the path algebra). To obtain braided (non-symmetric) interchange, one must consider 2-cell structures that do not arise from identity types.

---

## 7. Abstract 2-Cells and Universal Properties

### 7.1. The general setup

To study the braiding question precisely without presupposing a particular interchange law, we consider the following framework.

We postulate, in addition to the wild-categorical data of §2.2, a type

> Cell₂(f, g)

for all parallel morphisms f, g : Hom(x, y), together with operations of horizontal composition (whiskering) and vertical composition, but **without axiomatizing the interchange law**. Instead, we specify universal properties of composites as witnessed by inhabitants of Cell₂.

### 7.2. The universal property of composites

For composable f : Hom(x, y) and g : Hom(y, z), the **universal property of the composite** f ; g is the following contractibility condition:

> isContr(Σ(s : Hom(x, z)) × Cell₂(f ; g, s))

with center of contraction at the pair (f ; g, r), where r : Cell₂(f ; g, f ; g).

This condition does three things simultaneously:

1. **It characterizes the composite.** Any s equipped with a 2-cell f ; g ⇒ s is connected to the center by a path in the total space.

2. **It provides a reflexivity-like 2-cell.** The second component r of the center plays the role of an identity 2-cell, but is derived from the universal property rather than axiomatized.

3. **It constrains Cell₂ relative to the identity type.** By the fundamental characterization of identity types (encode-decode), the contractibility of Σ(s) × Cell₂(f ; g, s) with center (f ; g, r) yields an equivalence

> Cell₂(f ; g, s) ≃ (f ; g = s)

for each s — but only **fiberwise at composites**.

### 7.3. The scope of the universal property

The equivalence Cell₂(f ; g, s) ≃ (f ; g = s) holds for each composite f ; g. But the 2-cell type is defined for all pairs of parallel morphisms, not only those where the source is presented as a composite. For a morphism h : Hom(x, z) that is not presented as a composite, the total space Σ(s) × Cell₂(h, s) is not assumed contractible.

This means: when a morphism h admits two different presentations as a composite — h = f ; g and h = f' ; g' — each presentation induces its own contractibility, but the **transition** between the two presentations passes through the 2-cell structure at h itself, where the structure is unconstrained by the axiom.

The transition map between the two presentations is where the interchange law is determined. If the transition is forced to be trivial (all 2-cells are identity types), interchange is symmetric. If the transition can carry non-trivial structure, interchange can be braided.

This is the precise locus of the distinction between the paper's wild cwf framework (where 2-cells are identity types and interchange is symmetric) and a potential "braided wild cwf" (where 2-cells are abstract and interchange is derived from universal properties).

### 7.4. Composition across an isomorphism

The universal property applies to on-the-nose composites f ; g, where f : Hom(x, y) and g : Hom(y, z) share the same mediating object y. For composites formed by transport — f ; tr(g, e) for an isomorphism e : x ≅ y — the universal property governs each transported composite separately.

Different choices of isomorphism e, e' : x ≅ y yield different composites f ; tr(g, e) and f ; tr(g, e'), each individually characterized by a contractible 2-cell slice. The relationship between the two is determined by the automorphism e⁻¹ ∘ e' : Aut(y) acting on the hom type.

In the setting of §7.1–7.3, this action is mediated by the (non-axiomatized) 2-cell structure, and the coherence of the action across different automorphisms is whatever the universal properties force. The braiding question reduces to: does the Aut(y)-action on the 2-cell slices satisfy a symmetric or braided interchange law?

---

## 8. The Quasigroupoid Direction

### 8.1. Quasigroups and their partialization

The structures discussed in §§3–5 lie on the hierarchy

> magma →[+assoc] semigroup →[+id] monoid →[+inv] group

under partialization. There is a parallel branch of universal algebra:

> magma →[+div] quasigroup →[+id] loop →[+assoc] group.

A **quasigroup** is a set Q with a binary operation such that for all a, b ∈ Q, the equations a · x = b and y · a = b each have unique solutions. Equivalently, the left and right multiplication maps L_a, R_a are bijections. Groups sit at the intersection of the two branches.

Jonsson's paper develops the first branch under partialization. We now consider what the second branch yields.

### 8.2. Decomposition of divisibility under partialization

In a total magma, the division condition combines cancellation (injectivity of L_a) and solvability (surjectivity of L_a). Under partialization, these separate:

**Cancellation conditions.**

- **(C1)** If ax↓ and ax'↓ and ax = ax', then x = x'.
- **(C2)** If ya↓ and y'a↓ and ya = y'a, then y = y'.

**Solvability conditions** (which further split depending on the domain of definition):

- **(D1-total)** L_a is total and surjective.
- **(D1-local)** L_a is surjective onto its effective codomain.
- **(D1-fiber)** L_a restricted to its effective domain surjects onto its effective codomain.

### 8.3. The Mal'cev operation and the many-object problem

In a quasigroup, the natural ternary operation is the **Mal'cev operation**

> m(x, y, z) = (x / y) · z

where x / y is the unique solution to t · y = x. In a group, this gives the heap operation m(x, y, z) = xy⁻¹z. In a non-associative quasigroup, m satisfies only the **Mal'cev identities**:

> m(x, x, y) = y    and    m(x, y, y) = x.

For the many-object generalization: in a groupoid, source and target emerge from **units** (identity morphisms), and their uniqueness relies on **associativity**. A quasigroup has neither units nor associativity, so neither mechanism is available.

Instead, in a many-object quasigroupoid, source and target are determined by the **division structure**. For fixed f : Hom(A, B), left division by f gives a partial equivalence

> L_f⁻¹ : Hom(A, C) ≃ Hom(B, C)

for each C. The hom types are related not by composition with identity morphisms (as in a category) but by division maps. The "source" of f is not picked out by a unit, but by the pattern of which hom types L_f⁻¹ connects.

### 8.4. The associativity obstruction as a cocycle

In a groupoid, the division maps satisfy the coherence L_f⁻¹ ∘ L_g⁻¹ = L_{g·f}⁻¹ (by associativity). In a quasigroupoid, this coherence fails. The discrepancy

> α(f,g) :≡ L_f⁻¹ ∘ L_g⁻¹ ∘ (L_{g·f}⁻¹)⁻¹ : Hom(B, D) ≃ Hom(B, D)

is an automorphism of a hom type, measuring the failure of associativity. As f and g vary, these discrepancies form a **cocycle**: they satisfy a coherence condition coming from the next level of iterated division.

The nature of this cocycle — symmetric, braided, or fully non-abelian — depends on the h-level of the hom types:

- **h-level 0** (hom types are sets): Aut(Hom(B,D)) is a group and α is a group cocycle. Exchange is a group action (discrete permutation).
- **h-level 1** (hom types are 1-types): Aut(Hom(B,D)) is a 2-group and the cocycle can carry braiding data. Exchange is potentially braided.
- **h-level 2 and beyond:** Higher coherence data accumulates.

### 8.5. The hierarchy for partial quasigroup-like structures

Combining the Jonsson-style categorical axis with the typal axis and the division structure, we obtain the following landscape:

| Structure     | Assoc. | Division     | h-level of hom | Obstruction               |
| ------------- | ------ | ------------ | -------------- | ------------------------- |
| Magmoid       | none   | none         | any            | —                         |
| Quasigroupoid | none   | full         | 0              | group cocycle             |
| Quasigroupoid | none   | full         | 1              | _braided cocycle_         |
| Loop-oid      | none   | full + id    | 0              | pointed group cocycle     |
| Pregroupoid   | full   | preinverse   | 0              | trivial (assoc. kills it) |
| Groupoid      | full   | full inverse | 0              | trivial                   |

The braided sequent calculus, if it exists, lives in the row where division is full (so the proof theory supports a form of cut elimination), associativity is absent (so cut elimination is not coherently associative), and hom types are 1-types (so the failure of associativity carries braiding data).

---

## 9. Synthesis: the Prepoloid–Poloid Gap as Truncation of Braiding Data

### 9.1. The restricted multiplication as truncation

Jonsson's restricted multiplication P[𝔪] — the passage from prepoloid to poloid — has a clean homotopy-theoretic reading: it is the **truncation of the mapping space** (Hom(x,y) → Ob).

The mapping space has connected components containing the source and target projections. Imposing the matching condition t(f) = s(g) for composability forces these components to be contractible: there is a unique (up to contractible choice) way to assign source and target. This is ‖−‖₀-truncation of the relevant components.

Truncation destroys information. What is lost is precisely the **automorphism action on projections** — the loops in the mapping space that, at h-level 1, carry braiding data. A poloid/category is what you get when you decide not to track how source/target assignments can be continuously deformed into each other. A prepoloid is what you have before making that decision.

### 9.2. The ESN theorem as fibration

The Ehresmann–Schein–Nambooripad theorem, in our reformulation, says: an inverse semigroup (= a one-object pregroupoid with unique preinverses) gives rise to a groupoid by **factoring** the single hom type through the object type of idempotents.

At set level, this is a reorganization of data. At higher h-level, the factoring question becomes genuinely topological: can you decompose a type H (the total hom space) as a fibration over B × B (pairs of objects) such that the fibers are the hom types?

The obstruction to clean factoring is the non-triviality of the mapping space (H → B) — i.e., the braiding data. A higher ESN theorem would establish a correspondence between "h-level 1 inverse-semigroup-like structures" and an appropriate notion of braided groupoid, where the restricted multiplication corresponds to truncation of the braiding.

### 9.3. Braided wild cwfs: a prospectus

Combining the analysis of §§6–8, we can outline the structure of a conjectural "braided wild cwf":

1. **The wild category of contexts is replaced by a "braided wild 2-category"**: a structure where 2-cells between substitutions are provided by an abstract Cell₂ type with braided (not symmetric) interchange.

2. **The typed term structure carries braided coherence.** The substitution coherences A[τ ∘ σ] = A[τ][σ] are witnessed by braided 2-cells rather than paths.

3. **The context extension β/η rules hold up to braided equivalence.** The decomposition Sub(Γ, Δ.A) ≃ Σ(σ) × Tm(A[σ]) is witnessed by braided 2-cells, and different decompositions of the same substitution are related by braids.

4. **The fibrational structure is "braided cloven" rather than cloven.** Lifts of substitutions along display maps are determined up to braiding rather than up to path.

The derivation of interchange from universal properties (§7) ensures that the braiding arises from the structure rather than being imposed by fiat. The h-level of the hom types and the type presheaf determine whether the derived interchange is symmetric (recovering the framework of 2-coherent wild cwfs) or braided (giving something genuinely new).

---

## 10. Open Questions

1. **Existence of braided wild cwfs.** Is there a non-trivial model of the axioms outlined in §9.3? The symmetric inverse monoid ℐ_n is a natural candidate: one could investigate whether, when the hom type is "thickened" to a 1-type (e.g., by taking the fundamental groupoid of a natural topology on partial bijections), the resulting structure has braided interchange.

2. **Higher ESN theorem.** Can the classical ESN correspondence be lifted to h-level 1, establishing an equivalence between "braided inverse-semigroup-like structures" and "braided groupoids" (in an appropriate sense)?

3. **Necessity of braiding at h-level 1.** Is the braided interchange law _forced_ by the universal properties at h-level 1 (analogous to how Eckmann–Hilton forces commutativity), or is it merely one option among several? The Mal'cev identities m(x,x,y) = y, m(x,y,y) = x may impose enough constraint on the obstruction cocycle to force braiding.

4. **Synthetic vs. analytic braiding.** Can braided interchange arise _within_ homotopical MLTT (i.e., synthetically, from type-forming operations), or does it necessarily require going outside the typal direction (to an externally provided Cell₂ type)? The observation that identity types always give symmetric interchange via Eckmann–Hilton suggests the latter, but novel type formers (such as those in a braided dependent sequent calculus) might circumvent this.

5. **Connection to directed type theory.** The frameworks of Riehl–Shulman (synthetic (∞,1)-categories) and Buchholtz–Weinberger provide non-invertible directed 2-cells. Braided-not-symmetric is a different relaxation from non-invertible. Can the two be combined?

---

## References

- Ahrens, B., Kapulkin, K., and Shulman, M. _Univalent categories and the Rezk completion._ Mathematical Structures in Computer Science, 25(5), 2015. [arXiv:1303.0584](https://arxiv.org/abs/1303.0584).

- Ahrens, B., et al. _Bicategories in univalent foundations._ Mathematical Structures in Computer Science, 31(10), 2021.

- Altenkirch, T. and Kaposi, A. _Type theory in type theory using quotient inductive types._ POPL 2016.

- Altenkirch, T. and Kaposi, A. _A container model of type theory._ 2021.

- Awodey, S. _Natural models of homotopy type theory._ Mathematical Structures in Computer Science, 28(2), 2018.

- Capriotti, P. and Kraus, N. _Univalent higher categories via complete semi-Segal types._ Proc. ACM Program. Lang. 2(POPL), 2018.

- Dybjer, P. _Internal type theory._ TYPES 1995, LNCS 1158, 1996.

- Ehresmann, C. _Gattungen von lokalen Strukturen._ Jahresber. Deutsch. Math.-Verein. 60, 1957.

- Gratzer, D., Weinberger, J., and Buchholtz, U. _Directed univalence in simplicial homotopy type theory._ 2024. [arXiv:2407.09146](https://arxiv.org/abs/2407.09146).

- Hasegawa, M. _A quantum double construction in Rel._ 2007. [arXiv:0711.4042](https://arxiv.org/abs/0711.4042).

- Hofmann, M. _Syntax and semantics of dependent types._ In Semantics and Logics of Computation, 1997.

- Jonsson, D. _On group-like magmoids._ (The source paper for this report.)

- Joyal, A. and Street, R. _Braided tensor categories._ Advances in Mathematics, 102(1), 1993.

- Kraus, N. _Internal higher-dimensional models of type theory._ 2021.

- Lumsdaine, P. L. _Weak ω-categories from intensional type theory._ Logical Methods in Computer Science, 6(3), 2010.

- Riehl, E. and Shulman, M. _A type theory for synthetic ∞-categories._ Higher Structures, 1(1), 2017. [arXiv:1705.07442](https://arxiv.org/abs/1705.07442).

- Spiwack, A. _An L-calculus._ (Referenced for the connection between linear logic and braided structural rules.)

- The Univalent Foundations Program. _Homotopy Type Theory: Univalent Foundations of Mathematics._ Institute for Advanced Study, 2013. Available at [homotopytypetheory.org/book](https://homotopytypetheory.org/book).

- van den Berg, B. and Garner, R. _Types are weak ω-groupoids._ Proc. London Math. Soc., 102(2), 2011.
