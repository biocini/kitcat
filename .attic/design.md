# Kitcat Design Philosophy

Kitcat is a self-contained cubical Agda library with two faces: a
practical standard library (`Core.*`, `Data.*`, `Trait.*`) and a
synthetic theory of wild categories (`Cat.*`). Both are built on
univalent type theory, sharing foundational infrastructure.

## Core Library

The `Core.*` / `Data.*` / `Trait.*` namespaces provide data
structures, algorithms, and abstractions familiar to Haskell/Idris2
programmers, grounded in HoTT. APIs are modeled on the Idris2
standard library where applicable — `Eq`, `Ord`, `Functor`, `Monad`
— adapted to programming in univalent type theory.

### Principles

1. **Correct and performant.** Both are goals, not trade-offs.
2. **Minimalism.** Every definition earns its place.
3. **Composability.** Small, orthogonal pieces that combine.
4. **Cubical idioms.** Direct path algebra and hcom over
   transport-heavy approaches.

### Module organization

- `Core.*` — Stable foundational primitives
- `Data.*` — Concrete data types and properties
- `Cat.*` - Higher category theory

### Safety

All code compiles with:
```agda
{-# OPTIONS --safe --erased-cubical #-}
```
No postulates or unsafe features without explicit authorization.
Kitcat is self-contained: no external library dependencies.

## Synthetic Wild Category Theory

The `Cat.*` namespace develops a synthetic theory of wild
(untruncated) ∞-categories in standard cubical Agda. The theory is
internal to HoTT — contractibility, equivalences, fibers, and
h-levels are the native vocabulary for categorical notions. No
truncation hypotheses on hom types.


### The h-level shift: from paths to representable categories

The relationship between path types and representable categories is an
h-level shift in the representation of composition.

**Representable categories (h-level 1 representation).** Each
morphism `f` uniquely determines a composition operator `emb f` —
`emb-image-contr` gives h-level 0 in the fiber. But the space of all
operators of the right type is larger: non-representable operators
exist. So `emb` is an embedding (propositional fibers, h-level 1
globally), not an equivalence.

This is the structural content of the representable theory: morphisms
faithfully *represent* composition behavior without *being* it.

### Why truncation is irrelevant

The theory operates at two h-levels, neither of which is the hom
level:

- **h-level 0 (fiber level):** `compose-contr` and
  `emb-image-contr` give contractible fibers. All derived structure
  (associativity, unit laws, pentagon, triangle) follows from
  contractibility of these fibers.

- **h-level 1 (representation level):** `emb` is an embedding.
  The composite-centric style works here.

Hom types float at arbitrary h-level. The theory never touches them
directly — only through the controlled h-level 0/1 layers above.
This is why the library handles path groupoids on arbitrary types
(including non-truncated ones) without truncation hypotheses.

### Composite-centric style

Associativity, unit laws, and higher coherences are defined as
`ap fst` of paths in contractible fibers (the Cat.Coherence
approach), never as direct hom-level path constructions.

### Fibered constructions decompose along the h-level boundary

When building structure over a representable category — displayed
categories, slices, covariant families, Yoneda — the structural
obligations decompose along the h-level boundary:

- **h-level 0 (path-level):** Obligations about paths ending at a
  fixed target (reversed singletons). These arise as second
  components of Σ-typed morphism spaces like `Σ k, k ⨾ fB ≡ fA`.
  Handled by `SinglP-contr` / `Singl-contr`. Always contractible.

- **h-level 1 (morphism-level):** Obligations about composition
  fibers. These arise as first components. Handled by
  `pull-contr` / `emb-image-contr`. Contractible by the
  representation axioms.

Factor contractibility proofs along this boundary:
Σ-reassociate the fiber to separate h-level 0 and h-level 1 parts,
then apply `SinglP-contr` and `compose-contr` independently.



### The coherence boundary

Pentagon is provable from base axioms alone. 

### Bimodule action perspective

`emb f` can be viewed as a bimodule action over two bundles:

```
Σ w, hom w x    (incoming to x, centered at (x, idn))
Σ v, hom y v    (outgoing from y, centered at (y, idn))
```

Restricting `emb f` to the center of each bundle recovers `f`:
```
Π(Σ w, hom w x)(Σ v, hom y v). hom w v
    → Π(Σ v, hom y v). hom x v        (restrict to (x, idn))
    → hom x y                          (restrict to (y, idn))
```

In the path groupoid, both bundles are contractible (Singl-contr),
so `emb` is an equivalence — every bimodule map is representable.
In general, `emb` is an embedding: morphisms faithfully represent
their bimodule actions, but non-representable operators exist. This
gap is the representable structure.

### Identity uniqueness and 2-torsion

Cat.Type's unit conditions reduce to e² = refl in path
groupoids: left absorption `emb e x e z h ≡ h` at h = refl gives
`e ∙ e ≡ refl`. The space K(ℤ/2, 1) = RP∞ has a nontrivial
element α with α² = refl; both refl and α satisfy all unit axioms.
`unit-is-prop` fails — there are at least two units.

The ℤ/2 gauge freedom: the map `f ↦ yon f x idn` is always an
involution (order ≤ 2). This is S₂ (symmetric), not B∞ (braided).
The obstruction maps onto the braided/symmetric distinction:
2-torsion-free categories (braid-like) have unique identities;
2-torsion categories (symmetric-like) have involution ambiguity.

Cat.Type derives `unit-is-prop` via the Kraus chain using the
full axiom set (compose-contr + interchange + yon-eval), resolving
the tension without requiring binary idempotency.

### Interchange propositionality

The S² counterexample: interchange is a path `LHS ≡ RHS` in
hom w v. By `emb-image-contr`, this is equivalent to
`emb LHS ≡ emb RHS` in a function space that inherits higher
homotopy from hom. For S², π₃(S²) ≅ ℤ gives a nontrivial loop
in the space of interchange proofs.

This is the structural gap between strict 2-categories (interchange
= identity, propositional) and wild ∞-categories (interchange =
higher cell with its own coherences).

- **Petrakis** (arXiv:2303.14754) — Categories with dependent arrows;
  the codependent variation is named as open future work
- **Sterling** (jonmsterling.com/005B) — Virtual bicategory theory
- **Kelly** (J. Algebra 1964) — Mac Lane coherence, triangle not forced by pentagon
- **Joyal–Street** (Adv. Math. 1993) — Braided monoidal categories, hexagons
- **Sojakova** (LICS 2022) — The syllepsis in HoTT (Eckmann–Hilton; η
  at the operadic E₃ level — unrelated to the code fiber `E₃`)
