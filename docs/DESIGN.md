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
- `Trait.*` — Typeclass-like interfaces (Idris2-style)
- `Meta.*` — Metaprogramming and tactics

### Safety

All code compiles with:
```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}
```
`--no-sized-types` is set globally in `kitcat.agda-lib`.
No postulates or unsafe features without explicit authorization.
Self-contained: no external library dependencies.

## Synthetic Virtual Category Theory

The `Cat.*` namespace develops a synthetic theory of wild
(untruncated) ∞-categories in standard cubical Agda. The theory is
internal to HoTT — contractibility, equivalences, fibers, and
h-levels are the native vocabulary for categorical notions. No
truncation hypotheses on hom types.

### The primitive: ternary embedding

The single primitive is `emb`:
```
emb : hom x y → ∀ w → hom w x → ∀ v → hom y v → hom w v
```

A morphism `f : hom x y` determines a ternary composition operator
`emb f` that takes a morphism into `x`, the morphism `f` itself, and
a morphism out of `y`, and produces the composite. All categorical
structure is derived from `emb` plus four axioms:

- **`unit`** — a chosen identity with left/right equivalences and
  yon-idempotency
- **`compose-contr`** — contractibility of composition fibers
- **`interchange`** — noy and yon views of composition agree
- **`yon-eval`** — evaluating at the identity recovers the morphism

### The h-level shift: from paths to virtual categories

The relationship between path types and virtual categories is an
h-level shift in the representation of composition.

**Path types (h-level 0 representation).** A path `p : x ≡ y` IS
its composition behavior. The singleton type `Σ y, x ≡ y` is
contractible (`Singl-contr`), giving h-level 0. The ternary map
`emb p w a v b = a ∙ p ∙ b` is an equivalence: every polymorphic
binary composition operator on paths arises from a unique path. This
is the free theorem / parametricity for the identity type.

**Virtual categories (h-level 1 representation).** Each morphism `f`
uniquely determines a composition operator `emb f` —
`emb-image-contr` gives h-level 0 in the fiber. But the space of all
operators of the right type is larger: non-representable operators
exist. So `emb` is an embedding (propositional fibers, h-level 1
globally), not an equivalence.

This is the structural content of virtual category theory: morphisms
faithfully *represent* composition behavior without *being* it.
`yon-eval` witnesses the section: evaluating the representation at
the identity recovers the morphism. `emb-section` /
`emb-retraction` witness that `emb-inj` and `ap emb` are mutual
inverses.

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

The native notion of "these compose to that" is `_⨾_=>_` (the
composite witness, a fiber of `emb`), NOT bare path equality `≡`.

Working with `_⨾_=>_` stays at h-level 1 — the emb fiber level —
where contractibility gives structural leverage. Dropping to bare `≡`
via `cast-path` exits this layer into the potentially wild hom-level.

Associativity, unit laws, and higher coherences are defined as
`ap fst` of paths in contractible fibers (the Cat.Coherence
approach), never as direct hom-level path constructions.

### Fibered constructions decompose along the h-level boundary

When building structure over a virtual category — displayed
categories, slices, covariant families, Yoneda — the structural
obligations decompose along the h-level boundary:

- **h-level 0 (path-level):** Obligations about paths ending at a
  fixed target (reversed singletons). These arise as second
  components of Σ-typed morphism spaces like `Σ k, k ⨾ fB ≡ fA`.
  Handled by `SinglP-contr` / `Singl-contr`. Always contractible.

- **h-level 1 (morphism-level):** Obligations about composition
  fibers. These arise as first components. Handled by
  `compose-contr` / `emb-image-contr`. Contractible by the virtual
  category axioms.

Factor contractibility proofs along this boundary:
Σ-reassociate the fiber to separate h-level 0 and h-level 1 parts,
then apply `SinglP-contr` and `compose-contr` independently.

### Derived structure

From the four axioms, the following are derived (not axiomatized):

- **Composition** `_⨾_` — from `compose-contr`
- **Absorption** `absorb-l`, `absorb-r` — noy/yon of identity
- **Unit laws** `unitl`, `unitr` — from `emb-image-contr`
- **Associativity** `assoc` — from `E₃-contr`
- **Pentagon** — from `E₄-contr` (Cat.Coherence)
- **Weak triangle** — from base (Cat.Coherence)
- **Full Mac Lane triangle** — requires `2-coherent` (`absorb-coh`)
- **Identity uniqueness** `unit-is-prop` — via Kraus chain
- **Opposite** `op`, `op-invol` — argument swap on `emb`
- **Embedding** `emb-is-embedding`, `emb-section`, `emb-retraction`
- **Covariant families** — functors C → Type with `yon` action (Cat.Covariant)
- **Yoneda lemma** — `nat-trans (hom-cov a) P ≅ P.Fib a` (Cat.Yoneda)
- **Product categories** — `_×cat_` with component-wise structure (Cat.Product)
- **Rezk completion** — HIT quotient by neutral morphisms, requires `--cubical` (Cat.Rezk)

### Relationship to simplicial HoTT

Riehl–Shulman's simplicial HoTT uses extension types to define
∞-categories, making horn maps equivalences. Virtual categories
weaken this: `emb` is an embedding, not an equivalence. The gap is
the non-representable operators — composition behaviors with no
corresponding morphism.

| Framework | Composition | Representation | Horn maps |
|-----------|-------------|----------------|-----------|
| Path types | h-level 0 | h-level 0 (equiv) | — |
| Virtual categories | h-level 0 | h-level 1 (embedding) | — |
| Simplicial HoTT | h-level 0 | h-level 0 (equiv via ext) | equiv |

The gap closes in groupoids, where inverses make `emb` surjective
on the relevant operators. This connects to the braided/symmetric
distinction: 2-torsion-free categories (braid-like) have unique
identities; 2-torsion categories (symmetric-like) have involution
ambiguity.

### Classified virtual categories

Cat.Classified generalizes Cat.Virtual by gating composition with a
propositional classifier `classifier : hom x y → hom y z → Type p`
on composable pairs. `compose-contr` and `interchange` fire only
when the classifier holds. Cat.Virtual is recovered by setting the
classifier to `⊤` (contractible — always composable).

The intended application is duploids, where composition is gated by
polarity: the classifier is the join `(is-pos f × is-pos g) ⊔
(is-neg f × is-neg g)`. Bipolar pairs (identity) get the
join-path identification. The lifting monad bridge internalizes
gated composition into a Kleisli category, making structural laws
into monad laws.

The classifier algebra — closure under whiskering, op,
intersection/union — gives a maximal sub-category: the universally
classifiable morphisms form a genuine Cat.Virtual.

### The coherence boundary

Pentagon is provable from base axioms alone. Five bracketings of a
4-fold composite live as fiber points in `E₄-contr f g h k`
(contractible). The five associator edges are fiber paths; the
pentagon identity holds by `is-contr→is-set`. Face lemmas identify
abstract edges with geometric operations via `total-contr-unique`.

The full Mac Lane triangle requires `absorb-coh`, bundled in the
`2-coherent` record. It mediates between two fiber decompositions
of `absorb-l (noy f v b)`: one via interchange and one via
`absorb-r`. The weak triangle (provable from base) leaves one edge
as an abstract fiber path; the full triangle identifies it with
`ap (f ⨾_) (unitl g)`, which lives in a different fiber
(`composable-contr idn g` vs `composable-contr f g`). The
`absorb-coh` axiom bridges the two fibers.

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
gap is the virtual structure.

### Identity uniqueness and 2-torsion

Cat.Virtual's unit conditions reduce to e² = refl in path
groupoids: left absorption `emb e x e z h ≡ h` at h = refl gives
`e ∙ e ≡ refl`. The space K(ℤ/2, 1) = RP∞ has a nontrivial
element α with α² = refl; both refl and α satisfy all unit axioms.
`unit-is-prop` fails — there are at least two units.

Binary idempotency `yon e x e ≡ e` (the VirtualAlt formulation)
immediately forces e ≡ refl by right-composition with sym e. This
is strictly stronger than Cat.Virtual's action-idempotency.

The ℤ/2 gauge freedom: the map `f ↦ yon f x idn` is always an
involution (order ≤ 2). This is S₂ (symmetric), not B∞ (braided).
The obstruction maps onto the braided/symmetric distinction:
2-torsion-free categories (braid-like) have unique identities;
2-torsion categories (symmetric-like) have involution ambiguity.

Cat.Virtual derives `unit-is-prop` via the Kraus chain using the
full axiom set (compose-contr + interchange + yon-eval), resolving
the tension without requiring binary idempotency.

### Interchange propositionality

Can `is-category` (the conjunction of all Cat.Virtual fields) be a
property — a proposition that any two inhabitants are equal?

- **unit**: yes — `unit-is-prop` via Kraus chain
- **compose-contr**: yes — `is-contr` is propositional
- **yon-eval**: yes — lives in a contractible fiber
- **interchange**: NO

The S² counterexample: interchange is a path `LHS ≡ RHS` in
hom w v. By `emb-image-contr`, this is equivalent to
`emb LHS ≡ emb RHS` in a function space that inherits higher
homotopy from hom. For S², π₃(S²) ≅ ℤ gives a nontrivial loop
in the space of interchange proofs.

This is the structural gap between strict 2-categories (interchange
= identity, propositional) and wild ∞-categories (interchange =
higher cell with its own coherences).

## References

- **STYLEGUIDE.md** — Formatting and naming conventions
- **Rijke, Introduction to HoTT** — Primary HoTT reference
- **1lab** (https://1lab.dev) — Idiomatic cubical Agda patterns
- **Riehl–Shulman** (arXiv:1705.07442) — Synthetic ∞-category theory
- **Capriotti–Kraus** (arXiv:1707.03693) — Univalent higher categories
- **Petrakis** (arXiv:2205.06651) — Univalent typoids
- **Sterling** (jonmsterling.com/005B) — Virtual bicategory theory
