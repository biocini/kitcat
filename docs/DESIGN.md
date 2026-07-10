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

Cat.Virtual generalizes Cat.Type by gating composition with a
propositional classifier `classifier : hom x y → hom y z → Type p`
on composable pairs. `compose-contr` and `interchange` fire only
when the classifier holds. The plain category Cat.Type is recovered
by setting the classifier to `⊤` (contractible — always composable).
The former separate `Cat.Classified` module is folded into
Cat.Virtual.

The intended application is duploids, where composition is gated by
polarity: the classifier is the join `(is-pos f × is-pos g) ⊔
(is-neg f × is-neg g)`. Bipolar pairs (identity) get the
join-path identification. The lifting monad bridge internalizes
gated composition into a Kleisli category, making structural laws
into monad laws.

The classifier algebra — closure under whiskering, op,
intersection/union — gives a maximal sub-category: the universally
classifiable morphisms form a genuine (un-gated) Cat.Type.

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

Cat.Type's unit conditions reduce to e² = refl in path
groupoids: left absorption `emb e x e z h ≡ h` at h = refl gives
`e ∙ e ≡ refl`. The space K(ℤ/2, 1) = RP∞ has a nontrivial
element α with α² = refl; both refl and α satisfy all unit axioms.
`unit-is-prop` fails — there are at least two units.

Binary idempotency `yon e x e ≡ e` (the VirtualAlt formulation)
immediately forces e ≡ refl by right-composition with sym e. This
is strictly stronger than Cat.Type's action-idempotency.

The ℤ/2 gauge freedom: the map `f ↦ yon f x idn` is always an
involution (order ≤ 2). This is S₂ (symmetric), not B∞ (braided).
The obstruction maps onto the braided/symmetric distinction:
2-torsion-free categories (braid-like) have unique identities;
2-torsion categories (symmetric-like) have involution ambiguity.

Cat.Type derives `unit-is-prop` via the Kraus chain using the
full axiom set (compose-contr + interchange + yon-eval), resolving
the tension without requiring binary idempotency.

### Interchange propositionality

Can `is-category` (the conjunction of all Cat.Type fields) be a
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

## Monoidal Categories

A monoidal category is a one-object bicategory. Kitcat presents it
natively, over the same `category` record (Cat.Type), rather than
by delooping onto a Unit-object category. The object-level tensor
is read off a ternary `tensor-emb : ob → ob → ob → ob` — the
erased-object-index image of `category.emb`, with the two Unit hom
indices dropped. A parallel morphism-tier `htensor-emb` acts on
three parallel 2-cells (a trifunctor action). From `tensor-emb`
plus a unit, `tensor-compose-contr`, `tensor-interchange`, and
`tensor-yon-eval`, the binary tensor `_⊗_`, the associator, the
unitors, and unit uniqueness all derive exactly as Cat.Type derives
`_⨾_`, `assoc`, and the unit laws.

### Coherence is free where the fiber is fixed

The monoidal coherences run on the same h-level-0 fiber
contractibility that drives Cat.Coherence, and it draws a sharp
line between what is *free* and what is *irreducible data*.

A coherence obtained as `ap fst` of paths in a contractible
`tensor-emb`-fiber is free (forced by `is-contr→is-set`) **iff all
its vertices live in one fixed fiber**. The pentagon qualifies: the
five bracketings of a fourfold tensor all represent the same
operation `λ l r → tensor-emb x l (noy y (noy z r))`, so they are
fiber points of a single `tensor-E₄`, and the pentagon is a 2-path
in that one contractible fiber. Free.

The **triangle's** full form is the first place the fiber closes
only with extra data. The weak triangle is free; the full Mac Lane
triangle needs `absorb-coh` (a field of `monoidal-2-coherent`),
which bridges two *different* fibers — the left-absorption and the
interchange-plus-right-absorption decompositions of the same
object.

### absorb-coh is genuinely independent (a π₀ obstruction)

`absorb-coh` is not derivable from the base monoidal axioms. It
demands a comparison between two members of the `tensor-interchange`
family that the base never makes — concretely, that the interchange
loop at the generic tuple `(I,x,I,r)` equals the loop at the
degenerate tuple `(I,I,I,I)`. Perturbing `tensor-interchange` by a
loop family `ω` gives a defect `ω(I,x,I,r) − ω(I,I,I,I)`: a
*balanced difference* that vanishes on any connected carrier (a
uniform 2-torsion twist cancels), so only a **π₀-separated** carrier
(`S¹ × ℤ/2`, with `x` in a different component from `I`) refutes it.
The `Cat.Monoidal.Indiscrete` builder and `Cat.Monoidal.Twist`
(`twist-reduces-to-omega`) formalize the algebraic core; the
concrete carrier is a deferred `--cubical` island.

### Braiding: free scaffolding, irreducible hexagon

The braiding relocates the same free/field boundary one categorical
dimension up. Unlike the associator, the braid *moves* the
`tensor-emb` target — `x⊗y` and `y⊗x` represent different
operations — so it cannot be fiber-derived; it needs one field
(`tensor-flank-swap`, the half that `tensor-interchange` does not
already supply). But everything *around* it is free: the object
braiding `⊗-braid : x⊗y ≡ y⊗x`, its invertibility (it is a path),
its naturality, and the *reduction* of each hexagon to a
target-level 2-path all fall out of the fibers.

The **hexagon** itself is irreducible. Its six vertices span three
target-permutations, so it is a 2-path in `E ≃ ob` (not a set),
which `is-contr→is-set` cannot force — it is a genuine field
(`hexagon-emb`), consumed only as a witness-move that vanishes on
projection, so the derived object `⊗-hexagon` stays honest.

### The coherence tower tracks the sphere

Climbing the coherence tower, the irreducible residues track the
homotopy groups of the sphere, and the perturbation defects shift
from balanced to unbalanced:

| Level | Coherence | Defect | Obstruction |
|-------|-----------|--------|-------------|
| E₁ | `absorb-coh` (triangle) | `ω(I,x,I,r) − ω(I,I,I,I)` | π₀ (component separation) |
| E₂ | hexagon | `−ζ` (odd) | π₁, any nontrivial loop |
| E₂ | `β² = id` (symmetric) | `2ζ` (even) | π₁, 2-torsion |
| E₃ | syllepsis | η | π₁ˢ = ℤ/2 (Hopf) |

The `absorb-coh` defect is a balanced difference — it vanishes on
connected carriers, which is why it is a π₀ phenomenon. The braid
defects are unbalanced sums, nonzero even for a constant twist on a
connected carrier, so they are π₁. The symmetric gate `β² = id` is
the even (2-torsion) sub-case: this is where the classical
braided/symmetric distinction becomes the ℤ/2 = ⟨η⟩ of the first
stable stem, deriving (rather than assuming) the 2-torsion story of
the identity-uniqueness discussion above. Unlike the
Eckmann–Hilton / syllepsis setting, which works in `Ω²` with two
concatenations and *derives* the braid as a path, the `monoidal`
record has one tensor and no such input — so the braid is
irreducible data — but its coherence residue lands on the same
E₁→E₂→E₃ ladder, with the stable Hopf class η at the syllepsis
rung.

## Representable Codependent Categories

Kitcat's category layer has a representable presentation
(`Cat.Codep`), following the *codependent* side of Petrakis's
dependent-arrow program ("Categories with dependent arrows", where the
codependent variation is named as open future work) in the wild,
untruncated setting.

### One axiom, everything derived

The record has four fields:

```
hom : ob → ob → Type h
idn : (x : ob) → hom x x
emb : ∀ {x y} → hom x y → loose x y
compose-contr : ∀ f g → is-contr (fiber emb (emb f · g))
```

`loose x y = (γ : ctx x y) → fam (γ .fst)` is a genuine `Π` over the
canonical context, so its head stays visible and `loose-ext = funext`
computes. The codependent application `_·_` and its composition law
`·-comp` are derived (Petrakis's dependent-arrow composition,
(dep₂)); `compose-contr` is the single categorical axiom.

### Composition extracted from representability

This inverts the usual layering. Petrakis builds dependent arrows over
a primitive category; here composition is *extracted* from
representability instead. `fiber emb` plays the co-Σ role, and `_⨾_`
is the co-section read off `compose-contr f g .center .fst`. A single
`is-contr` short-circuits the tower of Σ-object composites: rather than
positing associative composition and then proving coherence, one posits
that the composite fiber is contractible and reads composition,
associativity, and all higher coherence out of it.

### Representable ⇒ coherent

Because `compose-contr` gives a contractible fiber, the whole pentagon
tower is free: `assoc` is `ap fst` of a path in the triple-composite
fiber, and the Mac Lane pentagon (and the `Kₙ` associahedra above it)
projects from `is-contr → is-n-type` on the quadruple fiber via the
`Core.Coherence.Base` engine (`coh-project`). No coherence is ever a
field. The pentagon consumes only `compose-contr` and `emb-comp` — it
is purely associativity and touches no unit law.

### The load-bearing mechanism: definitional re-anchoring

Representability is only free because the action is transport-free. A
context splits as `ctx = Σ pass acted`; `fam` reads only the passenger,
and `acted φ z := fam (at z φ)` is `fam` re-anchored to a new domain.
Re-anchoring `at` swaps in the identity binder and preserves the
acted-object, so `at z (at y φ) = at z φ` holds **definitionally**.
That is exactly what lets `act φ g α = emb g (at _ φ , α)` — acting is
`emb` at the identity context, `act = emb @ idn` — type-check with no
transport. The definitional idempotency is what converts
"representability needs coherence fields" into "representability is
free": `act-comp` becomes `emb-comp` at the identity context, and the
inner-associator pentagon face collapses to `ap-comp`.

### The identity anchor, and scope

`idn` is the **representable anchor** — the slot the action reads at —
posited, not characterized. No unit law and no identity uniqueness is
asserted or used. The two instances make this concrete: `Type-codep`
fills `idn` with an identity morphism (`C.idn`), `Monoidal-codep` fills
it with the tensor unit *object* `I`; the shared role is "anchor", not
"two-sided unit". This is the noy-side structure through the pentagon.

### The identity fragment: two layers over the anchor

The scope note above is resolved by two extension records
(`Cat.Codep.Coupling`, `Cat.Codep.Unit`) that characterize the anchor
without touching the base.

The **coupling** layer adds the two representable actions — `noy`
(acting on the acted slot) and `yon` (acting on the passenger binder)
— together with the two axioms relating them: `interchange` (the
actions commute; this is the L3.5 profunctorial link) and `yon-eval`
(the passenger action at the identity is the identity). From the
coupling *alone* the identity idempotency `idem : idn ⨾ idn ≡ idn`
derives, via `yon-composite` + `comp-eq`. This is the **linchpin**:
idempotency precedes absorption, and the two are not circular. The
guarantee is structural — `CouplingDerived`, the module that proves
`idem`, has no access to `absorb-l` (which lives downstream in the
unit layer), so the module boundary *enforces* absorption-freeness
rather than merely observing it.

The **unit** layer adds invertibility of the identity's two actions
(`unit-l-equiv`, `unit-r-equiv`). From these, absorption
(`absorb-l`/`absorb-r`) cancels the identity, the codependent identity
law `·-idn` (`F · idn ≡ F`) follows, the unit laws `unitl`/`unitr`
project from the contractible image fiber `emb-image-contr`, and
identity uniqueness `unit-is-prop` follows by the Kraus chain: `yon e`
squares to itself and is idempotent, so it absorbs, forcing `e ≡ idn`.

The uniqueness hypothesis is the **binary** yon-idempotency
`yon e e ≡ e`, obtained via `yon-eval`. This gives `e² = e` (not
`e² = 1`), which forces `e = idn` in the representable setting —
excluding the involution ambiguity (`e² = 1`) that a ternary
idempotency would admit. Involutions are excluded; the identity is
genuinely unique.

Together the two layers give the refactor blueprint
`Cat.Type.category ≅ codep-category + codep-coupling + codep-unit`:
the four-axiom canonical record decomposes into one representability
axiom plus the coupling and unit characterizations of its anchor. The
same decomposition instantiates over `Cat.Monoidal` (the anchor being
the tensor unit `I`), where the generic `absorb-l` coincides with the
concrete one definitionally, and `unitl`/`unit-is-prop` specialize in
statement (two fibers giving the same edge).

## References

- **STYLEGUIDE.md** — Formatting and naming conventions
- **Rijke, Introduction to HoTT** — Primary HoTT reference
- **1lab** (https://1lab.dev) — Idiomatic cubical Agda patterns
- **Riehl–Shulman** (arXiv:1705.07442) — Synthetic ∞-category theory
- **Capriotti–Kraus** (arXiv:1707.03693) — Univalent higher categories
- **Petrakis** (arXiv:2205.06651) — Univalent typoids
- **Petrakis** (arXiv:2303.14754) — Categories with dependent arrows;
  the codependent variation is named as open future work
- **Sterling** (jonmsterling.com/005B) — Virtual bicategory theory
- **Kelly** (J. Algebra 1964) — Mac Lane coherence, triangle not forced by pentagon
- **Joyal–Street** (Adv. Math. 1993) — Braided monoidal categories, hexagons
- **Sojakova** (LICS 2022) — The syllepsis in HoTT (Eckmann–Hilton, η at E₃)
