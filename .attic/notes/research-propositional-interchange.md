# Research: Propositional Interchange for Virtual Categories

## Problem Statement

In the virtual category formulation (Cat.Virtual), `is-category` on a
graph `(ob, hom, emb)` factors into propositional and structural
components:

- `unit` — propositional (unique identity via Kraus argument)
- `compose-contr` — propositional (is-contr is always a prop)
- `yon-eval` — propositional (lives in contractible emb-image fiber)
- `interchange` — NOT propositional (S² counterexample: π₃(S²) ≅ ℤ)

**Question:** Is there a formulation of virtual categories where ALL
axioms are propositional, making `is-category` a property of
`(ob, hom, emb)` rather than additional structure? Or is
non-propositional interchange intrinsic to wild higher categories?

## The Category Record

```
record category o h where
  ob  : Type o
  hom : ob → ob → Type h
  emb : ∀ {x y} → hom x y
      → ∀ w → hom w x → ∀ z → hom y z → hom w z

  unit : ∀ {x} →
    Σ e ∶ hom x x
    , ( (∀ {z} → is-equiv (λ h → emb e x e z h))
      × (∀ {w} → is-equiv (λ g → emb e w g x e)))
    × (emb e x e x e ≡ e)

  compose-contr : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr (Σ s ∶ hom x z
               , emb s ≡ (λ w a v b → emb f w a v (noy g v b)))

  interchange : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb f w a v (noy g v b) ≡ emb g w (yon f w a) v b

  yon-eval : ∀ {x y} (f : hom x y) → yon f x idn ≡ f
```

Where `noy f z h = emb f _ idn z h` and `yon f w g = emb f w g _ idn`.

## Key Derived Facts

- `idn = unit .fst` (the identity morphism)
- `f ⨾ g = compose-contr f g .center .fst` (composition)
- `emb-composite : emb (f ⨾ g) ≡ noy-target` (from compose-contr center)
- `absorb-l : noy idn z h ≡ h` (derived from yon-eval → comp-eq → idem → equiv→lc)
- `absorb-r : yon idn w g ≡ g` (same chain)
- `unitl, unitr, assoc` (from contractible emb-image fibers)
- `unit-is-prop` (any alternative unit equals idn, via Kraus chain)
- `emb-image-contr : is-contr (Σ g, emb g ≡ emb f)` (emb is an embedding)
- `emb-inj : emb f ≡ emb g → f ≡ g` (from emb-image-contr)

## Why Other Axioms Are Propositional

**unit:** The type `Σ e, (equivs) × (yon-idpt)` is a proposition because
`unit-is-prop` shows any two inhabitants have equal first components, and
the remaining components are propositions (`is-equiv` is a prop, and the
yon-idpt path lives in the contractible emb-image fiber at `e`).

**compose-contr:** `is-contr X` is always a proposition (Rijke 12.1.4).

**yon-eval:** `yon f x idn ≡ f` is a path in `hom x y`. Both `yon f x idn`
and `f` are in the contractible fiber `Σ g, emb g ≡ emb f` (via
emb-image-contr). The path between them, as an element of a contractible
type's path space, is unique.

## Why Interchange Is NOT Propositional

**Counterexample:** Path groupoid on S². Take `x = y = z = base`,
`f = g = refl` (or specific 2-loops). The interchange equation becomes a
path between specific composites of 2-cells. The space of such paths is
`Ω²(S², base)`, which has `π₂(S²) ≅ ℤ`. So there are countably many
distinct interchange proofs — not propositional.

**The obstruction:** Interchange is a path `LHS ≡ RHS` in `hom w v`. By
emb-image-contr, this is equivalent to `emb LHS ≡ emb RHS` in the
function space. But the function space `∀ w → hom w x → ∀ v → hom y v → hom w v`
inherits the higher homotopy of `hom`, so paths in it are NOT propositional
for wild types.

## Failed Approaches

### Joint contractible fiber

Bundle both noy and yon characterizations into one fiber:
```
is-contr (Σ s, (emb s ≡ noy-target) × (emb s ≡ yon-target))
```

**Why it fails:** This type is equivalent to `noy-fiber × (noy-target ≡ yon-target)`.
The noy-fiber is contractible, but `noy-target ≡ yon-target` is a path in the
function space — not contractible for wild types. So the joint fiber is not
contractible. It CANNOT be provided for path groupoids on S².

### Two independent contractible fibers

Provide noy-fiber and yon-fiber as separate contractible axioms. Derive
interchange as the connection between their centers.

**Why it fails:** The two centers might be different morphisms. Connecting them
requires `noy-target ≡ yon-target` — which IS interchange. Circular. The
theoretician confirmed this is a reorganization, not an improvement: same
data content, more axioms.

### Absorb interchange into emb

Make `emb` carry interchange data in its type.

**Why it fails:** Relocates the non-propositional data from "interchange
axiom" into "emb". Does not eliminate the structure — just moves it.

## The Categorical Picture

Non-propositional interchange reflects the distinction between:
- **Strict 2-categories:** interchange is identity (propositional)
- **Bicategories:** interchange is invertible 2-cell (structure)
- **Wild ∞-categories:** interchange is higher cell with its own coherences

Cat.Virtual, when instantiated to path groupoids on arbitrary types, gives
wild ∞-groupoids. The interchange is an infinite tower of coherence data.
No finite truncation is propositional for arbitrary types.

**The parallel:** In the univalent categories literature (Ahrens-Kapulkin-Shulman),
`is-category = is-precategory × is-univalent`. Here the analogue is
`is-category = is-pre-category × interchange`, where
`is-pre-category = unit × compose-contr × yon-eval` IS propositional.

## Research Directions

1. **Is there a richer `emb` type where interchange becomes derivable?**
   Perhaps `emb` could be a profunctor-valued map with enough structure
   that interchange follows from a universal property.

2. **Can interchange be located in a contractible type that is NOT a
   fiber of emb?** Some other contractible space — perhaps related to
   the total space of composable triples, or a higher Segal condition.

3. **For which categories IS interchange propositional?** Beyond 1-types
   (where hom is a set), are there structural conditions weaker than
   h-level 1 that make interchange propositional? (E.g., categories
   enriched in specific monoidal categories.)

4. **Does the non-propositionality of interchange give meaningful
   invariants?** The "space of interchange proofs" is `Ω(hom)` at specific
   points. Does this carry interesting categorical content? Is it related
   to the center/Drinfeld center of the category?

5. **Virtual equipment perspective:** In Cruttwell-Shulman's virtual
   equipments, interchange is part of the fc-multicategory structure. Is
   there a formulation using the equipment's universal property that
   makes interchange propositional? (Equipments characterize profunctor
   composition via a universal property.)

6. **Segal condition approach:** In Rezk/complete Segal spaces, composition
   is characterized by a Segal condition (contractibility of the space of
   composites). Interchange in that setting is derivable from the Segal
   condition + completeness. Can a virtual analogue of the Segal condition
   absorb interchange?

## References

- Rijke, "Introduction to Homotopy Type Theory" — h-levels, contractibility, propositions
- Ahrens-Kapulkin-Shulman, "Univalent categories and the Rezk completion"
- Cruttwell-Shulman, "A unified framework for generalized multicategories"
- Leinster, "Higher Operads, Higher Categories" — fc-multicategories
- Capriotti-Kraus, "Univalent higher categories via complete semi-Segal types"
- Sterling, virtual bicategory theory (jonmsterling.com/005B)
- Schreiber, "Differential cohomology in a cohesive infinity-topos" — gauge transformations in HoTT
