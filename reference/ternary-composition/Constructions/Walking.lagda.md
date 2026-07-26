The walking morphism: the interval category **2** with two objects
and a single non-identity morphism from source to target. This is
the partial order `false ≤ true` viewed as a Cat.Virtual category.

All inhabited hom types are `⊤` (contractible), so composition,
units, and interchange are trivial.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Walking where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Bool using (Bool; true; false)
open import Core.Data.Empty using (⊥; ex-falso)
open import Core.Kan
  using (is-contr→is-prop; is-contr→is-set; Σ-contr-contr)
open import Core.Transport.Properties
  using (prop-inhabited→is-contr; is-prop→is-set)
open import Core.Trait.Trunc
  using (Π-is-prop; Σ-prop-path)
open import Core.HLevel.Base
  using (is-prop→Path-is-contr; ⊤-is-contr; ⊤-is-prop)
open import Core.Equiv.Base using (is-equiv; eqv-fibers)
open import Core.Equiv.Properties using (prop→endo-is-equiv)
open import Cat.Virtual using (category)
```

## Hom type

```agda
Arrow : Bool → Bool → Type
Arrow false false = ⊤
Arrow false true  = ⊤
Arrow true  false = ⊥
Arrow true  true  = ⊤
```


## Propositionality

Each Arrow type is either `⊤` or `⊥`, both propositions.

```agda
Arrow-is-prop : ∀ x y → is-prop (Arrow x y)
Arrow-is-prop false false = ⊤-is-prop
Arrow-is-prop false true  = ⊤-is-prop
Arrow-is-prop true  false x = ex-falso x
Arrow-is-prop true  true  = ⊤-is-prop

Arrow-is-set : ∀ x y → is-set (Arrow x y)
Arrow-is-set x y = is-prop→is-set (Arrow-is-prop x y)
```


## Ternary composition

Given `f : Arrow x y`, `a : Arrow w x`, `b : Arrow y z`, produce
`Arrow w z`. When `w = false` or `z = true`, the output is `⊤` and
we return `tt`. The remaining case `w = true, z = false` is absurd:
it forces a chain of contradictions through the inputs.

```agda
comp : ∀ {x y} → Arrow x y
  → ∀ w → Arrow w x → ∀ z → Arrow y z → Arrow w z
comp f false a false b = tt
comp f false a true  b = tt
comp f true  a true  b = tt
comp {x = false}             f true a false b = ex-falso a
comp {x = true} {y = false}  f true a false b = ex-falso f
comp {x = true} {y = true}   f true a false b = ex-falso b
```


## Helpers

```agda
idn : ∀ x → Arrow x x
idn false = tt
idn true  = tt
```

The function type `∀ w → Arrow w x → ∀ v → Arrow y v → Arrow w v`
is a proposition (iterated Π into propositions).

```agda
private
  emb-fn-is-prop
    : ∀ {x y}
    → is-prop (∀ w → Arrow w x → ∀ v → Arrow y v → Arrow w v)
  emb-fn-is-prop =
    Π-is-prop λ w → Π-is-prop λ _ →
    Π-is-prop λ v → Π-is-prop λ _ →
    Arrow-is-prop w v
```


## Category instance

```agda
𝟐 : category _ _
𝟐 .category.ob = Bool
𝟐 .category.hom = Arrow
𝟐 .category.emb = comp
```

### Unit

The identity at every object is `tt : ⊤ = Arrow x x`. Both
left and right actions are endofunctions on contractible types,
hence equivalences. Idempotency holds because the codomain is a
proposition.

```agda
𝟐 .category.unit {x} =
  idn x
  , (left-eqv , right-eqv)
  , left-idpt , right-idpt
  where
  e = idn x

  left-eqv : ∀ {z} → is-equiv (λ (h : Arrow x z) →
    comp e x e z h)
  left-eqv = prop→endo-is-equiv (Arrow-is-prop x _) _

  right-eqv : ∀ {w} → is-equiv (λ (g : Arrow w x) →
    comp e w g x e)
  right-eqv = prop→endo-is-equiv (Arrow-is-prop _ x) _

  left-idpt : ∀ {z} (h : Arrow x z)
    → comp e x e z (comp e x e z h) ≡ comp e x e z h
  left-idpt h = Arrow-is-prop x _ _ _

  right-idpt : ∀ {w} (g : Arrow w x)
    → comp e w (comp e w g x e) x e
    ≡ comp e w g x e
  right-idpt g = Arrow-is-prop _ x _ _
```

### Composition contractibility

Given `f : Arrow x y` and `g : Arrow y z`, the composite
`s : Arrow x z` exists (transitivity of the order) and the path
component is contractible (path in a proposition).

```agda
𝟐 .category.compose-contr {x} {y} {z} f g =
  Σ-contr-contr
    (prop-inhabited→is-contr
      (Arrow-is-prop x z) (comp f x (idn x) z g))
    path-contr
  where
  noy-g : ∀ v → Arrow z v → Arrow y v
  noy-g v b = comp g y (idn y) v b

  path-contr : (s : Arrow x z) → is-contr
    (comp s ≡ (λ w a v b → comp f w a v (noy-g v b)))
  path-contr s = is-prop→Path-is-contr
    emb-fn-is-prop (comp s) _
```

### Interchange

Both sides land in `Arrow w v`, which is a proposition.

```agda
𝟐 .category.interchange {x} {y} {z} f g w a v b =
  Arrow-is-prop w v _ _
```
