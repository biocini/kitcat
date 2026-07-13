The walking arrow (two objects, one non-identity morphism) as a
Cat.Base.category instance. Demonstrates that the yon-equiv
formulation admits non-groupoidal categories: there is a morphism
ob₀ → ob₁ with no inverse.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Test.WalkingArrow where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Equiv.Base
open import Cat.Base
```

## Objects and hom

Two objects. The only non-identity morphism goes ob₀ → ob₁; there
is no morphism ob₁ → ob₀.

```agda
private
  data Obj : Type where
    ob₀ ob₁ : Obj

  Arr : Obj → Obj → Type
  Arr ob₀ ob₀ = ⊤
  Arr ob₀ ob₁ = ⊤
  Arr ob₁ ob₀ = ⊥
  Arr ob₁ ob₁ = ⊤

  absurd : ∀ {u} {A : Type u} → ⊥ → A
  absurd ()
```

## Yoneda map

Post-composition: `yon f w k` is "k followed by f". Identity
morphisms act as identity; the unique ob₀→ob₁ arrow absorbs
everything from the left.

```agda
  yon-w : ∀ {x y} → Arr x y → ∀ w → Arr w x → Arr w y
  yon-w {x = ob₀} {y = ob₀} _ _ k = k
  yon-w {x = ob₀} {y = ob₁} _ ob₀ _ = tt
  yon-w {x = ob₀} {y = ob₁} _ ob₁ ()
  yon-w {x = ob₁} {y = ob₀} ()
  yon-w {x = ob₁} {y = ob₁} _ _ k = k
```

## yon is an equivalence

For each (x,y) pair, both Arr x y and the target Π-type are
either both contractible (≅ ⊤, via eta) or both empty. The
retractions hold because ⊤ has eta-equality (any element is
definitionally tt) and ⊥ is eliminated by absurd patterns.

```agda
  yon-w-equiv : ∀ {x y} → is-equiv (yon-w {x} {y})
  yon-w-equiv {x = ob₀} {y = ob₀} =
    iso→equiv yon-w (λ _ → tt) (λ _ → refl) ret .snd
    where
      ret : ∀ α → yon-w {x = ob₀} {y = ob₀} tt ≡ α
      ret α i ob₀ tt = tt
      ret α i ob₁ ()
  yon-w-equiv {x = ob₀} {y = ob₁} =
    iso→equiv yon-w (λ _ → tt) (λ _ → refl) ret .snd
    where
      ret : ∀ α → yon-w {x = ob₀} {y = ob₁} tt ≡ α
      ret α i ob₀ tt = tt
      ret α i ob₁ ()
  yon-w-equiv {x = ob₁} {y = ob₀} .eqv-fibers α = absurd (α ob₁ tt)
  yon-w-equiv {x = ob₁} {y = ob₁} =
    iso→equiv yon-w (λ _ → tt) (λ _ → refl) ret .snd
    where
      ret : ∀ α → yon-w {x = ob₁} {y = ob₁} tt ≡ α
      ret α i ob₀ tt = tt
      ret α i ob₁ tt = tt
```

## yon-op is an equivalence

yon-op f z g = yon g x f, i.e. pre-composition by f. Same
analysis: target Π-types are contractible or empty.

```agda
  yon-op-w : ∀ {x y} → Arr x y → ∀ z → Arr y z → Arr x z
  yon-op-w {x} f z g = yon-w g x f

  yon-op-equiv : ∀ {x y} → is-equiv (yon-op-w {x} {y})
  yon-op-equiv {x = ob₀} {y = ob₀} =
    iso→equiv yon-op-w (λ _ → tt) (λ _ → refl) ret .snd
    where
      ret : ∀ α → yon-op-w {x = ob₀} {y = ob₀} tt ≡ α
      ret α i ob₀ tt = tt
      ret α i ob₁ tt = tt
  yon-op-equiv {x = ob₀} {y = ob₁} =
    iso→equiv yon-op-w (λ _ → tt) (λ _ → refl) ret .snd
    where
      ret : ∀ α → yon-op-w {x = ob₀} {y = ob₁} tt ≡ α
      ret α i ob₀ ()
      ret α i ob₁ tt = tt
  yon-op-equiv {x = ob₁} {y = ob₀} .eqv-fibers α = absurd (α ob₀ tt)
  yon-op-equiv {x = ob₁} {y = ob₁} =
    iso→equiv yon-op-w (λ _ → tt) (λ _ → refl) ret .snd
    where
      ret : ∀ α → yon-op-w {x = ob₁} {y = ob₁} tt ≡ α
      ret α i ob₀ ()
      ret α i ob₁ tt = tt
```

## Assembly

```agda
walking-arrow : category 0ℓ 0ℓ
walking-arrow .category.ob = Obj
walking-arrow .category.hom = Arr
walking-arrow .category.yon = yon-w
walking-arrow .category.yon-equiv = yon-w-equiv
walking-arrow .category.yon-op-equiv = yon-op-equiv
```

The walking arrow has Arr ob₁ ob₀ = ⊥, so the unique morphism
ob₀ → ob₁ has no inverse. This category is not a groupoid,
confirming that Cat.Base admits non-groupoidal models.
