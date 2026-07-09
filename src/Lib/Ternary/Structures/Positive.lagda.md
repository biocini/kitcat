Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures/Positive.agda`.

A ternary relation is *positive* (with respect to an auxiliary preorder
`_≤ₐ_`) when any split makes the parts no bigger than the whole.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures.Positive where

open import Core.Type using (Type; Level; _⊔_; _₊)
open import Core.Base using (_≡_; refl; ap)
open import Core.Path.Base using (_≢_)
open import Core.Data.Sigma using (Sigma; _,_; fst; snd; _×_)
open import Core.Data.Empty using (¬_; ex-falso)
open import Lib.Relation.Unary
open import Lib.Relation.Binary
open import Lib.Ternary.Core
open import Lib.Ternary.Structures.PartialSemigroup
open import Lib.Ternary.Structures.PartialMonoid

-- A minimal preorder on the carrier (ported slice of Relation.Binary.Structures.IsPreorder).
record IsPreorder {a ℓ₁ ℓ₂} {A : Type a}
  (_≈_ : Rel A ℓ₁) (_∼_ : Rel A ℓ₂) : Type (a ⊔ ℓ₁ ⊔ ℓ₂) where
  no-eta-equality
  field
    ⦃ isEquivalence ⦄ : IsEquivalence _≈_
    reflexive : ∀ {x y} → x ≈ y → x ∼ y
    trans     : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
{-# INLINE IsPreorder.constructor #-}

Positive : ∀ {a} {A : Type a} → Rel₃ A → A → Type _
Positive rel ε =
  let open Rel₃ rel in ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → (Φ₁ , Φ₂) ≡ (ε , ε)

-- NonNegativity: split-off fragments are not bigger than their source.
record IsPositive {a} {A : Type a} {e} s
  (_≈_ : A → A → Type e) (rel : Rel₃ A) : Type (a ⊔ e ⊔ (s ₊)) where
  open Rel₃ rel

  field
    {_≤ₐ_}   : A → A → Type s
    orderₐ   : IsPreorder _≈_ _≤ₐ_

    positiveˡ : ∀ {Φ₁ Φ₂ Φ} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₁ ≤ₐ Φ
    positiveʳ : ∀ {Φ₁ Φ₂ Φ} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₂ ≤ₐ Φ

-- With ε as the smallest element.
record IsPositiveWithZero {a} {A : Type a} {e} s
  (_≈_ : A → A → Type e) (rel : Rel₃ A) ε : Type (a ⊔ e ⊔ (s ₊)) where
  open Rel₃ rel

  field
    ⦃ isPositive ⦄ : IsPositive s _≈_ rel

  open IsPositive isPositive

  field
    ε-least   : ∀ {Φ} → ε ≤ₐ Φ
    ε-split   : Positive rel ε

  non-negativeₗ : ∀ {x y} → x ∙ y ≣ ε → ¬ (x ≢ ε)
  non-negativeₗ σ p with ε-split σ
  ... | eq = ex-falso (p (ap fst eq))

  non-negativeᵣ : ∀ {x y} → x ∙ y ≣ ε → ¬ (y ≢ ε)
  non-negativeᵣ σ p with ε-split σ
  ... | eq = ex-falso (p (ap snd eq))

```
