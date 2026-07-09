Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Construct/Product.agda`.

The pointwise product of two ternary relations: pairs split componentwise.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Construct.Product where

open import Core.Type using (Type; Level; _⊔_; _₊; 0ℓ)
open import Core.Data.Sigma using (Sigma; _,_; fst; snd; _×_)
open import Lib.Relation.Unary
open import Lib.Relation.Binary
open import Lib.Ternary.Core
open import Lib.Ternary.Structures
open import Lib.Ternary.Structures.Syntax
open import Lib.Ternary.Respect.Propositional

module _ {ℓ₁ ℓ₂} {C₁ : Type ℓ₁} {C₂ : Type ℓ₂} where

  private variable
    e₁ e₂ : Level

  _×-∙_ : Rel₃ C₁ → Rel₃ C₂ → Rel₃ (C₁ × C₂)
  R₁ ×-∙ R₂ = record { _∙_≣_ = split }
    where
      module M₁ = Rel₃ R₁
      module M₂ = Rel₃ R₂
      split : (Φ₁ Φ₂ : C₁ × C₂) → Pred (C₁ × C₂) (ℓ₁ ⊔ ℓ₂)
      split Φ₁ Φ₂ Φ =
        (M₁._∙_≣_ (fst Φ₁) (fst Φ₂) (fst Φ))
        × (M₂._∙_≣_ (snd Φ₁) (snd Φ₂) (snd Φ))

  -- Pointwise equivalence on products.
  Pointwise
    : (C₁ → C₁ → Type e₁) → (C₂ → C₂ → Type e₂)
    → (C₁ × C₂) → (C₁ × C₂) → Type (e₁ ⊔ e₂)
  Pointwise _≈₁_ _≈₂_ a b = (fst a ≈₁ fst b) × (snd a ≈₂ snd b)

  module _ {_≈₁_ : C₁ → C₁ → Type e₁} {_≈₂_ : C₂ → C₂ → Type e₂}
    ⦃ eq₁ : IsEquivalence _≈₁_ ⦄ ⦃ eq₂ : IsEquivalence _≈₂_ ⦄ where

    instance ×-equiv : IsEquivalence (Pointwise _≈₁_ _≈₂_)
    IsEquivalence.refl  ×-equiv = refl , refl
    IsEquivalence.sym   ×-equiv (a , b) = sym a , sym b
    IsEquivalence.trans ×-equiv (a₁ , b₁) (a₂ , b₂) = trans a₁ a₂ , trans b₁ b₂

  module _ ⦃ R₁ : Rel₃ C₁ ⦄ ⦃ R₂ : Rel₃ C₂ ⦄
    {_≈₁_ : C₁ → C₁ → Type e₁} {_≈₂_ : C₂ → C₂ → Type e₂}
    ⦃ s₁ : IsPartialSemigroup _≈₁_ R₁ ⦄ ⦃ s₂ : IsPartialSemigroup _≈₂_ R₂ ⦄ where

    instance ×-isSemigroup : IsPartialSemigroup (Pointwise _≈₁_ _≈₂_) (R₁ ×-∙ R₂)

    Respect.coe (IsPartialSemigroup.∙-respects-≈ ×-isSemigroup) (eq₁ , eq₂) (σ₁ , σ₂) =
      coe eq₁ σ₁ , coe eq₂ σ₂
    Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ ×-isSemigroup) (eq₁ , eq₂) (σ₁ , σ₂) =
      coe eq₁ σ₁ , coe eq₂ σ₂
    Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ ×-isSemigroup) (eq₁ , eq₂) (σ₁ , σ₂) =
      coe eq₁ σ₁ , coe eq₂ σ₂

    IsPartialSemigroup.∙-assocᵣ ×-isSemigroup (l₁ , r₁) (l₂ , r₂) =
      let
        _ , l₃ , l₄ = ∙-assocᵣ l₁ l₂
        _ , r₃ , r₄ = ∙-assocᵣ r₁ r₂
      in _ , (l₃ , r₃) , l₄ , r₄

    IsPartialSemigroup.∙-assocₗ ×-isSemigroup (l₁ , r₁) (l₂ , r₂) =
      let
        _ , l₃ , l₄ = ∙-assocₗ l₁ l₂
        _ , r₃ , r₄ = ∙-assocₗ r₁ r₂
      in _ , (l₃ , r₃) , l₄ , r₄

  module _ ⦃ R₁ : Rel₃ C₁ ⦄ ⦃ R₂ : Rel₃ C₂ ⦄
    ⦃ s₁ : IsCommutative R₁ ⦄ ⦃ s₂ : IsCommutative R₂ ⦄ where

    instance ×-isCommutative : IsCommutative (R₁ ×-∙ R₂)
    IsCommutative.∙-comm ×-isCommutative (fst , snd) = ∙-comm fst , ∙-comm snd

```
