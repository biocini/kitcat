Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Construct/Function.agda`.

The pointwise function space: separation on functions into a resource is
pointwise separation of the codomain.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Construct.Function where

open import Core.Type using (Type; Level; _⊔_; _₊; 0ℓ)
open import Core.Data.Sigma using (fst; snd; _,_)
open import Lib.Relation.Unary
open import Lib.Relation.Binary
open import Lib.Ternary.Core
open import Lib.Ternary.Structures
open import Lib.Ternary.Structures.Syntax
open import Lib.Ternary.Respect.Propositional

module _ {a b} {A : Type a} {B : Type b} ⦃ rb : Rel₃ B ⦄ where

  private
    F = A → B

  instance →-rel : Rel₃ F
  Rel₃._∙_≣_ →-rel f g h = ∀ x → f x ∙ g x ≣ h x

  module Pointwise {e} (_≈_ : B → B → Type e) where

    _≈→_ : F → F → Type (a ⊔ e)
    f ≈→ g = ∀ x → f x ≈ g x

    instance ≈→-isEquivalence : ⦃ _ : IsEquivalence _≈_ ⦄ → IsEquivalence _≈→_
    IsEquivalence.refl  ≈→-isEquivalence _ = refl
    IsEquivalence.sym   ≈→-isEquivalence eq x = sym (eq x)
    IsEquivalence.trans ≈→-isEquivalence eq₁ eq₂ x = trans (eq₁ x) (eq₂ x)

  module _ {e} {_≈_ : B → B → Type e} ⦃ sgb : IsPartialSemigroup _≈_ rb ⦄ where
    open Pointwise _≈_

    instance →-semigroup : IsPartialSemigroup _≈→_ →-rel
    IsPartialSemigroup.≈-equivalence →-semigroup = ≈→-isEquivalence

    Respect.coe (IsPartialSemigroup.∙-respects-≈ →-semigroup) eq σ x = coe (eq x) (σ x)
    Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ →-semigroup) eq σ x = coe (eq x) (σ x)
    Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ →-semigroup) eq σ x = coe (eq x) (σ x)

    IsPartialSemigroup.∙-assocᵣ →-semigroup σ₁ σ₂ =
      _ , (λ x → fst (snd (∙-assocᵣ (σ₁ x) (σ₂ x))))
        , (λ x → snd (snd (∙-assocᵣ (σ₁ x) (σ₂ x))))
    IsPartialSemigroup.∙-assocₗ →-semigroup σ₁ σ₂ =
      _ , (λ x → fst (snd (∙-assocₗ (σ₁ x) (σ₂ x))))
        , (λ x → snd (snd (∙-assocₗ (σ₁ x) (σ₂ x))))

  module _ ⦃ cb : IsCommutative rb ⦄ where

    instance →-commutative : IsCommutative →-rel
    IsCommutative.∙-comm →-commutative σ₁ x = ∙-comm (σ₁ x)

  module _ {e} {_≈_ : B → B → Type e} {u} ⦃ cb : IsPartialMonoid _≈_ rb u ⦄ where
    open Pointwise _≈_
    open Emptiness emptiness

    instance →-empty : Emptiness {A = F} (λ _ → u)
    →-empty = record {}

    instance →-monoid : IsPartialMonoid _≈→_ →-rel (λ _ → u)
    IsPartialMonoid.isSemigroup →-monoid = →-semigroup
    IsPartialMonoid.emptiness →-monoid = →-empty
    IsPartialMonoid.∙-idˡ →-monoid x = ∙-idˡ
    IsPartialMonoid.∙-idʳ →-monoid x = ∙-idʳ
    IsPartialMonoid.∙-id⁻ˡ →-monoid σ x = ∙-id⁻ˡ (σ x)
    IsPartialMonoid.∙-id⁻ʳ →-monoid σ x = ∙-id⁻ʳ (σ x)

```
