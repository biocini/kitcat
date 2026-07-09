Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures/PartialMonoid.agda`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures.PartialMonoid where

open import Core.Type using (Type; Level; _⊔_; 0ℓ; _∘_)
open import Core.Base using (_≡_; refl; sym)
open import Core.Transport.J using (subst)
open import Core.Data.Sigma using (Sigma; _,_; fst; snd; _×_; Σ-syntax)
open import Lib.Relation.Unary hiding (_∪_; _∩_; ∅)
open import Lib.Relation.Binary hiding (refl; sym; trans)
open import Lib.Ternary.Core
open import Lib.Ternary.Structures.PartialSemigroup

-- Abstracted from the monoid instance to accommodate unambiguous use of ε/Emp
-- in contexts with multiple monoidal relations on a single carrier.
record Emptiness {a} {A : Type a} (unit : A) : Type 0ℓ where
  ε : A
  ε = unit

  Emp : Pred A a
  Emp = ｛ ε ｝

  infix 10 ε[_]
  ε[_] : ∀ {ℓ} → Pred A ℓ → Type ℓ
  ε[ P ] = P ε

  data Empty {p} (P : Type p) : Pred A (a ⊔ p) where
    emp : P → Empty P ε

open Emptiness ⦃ ... ⦄ public

record IsPartialMonoid {a} {A : Type a} {e}
  (_≈_ : A → A → Type e) (rel : Rel₃ A) (unit : A) : Type (a ⊔ e) where
  open Rel₃ rel
  open IsPartialSemigroup ⦃ ... ⦄
  module Eq = IsEquivalence ⦃ ... ⦄

  field
    overlap {{ emptiness }}   : Emptiness unit
    overlap {{ isSemigroup }} : IsPartialSemigroup _≈_ rel

    ∙-idˡ    : LeftIdentity rel ε
    ∙-idʳ    : RightIdentity rel ε

    ∙-id⁻ˡ   : LeftIdentity⁻ _≈_ rel ε
    ∙-id⁻ʳ   : RightIdentity⁻ _≈_ rel ε

  Emp′ = λ x → x ≈ ε

  ε∙ε′ : ∀[ ε ∙ ε ⇒ Emp′ ]
  ε∙ε′ p = Eq.sym (∙-id⁻ˡ p)

  ε∙ε : ⦃ uniq : IsUnique _≈_ ε ⦄ → ∀[ ε ∙ ε ⇒ Emp ]
  ε∙ε ⦃ uniq ⦄ p = unique ⦃ uniq ⦄ (∙-id⁻ˡ p)

  ∙-id⁺ˡ : ∀ {Φ} → ε ≈ Φ → ∃ λ Φ₂ → ε ∙ Φ₂ ≣ Φ
  ∙-id⁺ˡ eq = _ , coe eq ∙-idˡ

  ∙-id⁺ʳ : ∀ {Φ} → ε ≈ Φ → ∃ λ Φ₂ → Φ₂ ∙ ε ≣ Φ
  ∙-id⁺ʳ eq = _ , coe eq ∙-idʳ

  module _ {p} {P : Pred A p} ⦃ _ : Respect _≈_ P ⦄ where
    ✴-id⁻ʳ : ∀[ P ✴ Emp ⇒ P ]
    ✴-id⁻ʳ (px ∙⟨ σ ⟩ qx) =
      coe (∙-id⁻ʳ (subst (λ z → _ ∙ z ≣ _) (sym qx) σ)) px

    ✴-id⁻ˡ : ∀[ Emp ✴ P ⇒ P ]
    ✴-id⁻ˡ (qx ∙⟨ σ ⟩ px) =
      coe (∙-id⁻ˡ (subst (λ z → z ∙ _ ≣ _) (sym qx) σ)) px

  module _ {p} {P : Pred A p} where
    ✴-idʳ : ∀[ P ⇒ P ✴ Emp ]
    ✴-idʳ px = px ∙⟨ ∙-idʳ ⟩ refl

    ✴-idˡ : ∀[ P ⇒ Emp ✴ P ]
    ✴-idˡ px = refl ∙⟨ ∙-idˡ ⟩ px

  module _ {p q} {P : Pred A p} {Q : Pred A q} ⦃ _ : Respect _≈_ Q ⦄ where
    arrow : ∀[ P ⇒ Q ] → ε[ P ─✴ Q ]
    arrow f ⟨ σ ⟩ px = coe (∙-id⁻ˡ σ) (f px)

  {- A free preorder -}
  ≤-reflexive : ∀ {Φ₁ Φ₂} → Φ₁ ≡ Φ₂ → Φ₁ ≤ Φ₂
  ≤-reflexive eq = ε , subst (λ w → _ ∙ ε ≣ w) eq ∙-idʳ

  ≤-refl : ∀ {Φ} → Φ ≤ Φ
  ≤-refl = ε , ∙-idʳ

  ε-minimal : ∀ {Φ} → ε ≤ Φ
  ε-minimal = _ , ∙-idˡ

```
