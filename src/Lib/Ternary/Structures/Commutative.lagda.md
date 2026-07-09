Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures/Commutative.agda`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures.Commutative where

open import Core.Type using (Type; Level; _⊔_; _∘_)
open import Core.Data.Sigma using (Sigma; _,_; fst; snd; _×_; Σ-syntax)
open import Lib.Relation.Unary hiding (_∪_; _∩_; ∅)
open import Lib.Relation.Binary hiding (refl; sym; trans)
open import Lib.Ternary.Core
open import Lib.Ternary.Structures.PartialSemigroup
open import Lib.Ternary.Structures.PartialMonoid
open import Lib.Ternary.Structures.Idempotent

record IsCommutative {a} {A : Type a} (rel : Rel₃ A) : Type a where
  open Rel₃ rel

  field
    ∙-comm            : Commutative rel

  -- pairs commute
  module _ {p q} {P : Pred A p} {Q : Pred A q} where
    ✴-swap : ∀[ (P ✴ Q) ⇒ (Q ✴ P) ]
    ✴-swap (px ∙⟨ σ ⟩ qx) = qx ∙⟨ ∙-comm σ ⟩ px

module CommutativeSemigroupOps
  {a} {A : Type a} {e} {_≈_ : A → A → Type e} {rel : Rel₃ A}
  ⦃ pcsg : IsPartialSemigroup _≈_ rel ⦄
  ⦃ comm : IsCommutative rel ⦄ where

  open Rel₃ rel
  open IsPartialSemigroup ⦃ ... ⦄
  open IsCommutative ⦃ ... ⦄
  open IsIdempotent ⦃ ... ⦄

  module _ where

    resplit : ∀ {a b c d ab cd abcd} →
              a ∙ b ≣ ab → c ∙ d ≣ cd → ab ∙ cd ≣ abcd →
              ∃₂ λ ac bd → a ∙ c ≣ ac × b ∙ d ≣ bd × ac ∙ bd ≣ abcd
    resplit σ₁ σ₂ σ     with ∙-assocᵣ σ₁ σ
    ... | bcd , σ₃ , σ₄ with ∙-assocₗ σ₄ (∙-comm σ₂)
    ... | bd  , σ₅ , σ₆ with ∙-assocₗ σ₃ σ₆
    ... | abd , σ₇ , σ₈ with ∙-assocₗ (∙-comm σ₈) σ₇
    ... | ac  , τ  , τ' = _ , _ , ∙-comm τ , σ₅ , τ'

  module _ {p q p' q'}
    {P : Pred A p} {Q : Pred A q} {P' : Pred A p'} {Q' : Pred A q'} where

    both : ∀[ (P ─✴ P') ✴ (Q ─✴ Q') ⇒ P ✴ Q ─✴ P' ✴ Q' ]
    both (f ∙⟨ σ₁ ⟩ g) ⟨ σ₃ ⟩ (px ∙⟨ σ₂ ⟩ qx) with resplit σ₁ σ₂ σ₃
    ... | _ , _ , σ₄ , σ₅ , σ₆ = (f ⟨ σ₄ ⟩ px) ∙⟨ σ₆ ⟩ (g ⟨ σ₅ ⟩ qx)

  module _ {a b c bc abc} where
    ∙-rotateₗ : a ∙ bc ≣ abc → b ∙ c ≣ bc → ∃ λ ca → b ∙ ca ≣ abc × c ∙ a ≣ ca
    ∙-rotateₗ σ₁ σ₂ with ∙-assocᵣ σ₂ (∙-comm σ₁)
    ... | _ , σ₃ , σ₄ = _ , σ₃ , σ₄

    ∙-rotateᵣ : a ∙ bc ≣ abc → b ∙ c ≣ bc → ∃ λ ab → c ∙ ab ≣ abc × a ∙ b ≣ ab
    ∙-rotateᵣ σ₁ σ₂ with ∙-assocₗ σ₁ σ₂
    ... | _ , σ₃ , σ₄ = _ , ∙-comm σ₄ , σ₃

  -- pairs rotate and reassociate
  module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where
    ✴-rotateᵣ : ∀[ P ✴ Q ✴ R ⇒ R ✴ P ✴ Q ]
    ✴-rotateᵣ (p ∙⟨ σ₁ ⟩ (q ∙⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ∙-rotateᵣ σ₁ σ₂ in
      r ∙⟨ σ₃ ⟩ p ∙⟨ σ₄ ⟩ q

    ✴-rotateₗ : ∀[ P ✴ (Q ✴ R) ⇒ Q ✴ R ✴ P ]
    ✴-rotateₗ (p ∙⟨ σ₁ ⟩ (q ∙⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ∙-rotateₗ σ₁ σ₂ in
      q ∙⟨ σ₃ ⟩ r ∙⟨ σ₄ ⟩ p

{- Combined structures for abstract usage -}
module _ where

  record IsCommutativeSemigroup {a} {A : Type a} {e} (_≈_ : A → A → Type e) (rel : Rel₃ A) : Type (a ⊔ e) where
    no-eta-equality
    instance constructor isCommSemigroup
    field
      ⦃ isSemigroup ⦄   : IsPartialSemigroup _≈_ rel
      ⦃ isCommutative ⦄ : IsCommutative rel
  {-# INLINE IsCommutativeSemigroup.constructor #-}

  record IsCommutativeMonoid {a} {A : Type a} {e} (_≈_ : A → A → Type e) (rel : Rel₃ A) u : Type (a ⊔ e) where
    no-eta-equality
    instance constructor isCommMonoid
    field
      ⦃ isMonoid ⦄      : IsPartialMonoid _≈_ rel u
      ⦃ isCommutative ⦄ : IsCommutative rel
  {-# INLINE IsCommutativeMonoid.constructor #-}

{- Some smart constructors for semigroups and monoids -}
module _ where

  -- left biased
  record IsPartialSemigroupˡ {a} {A : Type a} {e} (_≈_ : A → A → Type e) (rel : Rel₃ A) : Type (a ⊔ e) where
    no-eta-equality
    open Rel₃ rel
    open IsCommutative ⦃ ... ⦄
    field
      ⦃ ≈-equivalence ⦄  : IsEquivalence _≈_
      ⦃ ∙-respects-≈ ⦄   : ∀ {Φ₁ Φ₂} → Respect _≈_ (Φ₁ ∙ Φ₂)
      ⦃ ∙-respects-≈ˡ ⦄  : ∀ {Φ₂ Φ}  → Respect _≈_ (_∙ Φ₂ ≣ Φ)

      ⦃ comm ⦄           : IsCommutative rel
      assocᵣ             : ∀ {a b ab c abc} → a ∙ b ≣ ab → ab ∙ c ≣ abc
                         → ∃ λ bc → a ∙ bc ≣ abc × b ∙ c ≣ bc

    instance semigroupˡ : IsPartialSemigroup _≈_ rel
    Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ semigroupˡ) eq = ∙-comm ∘ coe eq ∘ ∙-comm
    IsPartialSemigroup.∙-assocᵣ semigroupˡ = assocᵣ
    IsPartialSemigroup.∙-assocₗ semigroupˡ σ₁ σ₂ =
      let _ , σ₃ , σ₄ = assocᵣ (∙-comm σ₂) (∙-comm σ₁)
      in _ , ∙-comm σ₄ , ∙-comm σ₃
  {-# INLINE IsPartialSemigroupˡ.constructor #-}

  record IsPartialMonoidˡ {a} {A : Type a} {e} (_≈_ : A → A → Type e) (rel : Rel₃ A) (unit : A) : Type (a ⊔ e) where
    no-eta-equality
    open Rel₃ rel
    open IsCommutative ⦃ ... ⦄

    field
      ⦃ isSemigroup ⦄   : IsPartialSemigroup _≈_ rel
      ⦃ isCommutative ⦄ : IsCommutative rel
      ⦃ emptiness ⦄     : Emptiness unit
      identityˡ  : ∀ {Φ} → unit ∙ Φ ≣ Φ
      identity⁻ˡ : ∀ {Φ} → ∀[ unit ∙ Φ ⇒ _≈_ Φ ]

    partialMonoidˡ : IsPartialMonoid _≈_ rel unit
    IsPartialMonoid.∙-idˡ partialMonoidˡ = identityˡ
    IsPartialMonoid.∙-idʳ partialMonoidˡ = ∙-comm identityˡ
    IsPartialMonoid.∙-id⁻ˡ partialMonoidˡ = identity⁻ˡ
    IsPartialMonoid.∙-id⁻ʳ partialMonoidˡ = identity⁻ˡ ∘ ∙-comm
  {-# INLINE IsPartialMonoidˡ.constructor #-}

```
