Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures/Crosssplit.agda`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures.Crosssplit where

open import Core.Type using (Type; Level; _⊔_)
open import Core.Data.Sigma using (Sigma; _,_; fst; snd; _×_)
open import Lib.Ternary.Core
open import Lib.Ternary.Structures.PartialSemigroup

module _ {a} {A : Type a} (r₁ r₂ : Rel₃ A) where
  open Rel₃ r₁ using () renaming (_∙_≣_ to _∙₁_≣_)
  open Rel₃ r₂ using () renaming (_∙_≣_ to _∙₂_≣_)

  CrossSplit : Type a
  CrossSplit = ∀ {a b c d z} →
    a ∙₁ b ≣ z → c ∙₂ d ≣ z →
    Sigma (A × A × A × A) (λ frags →
      let ac , ad , bc , bd = frags
      in ac ∙₂ ad ≣ a × bc ∙₂ bd ≣ b × ac ∙₁ bc ≣ c × ad ∙₁ bd ≣ d)

  Uncross : Type a
  Uncross = ∀ {a b c d ab cd ac bd}
    → a ∙₁ b ≣ ab
    → c ∙₁ d ≣ cd
    → a ∙₂ c ≣ ac
    → b ∙₂ d ≣ bd
    → Sigma A (λ abcd →
        ab ∙₂ cd ≣ abcd
        × ac ∙₁ bd ≣ abcd)

module _ {a} {A : Type a} {r₁ r₂ : Rel₃ A} where

  crossover : CrossSplit r₁ r₂ → CrossSplit r₂ r₁
  crossover f σ₁ σ₂ with f σ₂ σ₁
  ... | _ , τ₁ , τ₂ , τ₃ , τ₄ = _ , τ₃ , τ₄ , τ₁ , τ₂

  uncrossover : Uncross r₁ r₂ → Uncross r₂ r₁
  uncrossover f σ₁ σ₂ σ₃ σ₄ with f σ₃ σ₄ σ₁ σ₂
  ... | _ , τ₁ , τ₂ = _ , τ₂ , τ₁

record IsCrosssplittable {a} {A : Type a} {e}
  (_≈_ : A → A → Type e) (rel : Rel₃ A) : Type (a ⊔ e) where
  open Rel₃ rel

  field
    cross   : CrossSplit rel rel
    uncross : Uncross rel rel

```
