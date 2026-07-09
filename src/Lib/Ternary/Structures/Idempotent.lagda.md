Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures/Idempotent.agda`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures.Idempotent where

open import Core.Type using (Type; Level; _⊔_; _₊)
open import Core.Transport.Base using (transport)
open import Lib.Relation.Unary using (Pred; ∀[_]; _⇒_)
open import Lib.Ternary.Core
open import Lib.Ternary.Structures.PartialSemigroup
open import Lib.Ternary.Structures.PartialMonoid

record IsIdempotent {a} {A : Type a} {c}
  (Condition : Pred A c) (rel : Rel₃ A) : Type (a ⊔ (c ₊)) where
  open Rel₃ rel
  field
    ∙-idem    : ∀ {xs : A} → Condition xs → xs ∙ xs ≣ xs

module _ {a} {A : Type a} ⦃ rel : Rel₃ A ⦄ where

  open Rel₃ rel
  open IsIdempotent ⦃ ... ⦄

  idem
    : ∀ {p} {P : Pred A p} ⦃ _ : IsIdempotent P rel ⦄
    → ∀[ P ⇒ P ✴ P ]
  idem px = px ∙⟨ ∙-idem px ⟩ px

module _ {a} {A : Type a} {e} {u} {_≈_ : A → A → Type e} {rel : Rel₃ A}
  ⦃ m : IsPartialMonoid _≈_ rel u ⦄ where

  open Rel₃ rel
  open IsPartialMonoid m

  Emp-idempotent : IsIdempotent Emp rel
  IsIdempotent.∙-idem Emp-idempotent qx =
    transport (λ i → qx i ∙ qx i ≣ qx i) ∙-idˡ

```
