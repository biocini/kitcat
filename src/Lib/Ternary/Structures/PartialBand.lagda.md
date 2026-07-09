Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures/PartialBand.agda`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures.PartialBand where

open import Core.Type using (Type; Level; _⊔_; _₊; 0ℓ)
open import Lib.Relation.Unary using (U)
open import Lib.Relation.Binary hiding (refl; sym; trans)
open import Lib.Ternary.Core using (Rel₃)
open import Lib.Ternary.Structures.Idempotent
open import Lib.Ternary.Structures.PartialSemigroup

record IsBand {a} {A : Type a} {e}
  (_≈_ : A → A → Type e) (rel : Rel₃ A) : Type (0ℓ ₊ ⊔ a ⊔ e) where
  open Rel₃ rel

  field
    ⦃ isSemigroup ⦄  : IsPartialSemigroup _≈_ rel
    ⦃ isIdempotent ⦄ : IsIdempotent U rel

```
