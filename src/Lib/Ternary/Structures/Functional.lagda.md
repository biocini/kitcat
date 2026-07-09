Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures/Functional.agda`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures.Functional where

open import Core.Type using (Type; Level; _⊔_)
open import Lib.Ternary.Core using (Rel₃; Functional)

record IsFunctional {a} {A : Type a} {e}
  (_≈_ : A → A → Type e) (rel : Rel₃ A) : Type (a ⊔ e) where
  open Rel₃ rel
  field
    functional : Functional _≈_ rel

```
