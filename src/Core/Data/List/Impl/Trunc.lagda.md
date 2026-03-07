Trunc instance for List.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.List.Impl.Trunc where

open import Core.Type
open import Core.Data.Nat.Type using (Nat; S)
open import Core.Data.List.Type
open import Core.Data.List.Properties using (List-is-hlevel)
open import Core.Trait.Trunc

instance
  Trunc-List
    : ∀ {u} {A : Type u} {n}
    → ⦃ Trunc A (S (S n)) ⦄
    → Trunc (List A) (S (S n))
  Trunc-List {n = n} .has-trunc =
    List-is-hlevel n (trunc (S (S n)))

```
