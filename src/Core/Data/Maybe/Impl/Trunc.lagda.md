Trunc instance for Maybe.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Maybe.Impl.Trunc where

open import Core.Type
open import Core.Data.Nat.Type using (Nat; S)
open import Core.Trait.Trunc

open import Agda.Builtin.Maybe
open import Core.Data.Maybe.Properties using (Maybe-is-hlevel)

instance
  Trunc-Maybe
    : ∀ {u} {A : Type u} {n}
    → ⦃ Trunc A (S (S n)) ⦄
    → Trunc (Maybe A) (S (S n))
  Trunc-Maybe {n = n} .has-trunc =
    Maybe-is-hlevel n (trunc (S (S n)))

```
