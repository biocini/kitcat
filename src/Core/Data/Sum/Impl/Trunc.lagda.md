Trunc instance for coproducts.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Sum.Impl.Trunc where

open import Core.Type
open import Core.Data.Nat.Type using (Nat; S)
open import Core.Data.Sum.Type
open import Core.Data.Sum.Properties using (⊎-is-hlevel)
open import Core.Trait.Trunc

instance
  Trunc-⊎
    : ∀ {u v} {A : Type u} {B : Type v} {n}
    → ⦃ Trunc A (S (S n)) ⦄ → ⦃ Trunc B (S (S n)) ⦄
    → Trunc (A ⊎ B) (S (S n))
  Trunc-⊎ {n = n} .has-trunc =
    ⊎-is-hlevel n (trunc (S (S n))) (trunc (S (S n)))

```
