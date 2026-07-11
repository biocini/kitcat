Pointed types: types equipped with a distinguished basepoint.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Pointed where

open import Core.Type
open import Core.Data.Sigma.Type

Type* : ∀ u → Type (u ₊)
Type* u = Σ A ∶ Type u , A

instance
  Underlying-Pointed : ∀ {u} → Underlying (Type* u)
  Underlying-Pointed {u} .Underlying.ℓ-underlying = u
  Underlying-Pointed .Underlying.⌞_⌟ A = A .fst

```