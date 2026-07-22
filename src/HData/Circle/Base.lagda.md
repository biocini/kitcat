Induction and recursion for the circle. `ind0` eliminates motives
over an erased circle argument.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Circle.Base where

open import Core.Type
open import Core.Base

open import HData.Circle.Type

private variable
  ℓ : Level

ind : (P : Circle → Type ℓ) (b : P base)
    → PathP (λ i → P (loop i)) b b
    → (x : Circle) → P x
ind P b l base = b
ind P b l (loop i) = l i

rec : {X : Type ℓ} (b : X) → b ≡ b → Circle → X
rec b l base = b
rec b l (loop i) = l i

ind0 : (P : @0 Circle → Type ℓ) (b : P base)
     → PathP (λ i → P (loop i)) b b
     → (x : Circle) → P x
ind0 P b l base = b
ind0 P b l (loop i) = l i
```
