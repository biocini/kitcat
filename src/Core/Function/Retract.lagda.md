Retraction pairs: left and right inverses for function composition.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Function.Retract where

open import Core.Type
open import Core.Base

is-left-inverse
  : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) (g : B → A) → Type v
is-left-inverse f g = ∀ b → f (g b) ≡ b

is-right-inverse
  : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) (g : B → A) → Type u
is-right-inverse f g = ∀ a → g (f a) ≡ a
```
