The join of two types as a higher inductive type.

The join `A ⋆ B` is the space of formal line segments from points
of `A` to points of `B`. This is the standard HIT formulation
following Rijke (Ch 18) and the cubical Agda library.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Join.Type where

open import Core.Type
open import Core.Base

private variable
  u v : Level

data _⋆_ (A : Type u) (B : Type v) : Type (u ⊔ v) where
  inl  : A → A ⋆ B
  inr  : B → A ⋆ B
  push : (a : A) (b : B) → inl a ≡ inr b

infixl 6 _⋆_
```
