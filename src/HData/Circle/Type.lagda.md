The circle as a higher inductive type: one point, one loop.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Circle.Type where

open import Core.Type
open import Core.Base

data Circle : Type where
  base : Circle
  loop : base ≡ base
```
