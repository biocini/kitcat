The circle as a higher inductive type, with its rotation family,
multiplication, and winding equivalence.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Circle where

open import Core.Type
open import HData.Circle.Type public hiding (module Circle)

module Circle where
  open HData.Circle.Type.Circle public
  open import HData.Circle.Base public
  open import HData.Circle.Mult public
  open import HData.Circle.Properties public
```
