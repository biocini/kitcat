Integers: type, arithmetic, and properties.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Int where

open import Core.Data.Int.Type public

module Int where
  open import Core.Data.Int.Base public
  open import Core.Data.Int.Properties public

  module impl where
    open import Core.Data.Int.Impl.Discrete public

```
