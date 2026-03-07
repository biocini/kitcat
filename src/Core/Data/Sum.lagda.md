Disjoint union (coproduct): type, operations, and properties.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Sum where

open import Core.Type
open import Core.Data.Sum.Type public

module ⊎ where
  open import Core.Data.Sum.Base public
  open import Core.Data.Sum.Properties public

  module impl where
    open import Core.Data.Sum.Impl.Trunc public

```
