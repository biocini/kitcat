Discrete instance for Int.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Int.Impl.Discrete where

open import Core.Data.Int.Type
open import Core.Trait.Eq
import Core.Data.Int.Properties as Int

instance
  Discrete-Int : Discrete Int
  Discrete-Int .Discrete._≟_ = Int.DecEq-Int

```
