Discrete instance for Fin.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Fin.Impl.Discrete where

open import Core.Data.Nat.Type
open import Core.Data.Fin.Type
open import Core.Trait.Eq using (Discrete)
import Core.Data.Fin.Properties as Fin

private variable
  n : Nat

instance
  Discrete-Fin : Discrete (Fin n)
  Discrete-Fin .Discrete._≟_ = Fin.Fin-discrete

```
