Trunc instance for Bool.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Bool.Impl.Trunc where

open import Core.Data.Nat.Type using (Nat; S)
open import Core.Data.Bool.Type
open import Core.Data.Bool.Properties using (set)
open import Core.Trait.Trunc

instance
  Trunc-Bool : ∀ {k} → Trunc Bool (S (S k))
  Trunc-Bool = set-trunc set

{-# OVERLAPS Trunc-Bool #-}

```
