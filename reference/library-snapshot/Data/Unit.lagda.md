```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Unit where

open import Core.Type public
  using (⊤; tt; Unit)
open import Core.Type
  using (Type; Level; id)

open Core.Type.Unit public
  renaming (ind to ⊤-elim)

-- Recursion principle
⊤-rec : ∀ {u} {A : Type u} → A → ⊤ → A
⊤-rec a tt = a
{-# INLINE ⊤-rec #-}

-- Unit is terminal: unique morphism from any type
terminal : ∀ {u} {A : Type u} → A → ⊤
terminal _ = tt
{-# INLINE terminal #-}

-- Absorbing element for products
absorb-× : ∀ {u} {A : Type u} → A → ⊤ → A
absorb-× a _ = a
{-# INLINE absorb-× #-}

```