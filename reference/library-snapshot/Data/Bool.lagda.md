```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Bool where

open import Core.Type
open import Core.Data.Bool public

-- Logical operations
xor : Bool → Bool → Bool
xor ff ff = ff
xor ff tt = tt
xor tt ff = tt
xor tt tt = ff
{-# INLINE xor #-}

implies : Bool → Bool → Bool
implies ff _ = tt
implies tt b = b
{-# INLINE implies #-}

nand : Bool → Bool → Bool
nand a b = Bool.not (a && b)
{-# INLINE nand #-}

nor : Bool → Bool → Bool
nor a b = Bool.not (Bool.or a b)
{-# INLINE nor #-}

-- Eliminator
bool-elim : ∀ {u} {@0 P : Bool → Type u} → P tt → P ff → (b : Bool) → P b
bool-elim t f tt = t
bool-elim t f ff = f
{-# INLINE bool-elim #-}

-- Recursion principle
bool-rec : ∀ {u} {A : Type u} → A → A → Bool → A
bool-rec t f tt = t
bool-rec t f ff = f
{-# INLINE bool-rec #-}

-- Decidable equality
_==_ : Bool → Bool → Bool
ff == ff = tt
ff == tt = ff
tt == ff = ff
tt == tt = tt
{-# INLINE _==_ #-}

_≠_ : Bool → Bool → Bool
a ≠ b = Bool.not (a == b)
{-# INLINE _≠_ #-}

```