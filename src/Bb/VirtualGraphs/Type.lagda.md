The minimal virtual-graph carrier: a graph and a representability
condition, nothing else.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Type where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
```

A term is an edge into an object, a coterm an edge out of it, and an
argument pairs one of each. The conclusion an argument names is the
edge between the two far endpoints; a judgment answers that name for
every argument. `reflect` is the representability condition: every
edge already answers every judgment it could be asked to settle.

```agda
record virtual-graph o h : Type₊ (o ⊔ h) where
  field
    ob : Type o
    hom : ob → ob → Type h

  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v

  argument : ob → ob → Type (o ⊔ h)
  argument x y = term x × coterm y

  conclusion : ∀ {x y} → argument x y → Type h
  conclusion γ = hom (γ .fst .fst) (γ .snd .fst)

  judgment : ob → ob → Type (o ⊔ h)
  judgment x y = (γ : argument x y) → conclusion γ

  field
    reflect : ∀ {x y} → hom x y → judgment x y
```
