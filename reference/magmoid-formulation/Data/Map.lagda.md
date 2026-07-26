Lane Biocini
February 2025

Magmoids and the structures we can characterize within them.

We compile all the definitions into a module meant to instantiate uniform definitions
for any category-like (i.e. magmoidal) structure; we also even have the machinery
for heteromorphisms between structures that only agree in being magmoidal,
see the definitions for functor, adjunctions, nat-trans, etc.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}


open import Cat.Data.Magmoid
module Cat.Data.Map (M N : Magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv

import Cat.Data.Base

private
  module C = Cat.Data.Base M
  module D = Cat.Data.Base N

record functor : Type (C.o ⊔ D.o ⊔ C.h ⊔ D.h) where
  no-eta-equality

  field
    map  : C.ob → D.ob
    hmap : ∀ {x y}
      → C.hom x y → D.hom (map x) (map y)
    preserves-iso : ∀ {x y} (f : C.hom x y)
      → C.is-neutral f → D.is-neutral (hmap f)
    preserves-comp : ∀ {x y z}
      (f : C.hom x y) (g : C.hom y z)
      → (D._⨾_ (hmap f) (hmap g)) ≡ (hmap (C._⨾_ f g))

{-# INLINE functor.constructor #-}

