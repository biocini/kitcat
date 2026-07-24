Lane Biocini
February 2025

Magmoids and the structures we can characterize within them.

We compile all the definitions into a module meant to instantiate uniform definitions
for any category-like (i.e. magmoidal) structure; we also even have the machinery
for heteromorphisms between structures that only agree in being magmoidal,
see the definitions for functor, adjunctions, nat-trans, etc.

FIXES NEEDED TODO

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Depreciated.Magmoid.Magmoid
import Cat.Depreciated.Magmoid.Base as M
import Cat.Depreciated.Magmoid.Neutral as N

module Cat.Depreciated.Magmoid.Coh (M : magmoids) (assoc : M.associativity M) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel.Base
open import Core.Kan
open import Core.Transport.Base
open import Core.Equiv.Base

open M M hiding (assoc)
open N M

has-pentagon : Type (o ⊔ h)
has-pentagon
  = ∀ {w x y z a} (f : hom w x) (g : hom x y) (k : hom y z) (l : hom z a)
  → pentagon f g k l (assoc g k l) (assoc f (g ⨾ k) l) (assoc f g k)
             (assoc f g (k ⨾ l)) (assoc (f ⨾ g) k l)

module 2-cat (units : ∀ x → unital x) where
  -- has-triangle : Type (o ⊔ h)
  -- has-triangle
  --   = ∀ {x y z} (f : hom x y) (g : hom y z) → triangle f g (assoc f (units y .fst) g)

  -- record is-2-coherent : Type (o ⊔ h) where
  --   no-eta-equality
  --   field
  --     tri : has-triangle
  --     pen : has-pentagon
