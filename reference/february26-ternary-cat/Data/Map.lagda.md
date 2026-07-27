Lane Biocini
February 2025

Functors between magmoids, parameterized by source and target.

The primitive field `yon-natural` says that `hmap` commutes with the
Yoneda action: applying `hmap` then acting by `yon` in the codomain
equals acting by `yon` in the domain then applying `hmap`. Since
composition is `f ⨾ g = yon g _ f`, preservation of composition
falls out as `preserves-comp f g = yon-natural g f`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}


open import Cat.Data.Magmoid
module Cat.Data.Map (M N : magmoids) where

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
    yon-natural : ∀ {x y w}
      (f : C.hom x y) (k : C.hom w x)
      → D.yon (hmap f) (map w) (hmap k)
        ≡ hmap (C.yon f w k)

  preserves-comp
    : ∀ {x y z}
      (f : C.hom x y) (g : C.hom y z)
    → D._⨾_ (hmap f) (hmap g) ≡ hmap (C._⨾_ f g)
  preserves-comp f g = yon-natural g f

{-# INLINE functor.constructor #-}

