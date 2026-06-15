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
module Cat.Data.Nat (M N : magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel.Base
open import Core.Kan
open import Core.Transport.Base
open import Core.Equiv.Base


open import Cat.Data.Map

import Cat.Data.Base
import Cat.Data.Neutral as Neu

private
  module C = Cat.Data.Base M
  module D = Cat.Data.Base N


record _⇒_ (F G : functor M N) : Type (C.o ⊔ C.h ⊔ D.o ⊔ D.h) where
  no-eta-equality
  private
    module F = functor F
    module G = functor G

  field
    component : ∀ x → D.hom (F.map x) (G.map x)
    natural
      : ∀ {x y} (f : C.hom x y)
      → (D._⨾_ (F.hmap f) (component y)) ≡ (D._⨾_ (component x) (G.hmap f))

{-# INLINE _⇒_.constructor #-}

open _⇒_ public

nat-trans : functor M N → functor M N → Type (C.o ⊔ D.o ⊔ C.h ⊔ D.h)
nat-trans = _⇒_

is-nat-iso : {F G : functor M N} → nat-trans F G → Type (C.o ⊔ D.o ⊔ D.h)
is-nat-iso alpha = ∀ x → D.is-neutral (component alpha x)

nat-iso : (F G : functor M N) → Type (C.o ⊔ D.o ⊔ C.h ⊔ D.h)
nat-iso F G = Σ α ∶ nat-trans F G , is-nat-iso α

module coh (assoc : D.associativity) {F G H : functor M N} where
  private
    module F = functor F
    module G = functor G
    module H = functor H

  nat-trans-comp : nat-trans F G → nat-trans G H → nat-trans F H
  nat-trans-comp α β .component x = D._⨾_ (component α x) (component β x)
  nat-trans-comp α β .natural {x} {y} f =
    assoc (F.hmap f) (component α y) (component β y)
    ∙ ap (λ z → D._⨾_ z (component β y)) (natural α f)
    ∙ sym (assoc (component α x) (G.hmap f) (component β y))
    ∙ ap (D._⨾_ (component α x)) (natural β f)
    ∙ assoc (component α x) (component β x) (H.hmap f)

  comp-nat-iso : (α : nat-trans F G) (β : nat-trans G H)
               → is-nat-iso α → is-nat-iso β → is-nat-iso (nat-trans-comp α β)
  comp-nat-iso α β α-iso β-iso x
    = comp-is-neutral
        ((λ {w} f → assoc f (component α x) (component β x))
          , (λ {z} → assoc (component α x) (component β x)))
        (α-iso x) (β-iso x)
        where open Neu.composable N
