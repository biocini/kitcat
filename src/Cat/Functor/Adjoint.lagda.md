Lane Biocini
July 2026

Adjunctions between functors of `Cat.Type` categories.

An adjunction `F ⊣ G` between categories `C` and `D` consists of an
equivalence `D.hom (F x) y ≃ C.hom x (G y)` natural in both variables.
The adjunct and coadjunct are the forward and inverse directions.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Functor.Adjoint where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Equiv.Base using (_≃_; Equiv)

open import Cat.Type
open import Cat.Base
open import Cat.Functor

record _⊣_
  {o h o' h'}
  {C : category o h} {D : category o' h'}
  (F : functor C D) (G : functor D C)
  : Type (o ⊔ h ⊔ o' ⊔ h')
  where
  no-eta-equality
  private
    module Cs = category C
    module Ds = category D
    module Ct = theory C
    module Dt = theory D
    module F = functor F
    module G = functor G

  field
    hom-equiv
      : ∀ x y
      → Ds.hom (F.map x) y ≃ Cs.hom x (G.map y)

  adjunct : ∀ {x y}
    → Ds.hom (F.map x) y → Cs.hom x (G.map y)
  adjunct {x} {y} = Equiv.fwd (hom-equiv x y)

  coadjunct : ∀ {x y}
    → Cs.hom x (G.map y) → Ds.hom (F.map x) y
  coadjunct {x} {y} = Equiv.inv (hom-equiv x y)

  field
    natural-dom
      : ∀ {x x' y} (f : Cs.hom x' x) (g : Ds.hom (F.map x) y)
      → adjunct (F.hmap f Dt.⨾ g) ≡ f Ct.⨾ adjunct g
    natural-cod
      : ∀ {x y y'} (g : Ds.hom (F.map x) y) (k : Ds.hom y y')
      → adjunct (g Dt.⨾ k) ≡ adjunct g Ct.⨾ G.hmap k

{-# INLINE _⊣_.constructor #-}

is-left-adjoint
  : ∀ {o h o' h'}
    {C : category o h} {D : category o' h'}
  → functor C D → Type _
is-left-adjoint F =
  Σ G ∶ functor _ _ , F ⊣ G

is-right-adjoint
  : ∀ {o h o' h'}
    {C : category o h} {D : category o' h'}
  → functor D C → Type _
is-right-adjoint G =
  Σ F ∶ functor _ _ , F ⊣ G
```
