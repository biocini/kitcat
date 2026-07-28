Lane Biocini
July 2026

Natural transformations between functors of
`Bb.CatsWithExplicitInterchange.Type` categories.

A natural transformation between functors `F` and `G` assigns to each
object `x` a component morphism `F x → G x`, such that for any
morphism `f : x → y`, the naturality square commutes:
`F(f) ⨾ η y ≡ η x ⨾ G(f)`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Functor.NatTrans where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Base
open import Bb.CatsWithExplicitInterchange.Morphism
open import Bb.CatsWithExplicitInterchange.Functor

record nat-trans
  {o h o' h'}
  {C : category o h} {D : category o' h'}
  (F G : functor C D)
  : Type (o ⊔ h ⊔ h')
  where
  no-eta-equality
  private
    module C = category C
    module D = category D
    module Dt = theory D
    module F = functor F
    module G = functor G

  field
    component
      : ∀ x → D.hom (F.map x) (G.map x)
    natural
      : ∀ {x y} (f : C.hom x y)
      → F.hmap f Dt.⨾ component y
      ≡ component x Dt.⨾ G.hmap f

{-# INLINE nat-trans.constructor #-}
```

The identity natural transformation has `idn` as every component.
Naturality follows from `unitl` and `unitr`.

```agda
nat-id
  : ∀ {o h o' h'}
    {C : category o h} {D : category o' h'}
    (F : functor C D)
  → nat-trans F F
nat-id {D = D} F = nt where
  module D = category D
  module Dt = theory D
  module F = functor F

  nt : nat-trans F F
  nt .nat-trans.component x = D.idn (F.map x)
  nt .nat-trans.natural f = Dt.unitr (F.hmap f) ∙ sym (Dt.unitl (F.hmap f))
```

Vertical composition of natural transformations composes the
components. Naturality of the composite follows from associativity
and the naturality of each factor.

```agda
nat-comp
  : ∀ {o h o' h'}
    {C : category o h} {D : category o' h'}
    {F G H : functor C D}
  → nat-trans F G → nat-trans G H → nat-trans F H
nat-comp {D = D} {F} {G} {H} α β = αβ where
  module D  = category D
  module Dt = theory D
  module Dm = morphism D
  module F  = functor F
  module G  = functor G
  module H  = functor H
  module α  = nat-trans α
  module β  = nat-trans β

  αβ : nat-trans F H
  αβ .nat-trans.component x = α.component x Dt.⨾ β.component x
  αβ .nat-trans.natural {x} {y} f =
    F.hmap f Dt.⨾ (α.component y Dt.⨾ β.component y)
      ≡⟨ Dt.assoc (F.hmap f)
            (α.component y) (β.component y) ⟩
    (F.hmap f Dt.⨾ α.component y) Dt.⨾ β.component y
      ≡⟨ α.natural f Dm.▹ β.component y ⟩
    (α.component x Dt.⨾ G.hmap f) Dt.⨾ β.component y
      ≡⟨ sym (Dt.assoc (α.component x)
            (G.hmap f) (β.component y)) ⟩
    α.component x Dt.⨾ (G.hmap f Dt.⨾ β.component y)
      ≡⟨ α.component x Dm.◃ β.natural f ⟩
    α.component x Dt.⨾ (β.component x Dt.⨾ H.hmap f)
      ≡⟨ Dt.assoc (α.component x)
            (β.component x) (H.hmap f) ⟩
    (α.component x Dt.⨾ β.component x) Dt.⨾ H.hmap f ∎
```
