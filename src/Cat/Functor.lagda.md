Lane Biocini
July 2026

Functors between `Cat.Type` categories.

A functor maps objects and morphisms, preserving composition and
neutrality. Identity preservation is derived: `hmap idn` is neutral
(preserved) and idempotent (from comp preservation + `idem`), so it
equals `idn` by `idempotent-neutral→idn`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Functor where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base

open import Cat.Type
open import Cat.Base
open import Cat.Morphism

record functor
  {o h o' h'}
  (C : category o h) (D : category o' h')
  : Type (o ⊔ h ⊔ o' ⊔ h')
  where
  no-eta-equality
  private
    module Cs = category C
    module Ds = category D
    module Ct = theory C
    module Dt = theory D
    module Cm = morphism C
    module Dm = morphism D

  field
    map  : Cs.ob → Ds.ob
    hmap : ∀ {x y}
      → Cs.hom x y → Ds.hom (map x) (map y)
    preserves-comp
      : ∀ {x y z} (f : Cs.hom x y) (g : Cs.hom y z)
      → hmap (f Ct.⨾ g) ≡ hmap f Dt.⨾ hmap g
    preserves-neutral
      : ∀ {x y} {f : Cs.hom x y}
      → Cm.is-neutral f → Dm.is-neutral (hmap f)

  hmap-idn : ∀ {x} → hmap (Cs.idn x) ≡ Ds.idn (map x)
  hmap-idn {x} = Dm.idempotent-neutral→idn
    (preserves-neutral Cm.idn-is-neutral)
    (sym (preserves-comp (Cs.idn x) (Cs.idn x)) ∙ ap hmap Ct.idem)

{-# INLINE functor.constructor #-}
```

The identity functor maps everything to itself.

```agda
id-functor
  : ∀ {o h} (C : category o h) → functor C C
id-functor C .functor.map x = x
id-functor C .functor.hmap f = f
id-functor C .functor.preserves-comp _ _ = refl
id-functor C .functor.preserves-neutral n = n
```

Functor composition maps objects and morphisms sequentially. Identity
preservation chains through both functors; composition preservation
uses `preserves-comp` of each functor plus `ap` to push the inner
functor's equation through the outer.

```agda
_∘F_
  : ∀ {o₁ h₁ o₂ h₂ o₃ h₃}
    {C : category o₁ h₁}
    {D : category o₂ h₂}
    {E : category o₃ h₃}
  → functor D E → functor C D → functor C E
_∘F_ {C = C} {D} {E} G F = FGF where
  module F = functor F
  module G = functor G

  FGF : functor C E
  FGF .functor.map x = G.map (F.map x)
  FGF .functor.hmap f = G.hmap (F.hmap f)
  FGF .functor.preserves-comp f g =
    ap G.hmap (F.preserves-comp f g)
    ∙ G.preserves-comp (F.hmap f) (F.hmap g)
  FGF .functor.preserves-neutral n = G.preserves-neutral (F.preserves-neutral n)

infixr 30 _∘F_
```
