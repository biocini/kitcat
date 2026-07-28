Lane Biocini
February 2025

Magmoids and virtual graphs via the covariant Yoneda embedding.

A magmoid is a type of objects, a family of hom-types, and a covariant
Yoneda embedding `yon` that is an embedding in the HoTT sense.
Composition is derived: `f ⨾ g = yon g _ f`. A virtual graph extends a
magmoid with a contractible fiber witnessing the identity morphism.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Bb.UnitalMagmoids.Magmoid where

open import Core.Function.Embedding using (is-embedding)
open import Core.Data.Sigma using (fst)
open import Core.Base using (is-contr; fiber; center)
open import Core.Type

record magmoid o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
    yon-emb : ∀ {x y} → is-embedding (yon {x} {y})

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = yon g _ f
  infixr 40 _⨾_

  yon-op : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  yon-op f z g = yon g _ f

{-# INLINE magmoid.constructor #-}


record magmoids : Typeω where
  constructor str
  field
    {o h} : Level
    ob  : Type o
    hom : ob → ob → Type h
    yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
    yon-emb : ∀ {x y} → is-embedding (yon {x} {y})

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = yon g _ f
  infixr 40 _⨾_

  yon-op : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  yon-op f z g = yon g _ f

{-# INLINE str #-}


record virtual-graph o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    magm : magmoid o h
  open magmoid magm public
  field
    idn-contr
      : ∀ {x}
      → is-contr
          (fiber yon (λ (_ : ob) → id {A = hom _ x}))
    idn-op-contr
      : ∀ {x}
      → is-contr
          (fiber (yon-op {x} {x}) (λ (_ : ob) → id))

  idn : ∀ {x} → hom x x
  idn = idn-contr .center .fst

{-# INLINE virtual-graph.constructor #-}


record virtual-graphs : Typeω where
  field
    {o h} : Level
    magm : magmoid o h
  open magmoid magm public
  field
    idn-contr
      : ∀ {x}
      → is-contr
          (fiber yon (λ (_ : ob) → id {A = hom _ x}))
    idn-op-contr
      : ∀ {x}
      → is-contr
          (fiber (yon-op {x} {x}) (λ (_ : ob) → id))

  idn : ∀ {x} → hom x x
  idn = idn-contr .center .fst

  to-magmoids : magmoids
  to-magmoids = str ob hom yon yon-emb

{-# INLINE virtual-graphs.constructor #-}
```
