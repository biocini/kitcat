Lane Biocini
February 2026

Functors between categories, instantiated from the generic magmoid
map theory. Includes the identity functor and functor composition.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Functor where

open import Core.Type using (id; _∘_)
open import Core.Base using (refl; ap)
open import Core.Kan using (_∙_)
open import Cat.Base
open import Cat.Data.Magmoid
import Cat.Data.Map as Map

private
  mgm : ∀ {o h} → category o h → magmoids
  mgm C = str ob hom yon yon-emb where open Cat C

module _ {o h o' h'} (C : category o h) (D : category o' h') where
  open Map (mgm C) (mgm D) public
```

## Functor module

Opens a functor value, re-exporting its fields and the derived
`preserves-comp` for qualified access: `module F = Functor F-val`
gives `F.map`, `F.hmap`, `F.yon-natural`, `F.preserves-comp`.

```agda
module Functor
  {o h o' h'} {C : category o h} {D : category o' h'}
  (F : functor C D)
  where
  open Map.functor F public
```

## Identity functor

Both sides of `yon-natural` reduce to `C.yon f w k` when `map` and
`hmap` are both the identity, so the proof is `refl`.

```agda
module _ {o h} (C : category o h) where
  id-functor : functor C C
  id-functor .functor.map  = id
  id-functor .functor.hmap = id
  id-functor .functor.yon-natural f k = refl
```

## Functor composition

The `yon-natural` proof for `G ∘F F` proceeds in two steps:
first apply `G.yon-natural` to reduce the outer Yoneda action,
then `ap G.hmap` of `F.yon-natural` to reduce the inner one.

```agda
module _
  {o h o' h' o'' h''}
  {C : category o h}
  {D : category o' h'}
  {E : category o'' h''}
  (F : functor C D)
  (G : functor D E)
  where
  private
    module F = Functor {C = C} {D = D} F
    module G = Functor {C = D} {D = E} G

  _∘F_ : functor C E
  _∘F_ = comp where
    comp : functor C E
    comp .functor.map  = G.map ∘ F.map
    comp .functor.hmap = G.hmap ∘ F.hmap
    comp .functor.yon-natural f k =
      G.yon-natural (F.hmap f) (F.hmap k)
      ∙ ap G.hmap (F.yon-natural f k)
```
