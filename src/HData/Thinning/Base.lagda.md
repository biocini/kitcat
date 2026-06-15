Basic operations on higher thinnings: identity, empty,
and the embedding from ordinary thinnings.

Composition requires handling the path constructors and
is left for Properties.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Thinning.Base where

open import Core.Type
open import Core.Base using (_≡_; refl; ap; PathP)
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type using (_:-_)
open import HData.Thinning.Type

private variable
  u : Level
  K : Type u
  k : K
  iz jz kz : List K

oi : {kz : List K} → kz ≤H kz
oi {kz = kz :- _} = os oi
oi {kz = []}       = oz

oe : {kz : List K} → [] ≤H kz
oe {kz = kz :- _} = o' oe
oe {kz = []}       = oz

-- Embedding from ordinary thinnings
open import Data.Thin.Type using (_≤_)
  renaming (o' to o''; os to os'; oz to oz')

embed : iz ≤ jz → iz ≤H jz
embed (o'' θ) = o' (embed θ)
embed (os' θ) = os (embed θ)
embed oz'     = oz

```
