Properties of higher thinnings: set-level identity types,
composition, and representation.

The path constructors `os-coh` and `o'-coh` make transport
along element paths trivial. Combined with the recursive
structure, this should give `≤H-is-set` by induction on the
list indices.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Thinning.Properties where

open import Core.Type
open import Core.Base
  using (_≡_; refl; ap; sym; is-set; is-prop; PathP)
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type using (_:-_)
open import HData.Thinning.Type
open import HData.Thinning.Base

private variable
  u : Level
  K : Type u
  k : K
  iz jz kz : List K

-- The path constructors at refl are definitionally trivial:
-- os-coh refl θ = refl and o'-coh refl θ = refl.
-- This is the base case for showing the path constructors
-- don't add new point-level data.

-- The 1-cells make transport endpoints trivial but freely
-- add loops. Whether ≤H is a set, and what additional
-- structure would make it one, is the open question.
-- ≤H-is-set : is-set (_≤H_ {K = K} iz jz)
-- ≤H-is-set = ?

```
