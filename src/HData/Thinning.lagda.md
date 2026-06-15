Higher thinnings: order-preserving embeddings as a HIT.

The point constructors are the same as `Data.Thin.Type._≤_`.
The path constructors `os-coh` and `o'-coh` internalize
parametricity in the element type: transport along element
paths is trivial. This makes the type a set without assuming
`is-set K`, enabling the thinning virtual category for
arbitrary element types.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Thinning where

open import HData.Thinning.Type public
open import HData.Thinning.Base public

```
