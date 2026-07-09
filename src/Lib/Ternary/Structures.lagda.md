Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures.agda`.

Aggregator for the ternary-relation structure hierarchy. (`Total` and
`PartialJoinoid` are deferred: they depend on a total-operation `IsMonoid`
from `Algebra.Structures`, not yet ported.)

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures where

open import Lib.Ternary.Structures.PartialSemigroup public
open import Lib.Ternary.Structures.PartialMonoid public
open import Lib.Ternary.Structures.Commutative public
open import Lib.Ternary.Structures.Positive public
open import Lib.Ternary.Structures.Functional public
open import Lib.Ternary.Structures.Crosssplit public
open import Lib.Ternary.Structures.Idempotent public
open import Lib.Ternary.Structures.PartialBand public

```
