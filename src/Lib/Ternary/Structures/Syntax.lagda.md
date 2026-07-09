Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures/Syntax.agda`.

Overloaded syntax: opening this module brings the fields of every ternary
structure into scope via instance search, so callers need only declare their
relations/structures as `instance`s and use `_✴_`, `_─✴_`, `ε`, etc. directly.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures.Syntax where

open import Lib.Relation.Binary
open import Lib.Ternary.Core
open import Lib.Ternary.Structures

open IsEquivalence ⦃ ... ⦄ using () renaming
  ( refl to ≈-refl
  ; sym to ≈-sym
  ; trans to ≈-trans) public

open Rel₃               ⦃ ... ⦄ public
open Emptiness          ⦃ ... ⦄ public
open IsPartialSemigroup ⦃ ... ⦄ public
open IsPartialMonoid    ⦃ ... ⦄ public
open IsPositive         ⦃ ... ⦄ public
open IsPositiveWithZero ⦃ ... ⦄ public
open IsCommutative      ⦃ ... ⦄ public
open IsCrosssplittable  ⦃ ... ⦄ public
open IsIdempotent       ⦃ ... ⦄ public

open CommutativeSemigroupOps public

```
