Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Bundles.agda`.

Bundled ternary structures: a carrier together with its relation and the
proof that it forms a partial semigroup / monoid. (The `Setoid`/`partialSetoid`
conveniences from the original are omitted; they pull in
`Relation.Binary.Bundles.Setoid`, not yet ported.)

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Bundles where

open import Core.Type using (Type; Level; _⊔_; _₊)
open import Lib.Relation.Binary
open import Lib.Ternary.Core
open import Lib.Ternary.Structures using
  ( Emptiness
  ; IsPartialSemigroup
  ; IsPartialMonoid )

record PartialSemigroup a e : Type ((a ⊔ e) ₊) where
  infix 4 _≈_
  field
    {Carrier}   : Type a
    {_≈_}       : Carrier → Carrier → Type e
    {rel}       : Rel₃ Carrier

    isSemigroup : IsPartialSemigroup _≈_ rel

  open Rel₃ rel public
  open IsPartialSemigroup isSemigroup public

  instance equivalence : IsEquivalence _≈_
  equivalence = ≈-equivalence

record PartialMonoid a e : Type ((a ⊔ e) ₊) where
  field
    {Carrier} : Type a
    {_≈_}     : Carrier → Carrier → Type e
    {rel}     : Rel₃ Carrier
    {unit}    : Carrier

    isMonoid  : IsPartialMonoid _≈_ rel unit

  open IsPartialMonoid isMonoid public
  open Emptiness emptiness public
  open IsPartialSemigroup isSemigroup public

  partialSemigroup : PartialSemigroup a e
  partialSemigroup = record { isSemigroup = isSemigroup }

```
