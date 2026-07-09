Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Construct/Unit.agda`.

The trivial resource: the unit type carries a canonical separation algebra.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Construct.Unit where

open import Core.Type using (⊤; tt; Type; Level)
open import Core.Base using (_≡_; refl)
open import Core.Data.Sigma using (_,_)
open import Lib.Relation.Binary hiding (refl; sym; trans)
open import Lib.Ternary.Core
open import Lib.Ternary.Structures
open import Lib.Ternary.Structures.Syntax
open import Lib.Ternary.Respect.Propositional

instance unit-rel : Rel₃ ⊤
Rel₃._∙_≣_ unit-rel = λ _ _ _ → ⊤

instance unit-semigroup : IsPartialSemigroup _≡_ unit-rel
IsPartialSemigroup.≈-equivalence unit-semigroup = ≡-isEquivalence
IsPartialSemigroup.∙-assocᵣ unit-semigroup _ _ = _ , tt , tt
IsPartialSemigroup.∙-assocₗ unit-semigroup _ _ = _ , tt , tt

instance unit-commutative : IsCommutative unit-rel
IsCommutative.∙-comm unit-commutative _ = tt

```
