Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Construct/Empty.agda`.

The trivially empty resource: no split ever exists. Parameterized by the
carrier `A` via an anonymous module.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Construct.Empty where

open import Core.Type using (Type; Level; ⊤; Lift)
open import Core.Base using (_≡_)
open import Core.Data.Empty using (⊥)
open import Core.Data.Sigma using (_,_)
open import Lib.Relation.Binary hiding (refl; sym; trans)
open import Lib.Ternary.Core
open import Lib.Ternary.Structures
open import Lib.Ternary.Structures.Syntax
open import Lib.Ternary.Respect.Propositional

module _ {a} (A : Type a) where

  instance empty-rel : Rel₃ A
  Rel₃._∙_≣_ empty-rel = λ _ _ _ → Lift _ ⊥

  instance empty-semigroup : IsPartialSemigroup _≡_ empty-rel
  IsPartialSemigroup.≈-equivalence empty-semigroup = ≡-isEquivalence
  IsPartialSemigroup.∙-assocᵣ empty-semigroup () ()
  IsPartialSemigroup.∙-assocₗ empty-semigroup () ()

  instance empty-commutative : IsCommutative empty-rel
  IsCommutative.∙-comm empty-commutative ()

  empty-xsplit : CrossSplit empty-rel empty-rel
  empty-xsplit () ()

```
