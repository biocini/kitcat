{-# OPTIONS --safe --erased-cubical #-}
module Test.ListTest where

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.List

variable
  A : Set

-- Does transport over constant family reduce to identity?
test : (xs : List A) → primTransp (λ _ → List A) i0 xs ≡ xs
test xs = refl
