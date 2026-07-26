```agda

{-# OPTIONS --safe --two-level --cubical-compatible #-}

module Lib.SSet where

open import Core.Type

data _≡_ {u} {A : SSet} (x : A) : A → SSet u where
  refl : x ≡ x
