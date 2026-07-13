{-# OPTIONS --safe --erased-cubical #-}
module Test.PathTest where

open import Agda.Primitive
open import Agda.Primitive.Cubical
  renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.List
open import Agda.Builtin.Cubical.HCompU
open import Agda.Builtin.Sigma

refl' : ∀ {u} {A : Set u} {x : A} → x ≡ x
refl' {x = x} _ = x

-- Singl-contr
Singl-contr : ∀ {u} {A : Set u} (x : A) (y : A) (p : x ≡ y) → (x , refl' {x = x}) ≡ (y , p)
Singl-contr x y p i = (p i , λ j → p (i ∧ j))

-- coei1: transport from position i to i1
coei1 : ∀ {u} (A : I → Set u) (i : I) → A i → A i1
coei1 A i = primTransp (λ j → A (i ∨ j)) i

-- The key: Singl-contr gives us a dependent path
-- .snd at i has type [] ≡ p i
-- We transport each point to i1, giving type [] ≡ p i1 = [] ≡ []
nil-path-contr : ∀ {A : Set} (p : [] {A = A} ≡ []) → refl' {x = [] {A = A}} ≡ p
nil-path-contr {A} p i = coei1 (λ j → [] ≡ p j) i (Singl-contr [] [] p i .snd)
