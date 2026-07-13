Test: which Tri cases allow propositional proofs?

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Test.TriProp where

open import Core.Type
open import Core.Base using (_≡_; refl; ap; is-prop)
open import Core.HCompU
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type
open import Data.Thin.Base
open import Data.Thin.Tri

private variable
  u : Level
  K : Type u
  iz jz kz : List K

-- Test 1: can we match a single Tri at tsss?
single-tsss : {θ : iz ≤ jz} {φ : jz ≤ kz} {ψ : iz ≤ kz}
  → Tri θ φ ψ → List K
single-tsss (t-'' t) = single-tsss t
single-tsss (t's' t) = single-tsss t
single-tsss (tsss t) = single-tsss t
single-tsss tzzz     = []

-- Test 2: matching two Tri at t-''/t-''
tri-prop-oo : {θ : iz ≤ jz} {φ : jz ≤ kz} {ψ : iz ≤ kz}
  → (t₁ t₂ : Tri θ (o' φ) (o' ψ))
  → t₁ ≡ t₂
tri-prop-oo (t-'' t₁) (t-'' t₂) = ap t-'' (tri-prop-oo t₁ t₂)

-- Test 3: matching two Tri at t's'/t's'
tri-prop-ss : {θ : iz ≤ jz} {φ : jz ≤ kz} {ψ : iz ≤ kz}
  → (t₁ t₂ : Tri (o' θ) (os φ) (o' ψ))
  → t₁ ≡ t₂
tri-prop-ss (t's' t₁) (t's' t₂) = ap t's' (tri-prop-ss t₁ t₂)

-- Test 4: matching two Tri at tsss/tsss (expect K failure)
tri-prop-sss : {θ : iz ≤ jz} {φ : jz ≤ kz} {ψ : iz ≤ kz}
  → (t₁ t₂ : Tri (os θ) (os φ) (os ψ))
  → t₁ ≡ t₂
tri-prop-sss (tsss t₁) (tsss t₂) = ap tsss (tri-prop-sss t₁ t₂)

-- Test 5: full Tri-is-prop (expect K failure at tsss)
-- tri-is-prop : {θ : iz ≤ jz} {φ : jz ≤ kz} {ψ : iz ≤ kz}
--   → (t₁ t₂ : Tri θ φ ψ) → t₁ ≡ t₂

```
