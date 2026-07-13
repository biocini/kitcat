Test: separated os avoids K.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Test.SepTest where

open import Core.Type
open import Core.Base
  using (_≡_; refl; ap; is-set; is-prop)
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type using (_:-_)

open Core.Type using (⊤; tt)
open import Core.Data.Empty using (⊥)

private variable
  u : Level
  K : Type u
  iz jz : List K

data Thin {u} {K : Type u}
  : List K → List K → Type u where
  o' : ∀ {iz jz k}
     → Thin iz jz → Thin iz (jz :- k)
  os : ∀ {iz jz} (k₁ k₂ : K) → k₁ ≡ k₂
     → Thin iz jz → Thin (iz :- k₁) (jz :- k₂)
  oz : Thin [] []

-- The key test: matching two Thin values at os.
-- k₁, k₂ are separate explicit args, so the second
-- match unifies k₃ = k₁ and k₄ = k₂ by cons
-- injectivity — no reflexive equation on K.
code : ∀ {u} {K : Type u} {iz jz : List K}
  → Thin iz jz → Thin iz jz → Type u
code (o' t₁)           (o' t₂)         = code t₁ t₂
code (os k₁ k₂ p₁ t₁) (os _ _ p₂ t₂) = code t₁ t₂
code oz                oz              = Lift _ ⊤
code (o' _)            (os _ _ _ _)    = Lift _ ⊥
code (os _ _ _ _)      (o' _)          = Lift _ ⊥

code-is-prop : ∀ {u} {K : Type u} {iz jz : List K}
  → (t₁ t₂ : Thin iz jz)
  → is-prop (code t₁ t₂)
code-is-prop (o' t₁)           (o' t₂)
  = code-is-prop t₁ t₂
code-is-prop (os k₁ k₂ p₁ t₁) (os _ _ p₂ t₂)
  = code-is-prop t₁ t₂
code-is-prop oz                oz
  (liftℓ tt) (liftℓ tt) = refl
code-is-prop (o' _)            (os _ _ _ _)
  (liftℓ ())
code-is-prop (os _ _ _ _)      (o' _)
  (liftℓ ())

```
