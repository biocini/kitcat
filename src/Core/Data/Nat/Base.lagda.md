Natural numbers: type, arithmetic, and ordering.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Nat.Base where

open import Core.Type

open import Core.Data.Nat.Type
open import Core.Data.Bool.Type using (Bool)

open import Agda.Builtin.Nat public
  using (_+_; _*_; _-_; div-helper; mod-helper)
  renaming (_==_ to EqBool; _<_ to LtBool)

ind : ∀ {u} (P : Nat → Type u)
          → P Z
          → (∀ {k} → P k → P (S k))
          → ∀ n → P n
ind P z s Z = z
ind P z s (S n) = s (ind P z s n)

data _<_ (m : Nat) : Nat → Type where
  instance suc : m < S m
  step : ∀ {n} → m < n → m < S n

_≤_ : Nat → Nat → Type
m ≤ n = m < S n

s<s : ∀ {m n} → m < n → S m < S n
s<s suc = suc
s<s (step p) = step (s<s p)

pred : Nat → Nat
pred Z     = Z
pred (S n) = n

max : Nat → Nat → Nat
max Z     n     = n
max (S m) Z     = S m
max (S m) (S n) = S (max m n)

_≤ᵇ_ : Nat → Nat → Bool
m ≤ᵇ n = LtBool m (S n)

_==ᵇ_ : Nat → Nat → Bool
_==ᵇ_ = EqBool
