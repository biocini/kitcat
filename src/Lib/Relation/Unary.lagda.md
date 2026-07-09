Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet).

This mirrors the slice of agda-stdlib's `Relation.Unary` that the ternary
relations library depends on: predicates over a carrier, inclusion, the
empty and singleton predicates, and the pointwise implication. Predicates
are just families `A → Type ℓ`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Relation.Unary where

open import Core.Type
open import Core.Base using (_≡_)
open import Core.Data.Sigma using (Sigma; _,_; fst; snd; _×_)
open import Core.Data.Empty using (⊥)
open import Core.Data.Sum using (_⊎_)

-- Predicates over a carrier.
Pred : ∀ {a} (A : Type a) (ℓ : Level) → Type (a ⊔ (ℓ ₊))
Pred A ℓ = A → Type ℓ

-- The universal (always-satisfied) predicate.
U : ∀ {a} {A : Type a} → Pred A 0ℓ
U = λ _ → ⊤

-- Pointwise implication as a predicate.
infixr 2 _⇒_
_⇒_
  : ∀ {a p q} {A : Type a} → Pred A p → Pred A q → Pred A (p ⊔ q)
(P ⇒ Q) x = P x → Q x

-- Universal forcing of a predicate.
∀[_] : ∀ {a p} {A : Type a} → Pred A p → Type (a ⊔ p)
∀[ P ] = ∀ {x} → P x

-- Predicate inclusion / reverse inclusion.
infix 4 _⊆_ _⊇_
_⊆_
  : ∀ {a p q} {A : Type a} → Pred A p → Pred A q → Type (a ⊔ p ⊔ q)
P ⊆ Q = ∀ {x} → P x → Q x

_⊇_
  : ∀ {a p q} {A : Type a} → Pred A q → Pred A p → Type (a ⊔ p ⊔ q)
Q ⊇ P = P ⊆ Q

-- The empty predicate.
∅ : ∀ {a} {A : Type a} → Pred A 0ℓ
∅ = λ _ → ⊥

-- A predicate respects a binary relation when it is stable under it.
infix 3 _Respects_
_Respects_
  : ∀ {a e p} {A : Type a} → Pred A p → (A → A → Type e) → Type (a ⊔ p ⊔ e)
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

-- A predicate is satisfiable when some carrier point lies in it.
Satisfiable
  : ∀ {a p} {A : Type a} → Pred A p → Type (a ⊔ p)
Satisfiable {A = A} P = Sigma A (λ x → P x)

-- Singleton predicate: ownership of a single point.
infix 9 ｛_｝
｛_｝ : ∀ {a} {A : Type a} → A → Pred A a
｛ x ｝ = λ y → x ≡ y

-- Pointwise union and intersection.
infixr 6 _∪_
infixr 7 _∩_
_∪_
  : ∀ {a p q} {A : Type a} → Pred A p → Pred A q → Pred A (p ⊔ q)
(P ∪ Q) x = P x ⊎ Q x

_∩_
  : ∀ {a p q} {A : Type a} → Pred A p → Pred A q → Pred A (p ⊔ q)
(P ∩ Q) x = P x × Q x

```
