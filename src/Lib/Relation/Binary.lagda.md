Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet).

This mirrors the slice of agda-stdlib's `Relation.Binary` that the ternary
relations library depends on: binary relations, the `IsEquivalence` record,
and the `Congruent` / `_Preserves_⟶_` helpers from `Function.Definitions`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Relation.Binary where

open import Core.Type

-- Binary relations over a carrier.
Rel : ∀ {a} (A : Type a) (ℓ : Level) → Type (a ⊔ (ℓ ₊))
Rel A ℓ = A → A → Type ℓ

-- A binary relation is an equivalence when it is reflexive, symmetric and
-- transitive.
record IsEquivalence
  {a ℓ} {A : Type a} (_≈_ : Rel A ℓ) : Type (a ⊔ ℓ) where
  no-eta-equality
  field
    refl  : ∀ {x} → x ≈ x
    sym   : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
{-# INLINE IsEquivalence.constructor #-}

open IsEquivalence ⦃ ... ⦄ public

-- A function is congruent w.r.t. two relations when it preserves them.
Congruent
  : ∀ {a b ℓ ℓ'} {A : Type a} {B : Type b}
  → Rel A ℓ → Rel B ℓ' → (A → B) → Type (a ⊔ ℓ ⊔ ℓ')
Congruent _≈_ _≈'_ f = ∀ {x y} → x ≈ y → f x ≈' f y

-- `_ Preserves _ ⟶ _`: unary preservation of a relation.
infixr 0 _Preserves_⟶_
_Preserves_⟶_
  : ∀ {a b ℓ ℓ'} {A : Type a} {B : Type b}
  → (A → B) → Rel A ℓ → Rel B ℓ' → Type (a ⊔ ℓ ⊔ ℓ')
_Preserves_⟶_ f _∼_ _≈_ = ∀ {x y} → x ∼ y → f x ≈ f y

```
