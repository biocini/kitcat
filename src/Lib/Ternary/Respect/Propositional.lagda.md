Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Respect/Propositional.agda`.

Every predicate respects propositional (path) equality, by transport. Also
provides the canonical `IsEquivalence _≡_` used by constructions whose
carrier equality is propositional.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Respect.Propositional where

open import Core.Type using (Type; Level)
open import Core.Base using (_≡_; refl; sym)
open import Core.Kan using (_∙_)
open import Core.Transport.Base using (transport)
open import Lib.Relation.Unary using (Pred)
open import Lib.Relation.Binary using (IsEquivalence)
open import Lib.Ternary.Core using (Respect)

-- Every predicate respects propositional equality.
coe-≡
  : ∀ {a p} {A : Type a} (P : Pred A p) {x y : A} → x ≡ y → P x → P y
coe-≡ P eq px = transport (λ i → P (eq i)) px

instance
  respect-≡ : ∀ {a p} {A : Type a} {P : Pred A p} → Respect _≡_ P
Respect.coe respect-≡ eq px = coe-≡ _ eq px

-- The canonical equivalence on `_≡_` (cubical paths).
≡-isEquivalence : ∀ {a} {A : Type a} → IsEquivalence (_≡_ {A = A})
IsEquivalence.refl  ≡-isEquivalence = refl
IsEquivalence.sym   ≡-isEquivalence = sym
IsEquivalence.trans ≡-isEquivalence p q = p ∙ q

```
