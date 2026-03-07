Generic h-level utilities: contractibility, propositions, sets, and truncation.

This module re-exports Core.Trait.Trunc (which provides is-hlevel and the Trunc
automation) and adds closure lemmas and utilities that don't depend on specific
data types.

The H-Level automation machinery is largely derived from 1Lab (Amélia Liao et al.),
with additional influence from Chen's semicategories-with-identities formalization.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.HLevel.Base where

open import Core.Data.Nat
open import Core.Transport
open import Core.Equiv
open import Core.Base
open import Core.Path.Base
open import Core.Data.Sigma
open import Core.Type
open import Core.Kan
open import Core.Sub

-- Re-export the Trunc trait and is-hlevel definitions
open import Core.Trait.Trunc public

private variable
  u v : Level
  A B : Type u

is-groupoid : ∀ {u} → Type u → Type u
is-groupoid = is-hlevel 3


-- nType: bundled n-truncated types (the n-type classifier)

record nType u n : Type₊ u where
  no-eta-equality
  field
    ∣_∣   : Type u
    is-tr : is-hlevel n ∣_∣

{-# INLINE nType.constructor #-}

-- Additional proofs

PathP-is-hlevel'
  : ∀ {u} {A : I → Type u} {n} {x : A i0} {y : A i1}
  → ((i : I) → is-hlevel (S n) (A i)) → is-hlevel n (PathP A x y)
PathP-is-hlevel' hl = PathP-is-hlevel (hl i1)

equiv→is-hlevel
  : ∀ {u v} {A : Type u} {B : Type v} (n : Nat)
  → A ≃ B → is-hlevel n A → is-hlevel n B
equiv→is-hlevel n e =
  retract→is-hlevel n (Equiv.fwd e) (Equiv.inv e) (Equiv.counit e)

is-prop-×
  : ∀ {u v} {A : Type u} {B : Type v}
  → is-prop A → is-prop B → is-prop (A × B)
is-prop-× aprop bprop (a , b) (a' , b') i = aprop a a' i , bprop b b' i

is-prop-equiv
  : ∀ {u v} {A : Type u} {B : Type v}
  → A ≃ B → is-prop B → is-prop A
is-prop-equiv e bprop x y = p
  where
    module E = Equiv e
    p : x ≡ y
    p = sym (E.unit x) ∙ ap E.inv (bprop (E.fwd x) (E.fwd y)) ∙ E.unit y

singl-contr-in-contr
  : ∀ {u} {A : Type u}
  → is-contr A → (x : A) → is-contr (Σ y ∶ A , x ≡ y)
singl-contr-in-contr c x .center = x , refl
singl-contr-in-contr c x .paths (y , p) = Σ-prop-path (is-contr→is-set c x) p

subst-prop
  : ∀ {u u'} {A : Type u} {P : A → Type u'}
  → is-prop A → ∀ a → P a → ∀ b → P b
subst-prop {P = P} prop a pa b = subst P (prop a b) pa

contr→contr-fiber
  : ∀ {u u'} {A : Type u} {B : Type u'}
  → (f : A → B) → is-contr A → is-contr B
  → ∀ b → is-contr (Σ a ∶ A , f a ≡ b)
contr→contr-fiber {A = A} f acontr bcontr b =
  prop-inhabited→is-contr fiber-is-prop fiber-inhabited
  where
    β : (x : A) → is-prop (f x ≡ b)
    β x f g = is-contr→is-set bcontr _ _ f g

    fiber-is-prop : is-prop (Σ a ∶ A , f a ≡ b)
    fiber-is-prop (a₁ , p₁) (a₂ , p₂) =
      Σ-prop-path β (is-contr→is-prop acontr a₁ a₂)

    fiber-inhabited : Σ a ∶ A , f a ≡ b
    fiber-inhabited = acontr .center , is-contr→is-prop bcontr _ _


-- H-level closure lemmas from Rijke (Sections 12-13)

-- Propositions are closed under implication
-- (Π-is-prop is in Core.Trait.Trunc)
→-is-prop
  : ∀ {u v} {A : Type u} {B : Type v}
  → is-prop B → is-prop (A → B)
→-is-prop bprop = Π-is-prop (λ _ → bprop)

-- Sets are closed under Π
-- This is a special case of Π-is-hlevel at level 2
Π-is-set
  : ∀ {u v} {A : Type u} {B : A → Type v}
  → ((x : A) → is-set (B x))
  → is-set ((x : A) → B x)
Π-is-set bset f g =
  retract→is-hlevel 1 funext happly (λ _ → refl)
    (Π-is-prop (λ x → bset x (f x) (g x)))

-- Sets are closed under →
→-is-set
  : ∀ {u v} {A : Type u} {B : Type v}
  → is-set B → is-set (A → B)
→-is-set bset = Π-is-set (λ _ → bset)

-- Σ over a set with set fibers is a set
-- (This is a special case of Σ-is-hlevel from Core.Trait.Trunc)
Σ-is-set
  : ∀ {u v} {A : Type u} {B : A → Type v}
  → is-set A → ((x : A) → is-set (B x))
  → is-set (Σ B)
Σ-is-set aset bset = Σ-is-hlevel 2 aset bset

open Nat using (_<_; suc; step; _≤_)

is-hlevel-<
  : ∀ {u} {A : Type u} {n m : Nat}
  → n < m → is-hlevel n A → is-hlevel m A
is-hlevel-< suc      hl = is-hlevel-suc hl
is-hlevel-< (step p) hl = is-hlevel-suc (is-hlevel-< p hl)

is-hlevel-≤
  : ∀ {u} {A : Type u} {n m : Nat}
  → n ≤ m → is-hlevel n A → is-hlevel m A
is-hlevel-≤ suc      hl = hl
is-hlevel-≤ (step p) hl = is-hlevel-< p hl
```


## Proposition utilities

```agda

-- Paths in propositions are contractible
is-prop→Path-is-contr
  : ∀ {u} {A : Type u}
  → is-prop A → (x y : A) → is-contr (x ≡ y)
is-prop→Path-is-contr aprop x y =
  prop-inhabited→is-contr (is-prop→is-set aprop x y) (aprop x y)

-- Propositions are closed under retraction
-- If B is a retract of A (via section f : A → B) and A is a prop, then B is a prop.
-- The condition is: f (g b) ≡ b for all b : B (g is a section of f).
retract→is-prop
  : ∀ {u' v'} {A' : Type u'} {B' : Type v'}
  → (f : A' → B') (g : B' → A')
  → is-left-inverse f g
  → is-prop A' → is-prop B'
retract→is-prop f g r aprop = retract→is-hlevel 1 f g r aprop
```
