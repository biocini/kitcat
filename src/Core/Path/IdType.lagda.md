## Identity type characterizations

Characterizations of path types for sigma types, function types, and sum types.
These show that paths in structured types decompose into paths in their components.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Path.IdType where

open import Core.Transport.Base
open import Core.Transport.J
open import Core.Base
open import Core.Type
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Sum.Type
open import Core.Equiv.Base using (_≃_; iso→equiv; Equiv)
open import Core.IdSys

private
  variable
    u v : Level

Σ-path-equiv
  : {A : Type u} {B : A → Type v} {w x : Σ B}
  → (w ≡ x) ≃ (Σ p ∶ (fst w ≡ fst x) , PathP (λ i → B (p i)) (snd w) (snd x))
Σ-path-equiv = iso→equiv fwd bwd sec retr
  where
  fwd : _
  fwd p = ap fst p , ap snd p

  bwd : _
  bwd (p , q) i = p i , q i

  sec : _
  sec _ = refl

  retr : _
  retr _ = refl

Π-path-equiv
  : {A : Type u} {B : A → Type v} {f g : (x : A) → B x}
  → (f ≡ g) ≃ ((x : A) → f x ≡ g x)
Π-path-equiv = iso→equiv happly funext (λ _ → refl) (λ _ → refl)
```

### Sum type path characterizations

For sum types, paths between inl's are equivalent to paths between the
injected values, and similarly for inr's. Paths between inl and inr are
impossible (disjointness).

```agda

private
  -- Cover for sum types: decodes a path in A ⊎ B starting at inl a
  ⊎-codel : ∀ {u v} {A : Type u} {B : Type v} (a : A) → A ⊎ B → Type u
  ⊎-codel a (inl x) = a ≡ x
  ⊎-codel {u} a (inr _) = Lift u ⊥

  -- Cover for sum types: decodes a path in A ⊎ B starting at inr b
  ⊎-coder : ∀ {u v} {A : Type u} {B : Type v} (b : B) → A ⊎ B → Type v
  ⊎-coder {v = v} b (inl _) = Lift v ⊥
  ⊎-coder b (inr x) = b ≡ x

⊎-path-inl
  : {A : Type u} {B : Type v} {a a' : A}
  → (inl {B = B} a ≡ inl a') ≃ (a ≡ a')
⊎-path-inl {a = a} = Ids-based→equiv ⊎-inl-ids where
  ⊎-inl-ids
    : is-based-identity-system (inl a) (⊎-codel a) refl
  ⊎-inl-ids .to-path {inl x} q i  = inl (q i)
  ⊎-inl-ids .to-path {inr _} (liftℓ ())
  ⊎-inl-ids .to-path-over {inl x} q i j  = q (i ∧ j)
  ⊎-inl-ids .to-path-over {inr _} (liftℓ ())

⊎-path-inr
  : {A : Type u} {B : Type v} {b b' : B}
  → (inr {A = A} b ≡ inr b') ≃ (b ≡ b')
⊎-path-inr {b = b} = Ids-based→equiv ⊎-inr-ids where
  ⊎-inr-ids
    : is-based-identity-system (inr b) (⊎-coder b) refl
  ⊎-inr-ids .to-path {inl _} (liftℓ ())
  ⊎-inr-ids .to-path {inr x} q i  = inr (q i)
  ⊎-inr-ids .to-path-over {inl _} (liftℓ ())
  ⊎-inr-ids .to-path-over {inr x} q i j  = q (i ∧ j)

-- Disjointness: inl a and inr b are never equal
⊎-disjoint : {A : Type u} {B : Type v} {a : A} {b : B} → ¬ (inl a ≡ inr b)
⊎-disjoint p = subst discrim p tt
  where
  discrim : _ ⊎ _ → Type
  discrim (inl _) = ⊤
  discrim (inr _) = ⊥
```
