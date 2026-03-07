Identity systems: consolidated API, equivalence extraction, and canonical
instances.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.IdSys where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Data.Sigma
open import Core.Transport
open import Core.Equiv

open Core.Transport public
  using ( is-identity-system; is-based-identity-system
        ; to-path; to-path-over
        ; IdsJ; IdsJ-based
        ; singl-contr→Ids; fundamental-theorem-id; set-identity-system
        ; is-contr-ΣC
        )

```

## Canonical instances

```agda

path-identity-system
  : ∀ {u} {A : Type u} → is-identity-system {A = A} _≡_ (λ _ → refl)
path-identity-system .to-path p = p
path-identity-system .to-path-over p i j = p (i ∧ j)

```

## Equivalence extraction

Given an identity system, the reflexive relation is fiberwise equivalent to
paths. These combinators eliminate the manual encode-decode pattern.

```agda

Ids-based→equiv
  : ∀ {u v} {A : Type u} {a : A} {C : A → Type v} {r : C a}
  → is-based-identity-system a C r
  → ∀ {b} → (a ≡ b) ≃ C b
Ids-based→equiv {a = a} {C = C} {r = r} ids {b} =
  iso→equiv fwd bwd sec retr
  where
  fwd : ∀ {b'} → a ≡ b' → C b'
  fwd p = subst C p r

  bwd : ∀ {b'} → C b' → a ≡ b'
  bwd c = ids .to-path c

  sec : (p : a ≡ b) → bwd (fwd p) ≡ p
  sec p = J (λ b' p' → bwd {b'} (fwd p') ≡ p')
    (ap (ids .to-path) (transport-refl r) ∙ loop-refl) p
    where
    loop-refl : ids .to-path r ≡ refl
    loop-refl i j =
      is-contr→loop-is-refl (is-contr-ΣC ids) i j .fst

  retr : (c : C b) → fwd (bwd c) ≡ c
  retr c = Path-over.from-pathp (ids .to-path-over c)

Ids→equiv
  : ∀ {u v} {A : Type u} {R : A → A → Type v} {r : ∀ a → R a a}
  → is-identity-system R r
  → ∀ {a b} → (a ≡ b) ≃ R a b
Ids→equiv {R = R} {r = r} ids {a} {b} =
  iso→equiv fwd bwd sec retr
  where
  fwd : ∀ {b'} → a ≡ b' → R a b'
  fwd p = subst (R a) p (r a)

  bwd : ∀ {b'} → R a b' → a ≡ b'
  bwd s = ids .to-path s

  sec : (p : a ≡ b) → bwd (fwd p) ≡ p
  sec p = J (λ b' p' → bwd {b'} (fwd p') ≡ p')
    (ap (ids .to-path) (transport-refl (r a)) ∙ loop-refl) p
    where
    loop-refl : ids .to-path (r a) ≡ refl
    loop-refl i j =
      is-contr→loop-is-refl (is-contr-ΣR ids {a}) i j .fst

  retr : (s : R a b) → fwd (bwd s) ≡ s
  retr s = Path-over.from-pathp (ids .to-path-over s)

```
