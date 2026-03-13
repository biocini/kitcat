Truncation level automation via instance resolution.

The H-Level automation machinery in this module is largely derived from 1Lab
(Amelia Liao et al.), with additional influence from Chen's semicategories-with-
identities formalization.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Trunc where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat.Type
open import Core.Data.Nat.Base using (_+_)
open import Core.Transport
open import Core.HLevel.Base public

private variable
  ℓ : Level
  A : Type ℓ
```


## The Trunc trait record

```agda

record Trunc {ℓ} (T : Type ℓ) (n : Nat) : Type ℓ where
  no-eta-equality
  constructor trunc-instance
  field has-trunc : is-hlevel n T

open Trunc ⦃ ... ⦄ public
{-# INLINE Trunc.constructor #-}
{-# DISPLAY Trunc.has-trunc _ x = has-trunc x #-}
```


## Entry points

```agda

trunc : (n : Nat) ⦃ _ : Trunc A n ⦄ → is-hlevel n A
trunc n = has-trunc

trunc! : ⦃ _ : Trunc A Z ⦄ → A
trunc! = has-trunc .center

prop! : ∀ {A : I → Type ℓ} ⦃ hl : ∀ {i} → Trunc (A i) (S Z) ⦄ {x : A i0} {y : A i1}
      → PathP A x y
prop! ⦃ hl ⦄ {x} {y} = is-prop→PathP (λ i → hl .has-trunc) x y
```


## Instance helpers

```agda

basic-trunc : (n : Nat) → is-hlevel n A → ∀ {k} → Trunc A (n + k)
basic-trunc n hl {k} .has-trunc = is-hlevel-+ n k hl

prop-trunc : is-prop A → ∀ {k} → Trunc A (S k)
prop-trunc p {k} .has-trunc = is-prop→is-hlevel-suc {n = k} p

set-trunc : is-set A → ∀ {k} → Trunc A (S (S k))
set-trunc s {k} .has-trunc = is-hlevel-+ 2 k s

contr-trunc : is-contr A → ∀ {k} → Trunc A k
contr-trunc c {k} .has-trunc = is-contr→is-hlevel k c
```


## Instances

```agda

instance
  Trunc-Π : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {n}
          → ⦃ ∀ {x} → Trunc (B x) n ⦄
          → Trunc ((x : A) → B x) n
  Trunc-Π {n = n} .has-trunc = Π-is-hlevel n (λ _ → trunc n)

  Trunc-Πi : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {n}
           → ⦃ hl : ∀ {x} → Trunc (B x) n ⦄
           → Trunc ({x : A} → B x) n
  Trunc-Πi {n = Z} ⦃ hl ⦄ .has-trunc .center {x} = hl .has-trunc .center
  Trunc-Πi {n = Z} ⦃ hl ⦄ .has-trunc .paths f i {x} = hl .has-trunc .paths f i
  Trunc-Πi {n = S Z} .has-trunc = Πi-is-prop (λ _ → trunc 1)
  Trunc-Πi {n = S (S n)} ⦃ hl ⦄ .has-trunc f g =
    retract→is-hlevel (S n) (λ p i {x} → p x i) (λ q x i → q i {x})
      (λ _ → refl) (Π-is-hlevel (S n) λ x → hl {x} .has-trunc (f {x}) (g {x}))

  Trunc-Σ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {n}
          → ⦃ Trunc A n ⦄ → ⦃ ∀ {x} → Trunc (B x) n ⦄
          → Trunc (Σ B) n
  Trunc-Σ {n = n} .has-trunc = Σ-is-hlevel n (trunc n) (λ _ → trunc n)

  Trunc-× : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {n}
          → ⦃ Trunc A n ⦄ → ⦃ Trunc B n ⦄
          → Trunc (A × B) n
  Trunc-× {n = n} .has-trunc = ×-is-hlevel n (trunc n) (trunc n)

  Trunc-PathP : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} {n}
              → ⦃ Trunc (A i1) (S n) ⦄
              → Trunc (PathP A x y) n
  Trunc-PathP {n = n} .has-trunc = PathP-is-hlevel (trunc (S n))

  Trunc-Path : ∀ {ℓ} {A : Type ℓ} {x y : A} {n}
             → ⦃ Trunc A (S n) ⦄
             → Trunc (x ≡ y) n
  Trunc-Path {n = n} .has-trunc = Path-is-hlevel (trunc (S n))

  Trunc-Lift : ∀ {ℓ ℓ'} {A : Type ℓ} {n}
             → ⦃ Trunc A n ⦄
             → Trunc (Lift ℓ' A) n
  Trunc-Lift {n = n} .has-trunc = Lift-is-hlevel n (trunc n)

  Trunc-⊤ : ∀ {n} → Trunc ⊤ n
  Trunc-⊤ = contr-trunc (Contr tt (λ _ → refl))

  Trunc-Unit : ∀ {ℓ} {n} → Trunc (Unit {ℓ}) n
  Trunc-Unit = contr-trunc (Contr (liftℓ tt) (λ { (liftℓ tt) → refl }))

  Trunc-⊥ : ∀ {n} → Trunc ⊥ (S n)
  Trunc-⊥ = prop-trunc (λ x → ex-falso x)

  Trunc-is-prop : ∀ {ℓ} {A : Type ℓ} {n} → Trunc (is-prop A) (S n)
  Trunc-is-prop = prop-trunc (is-prop-is-prop _)

  Trunc-is-contr : ∀ {ℓ} {A : Type ℓ} {n} → Trunc (is-contr A) (S n)
  Trunc-is-contr = prop-trunc (is-contr-is-prop _)

  Trunc-is-hlevel : ∀ {ℓ} {A : Type ℓ} {n m} → Trunc (is-hlevel n A) (S m)
  Trunc-is-hlevel {n = n} = prop-trunc (is-hlevel-is-prop n)

{-# OVERLAPS Trunc-⊤ Trunc-Unit Trunc-⊥ #-}
{-# OVERLAPS Trunc-is-prop Trunc-is-contr Trunc-is-hlevel #-}
```
