Lane Biocini, February 2026. Fiber-truncated partial elements:
maps whose fibers have controlled h-level.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Function.Partial.Fiber where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat.Type using (Nat; S)
open import Core.HLevel
  using ( is-hlevel; is-hlevel-suc; is-contr→is-hlevel
        ; is-prop→is-hlevel-suc; Path-is-hlevel; Σ-is-hlevel )
open import Core.Equiv using (is-equiv; eqv-fibers)
open import Core.Function.Embedding using (is-embedding)

private variable
  u v : Level
  n : Nat
```


## The n-Map

An `n-Map u X n` classifies maps into `X` whose fibers have h-level
`n`. Where `LiftM` controls the h-level of the definedness
predicate, `n-Map` instead controls the h-level of the fibers of the
value map.

```agda
record n-Map (u : Level) {v : Level} (X : Type v) (n : Nat)
  : Type (u ₊ ⊔ v) where
  no-eta-equality
  field
    is-defined  : Type u
    value       : is-defined → X
    fiber-trunc : (x : X) → is-hlevel n (fiber value x)

open n-Map public
{-# INLINE n-Map.constructor #-}
```


## Bridges

```agda
module _ {u : Level} where

  from-equiv
    : ∀ {v} {A : Type u} {X : Type v}
    → (f : A → X) → is-equiv f → n-Map u X 0
  from-equiv f e .is-defined  = _
  from-equiv f e .value       = f
  from-equiv f e .fiber-trunc = eqv-fibers e

  from-embedding
    : ∀ {v} {A : Type u} {X : Type v}
    → (f : A → X) → is-embedding f → n-Map u X 1
  from-embedding f e .is-defined  = _
  from-embedding f e .value       = f
  from-embedding f e .fiber-trunc = e

  n-Map-suc
    : ∀ {v n} {X : Type v}
    → n-Map u X n → n-Map u X (S n)
  n-Map-suc m .is-defined  = is-defined m
  n-Map-suc m .value       = value m
  n-Map-suc m .fiber-trunc x = is-hlevel-suc (fiber-trunc m x)

  to-equiv
    : ∀ {v} {X : Type v}
    → (m : n-Map u X 0) → is-equiv (value m)
  to-equiv m .eqv-fibers = fiber-trunc m

  to-embedding
    : ∀ {v} {X : Type v}
    → (m : n-Map u X 1) → is-embedding (value m)
  to-embedding m = fiber-trunc m
```


## Distinguished elements

`η` is characterized by domain contractibility, `⊥ₗ` by domain
emptiness via the general `from-empty` constructor.

```agda
  η : ∀ {v n} {X : Type v}
    → is-hlevel (S n) X → X → n-Map u X n
  η hl x .is-defined = Lift _ ⊤
  η hl x .value _    = x
  η {n = n} hl x .fiber-trunc y = Σ-is-hlevel n
    (is-contr→is-hlevel n (Contr (liftℓ tt) λ { (liftℓ tt) → refl }))
    (λ _ → Path-is-hlevel hl)

  from-empty
    : ∀ {v m} {X : Type v} {D : Type u}
    → (D → ⊥) → n-Map u X (S m)
  from-empty e .is-defined    = _
  from-empty e .value d       = ex-falso (e d)
  from-empty e .fiber-trunc y =
    is-prop→is-hlevel-suc λ (d , _) → ex-falso (e d)

  ⊥ₗ : ∀ {v m} {X : Type v} → n-Map u X (S m)
  ⊥ₗ = from-empty lower
```
