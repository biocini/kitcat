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
open import Core.HLevel.Base
  using ( is-hlevel; is-hlevel-suc; is-contr→is-hlevel
        ; is-prop→is-hlevel-suc; Path-is-hlevel; Σ-is-hlevel )
open import Core.Equiv.Base using (is-equiv; eqv-fibers; _≃_; Equiv)
open import Core.Function.Embedding
  using (is-embedding; equiv→embedding; _∙↪_)
open import Core.Kan using (Σ-contr-contr; _∙_)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties
  using (prop-inhabited→is-contr)

private variable
  u v : Level
  n : Nat
```


## The hMap

An `hMap u X n` classifies maps into `X` whose fibers have h-level
`n`. Where `LiftM` controls the h-level of the definedness
predicate, `hMap` controls the h-level of the fibers of the value
map.

```agda
record hMap (u : Level) {v : Level} (X : Type v) (n : Nat)
  : Type (u ₊ ⊔ v) where
  no-eta-equality
  field
    is-defined  : Type u
    value       : is-defined → X
    fiber-trunc : (x : X) → is-hlevel n (fiber value x)

open hMap public
{-# INLINE hMap.constructor #-}
```


## Bridges

```agda
module _ {u : Level} where

  from-equiv
    : ∀ {v} {A : Type u} {X : Type v}
    → (f : A → X) → is-equiv f → hMap u X 0
  from-equiv f e .is-defined  = _
  from-equiv f e .value       = f
  from-equiv f e .fiber-trunc = eqv-fibers e

  from-embedding
    : ∀ {v} {A : Type u} {X : Type v}
    → (f : A → X) → is-embedding f → hMap u X 1
  from-embedding f e .is-defined  = _
  from-embedding f e .value       = f
  from-embedding f e .fiber-trunc = e

  hMap-suc
    : ∀ {v n} {X : Type v}
    → hMap u X n → hMap u X (S n)
  hMap-suc m .is-defined  = is-defined m
  hMap-suc m .value       = value m
  hMap-suc m .fiber-trunc x = is-hlevel-suc (fiber-trunc m x)

  to-equiv
    : ∀ {v} {X : Type v}
    → (m : hMap u X 0) → is-equiv (value m)
  to-equiv m .eqv-fibers = fiber-trunc m

  to-embedding
    : ∀ {v} {X : Type v}
    → (m : hMap u X 1) → is-embedding (value m)
  to-embedding m = fiber-trunc m
```


## Distinguished elements

`η` is characterized by domain contractibility, `⊥ₗ` by domain
emptiness via the general `from-empty` constructor.

```agda
  η : ∀ {v n} {X : Type v}
    → is-hlevel (S n) X → X → hMap u X n
  η hl x .is-defined = Lift _ ⊤
  η hl x .value _    = x
  η {n = n} hl x .fiber-trunc y = Σ-is-hlevel n
    (is-contr→is-hlevel n (Contr (liftℓ tt) λ { (liftℓ tt) → refl }))
    (λ _ → Path-is-hlevel hl)

  from-empty
    : ∀ {v m} {X : Type v} {D : Type u}
    → (D → ⊥) → hMap u X (S m)
  from-empty e .is-defined    = _
  from-empty e .value d       = ex-falso (e d)
  from-empty e .fiber-trunc y =
    is-prop→is-hlevel-suc λ (d , _) → ex-falso (e d)

  ⊥ₗ : ∀ {v m} {X : Type v} → hMap u X (S m)
  ⊥ₗ = from-empty lower
```


## Partial equivalences

A partial equivalence is an embedding (hMap at level 1) together
with a propositional classifier that gates contractibility of
fibers. When the classifier holds at a point, the fiber there is
inhabited and therefore contractible (prop + inhabited = contr).

```agda
record PartialEquiv (u : Level) {v : Level}
  (X : Type v) : Type (u ₊ ⊔ v) where
  no-eta-equality
  field
    map             : hMap u X 1
    classifier      : X → Type u
    classifier-prop : (x : X) → is-prop (classifier x)
    witness
      : (x : X) → classifier x
      → fiber (value map) x

{-# INLINE PartialEquiv.constructor #-}

module PartialEquiv-ops {u v} {X : Type v}
  (pe : PartialEquiv u X) where
  open PartialEquiv pe

  classified-contr
    : (x : X) → classifier x
    → is-contr (fiber (value map) x)
  classified-contr x c =
    prop-inhabited→is-contr
      (fiber-trunc map x)
      (PartialEquiv.witness pe x c)
```


## Derived operations on partial equivalences

Transport classified contractibility along a path in the
codomain.

```agda
  classified-transport
    : {x y : X} → x ≡ y
    → classifier x → is-contr (fiber (value map) y)
  classified-transport p cx =
    subst (λ z → is-contr (fiber (value map) z))
      p (classified-contr _ cx)
```

Transport a `PartialEquiv` along an equivalence on the
codomain. The new map composes the original embedding with
the equivalence forward map, the classifier pulls back
through the inverse, and the witness lifts through the
forward map.

```agda
  classified-equiv
    : ∀ {w} {Y : Type w}
    → X ≃ Y → PartialEquiv u Y
  classified-equiv e .PartialEquiv.map .is-defined =
    is-defined map
  classified-equiv e .PartialEquiv.map .value d =
    e.fwd (value map d)
    where module e = Equiv e
  classified-equiv e .PartialEquiv.map .fiber-trunc =
    ((value map , fiber-trunc map) ∙↪ equiv→embedding e) .snd
  classified-equiv e .PartialEquiv.classifier y =
    classifier (e.inv y)
    where module e = Equiv e
  classified-equiv e .PartialEquiv.classifier-prop y =
    classifier-prop (e.inv y)
    where module e = Equiv e
  classified-equiv e .PartialEquiv.witness y cy = d , q
    where
      module e = Equiv e
      w : fiber (value map) (e.inv y)
      w = PartialEquiv.witness pe (e.inv y) cy
      d : is-defined map
      d = w .fst
      q : e.fwd (value map d) ≡ y
      q = ap e.fwd (w .snd) ∙ e.counit y
```

Compose two classified contractibility results through a
dependent Sigma. Given a family of partial equivalences
indexed by the definedness predicate, if both the base
fiber and the dependent fiber are classified, the total
fiber is contractible via `Σ-contr-contr`.

```agda
  classified-Σ
    : ∀ {w} {B : is-defined map → Type w}
    → (pe-B : (d : is-defined map) → PartialEquiv u (B d))
    → (x : X) (cx : classifier x)
    → (bf : (d : is-defined map) → B d)
    → ( (d : is-defined map)
      → PartialEquiv.classifier (pe-B d) (bf d))
    → is-contr
        ( Σ (d , _) ∶ fiber (value map) x
        , fiber
            (value (PartialEquiv.map (pe-B d)))
            (bf d))
  classified-Σ pe-B x cx bf cbf =
    Σ-contr-contr (classified-contr x cx) λ fib →
      dep-contr (fib .fst) (cbf (fib .fst))
    where
      dep-contr
        : (d : is-defined map) → PartialEquiv.classifier (pe-B d) (bf d)
        → is-contr (fiber (value (PartialEquiv.map (pe-B d))) (bf d))
      dep-contr d cd =
        prop-inhabited→is-contr
          (fiber-trunc (PartialEquiv.map (pe-B d)) (bf d))
          (PartialEquiv.witness (pe-B d) (bf d) cd)
```
