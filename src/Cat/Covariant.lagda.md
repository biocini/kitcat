Covariant families over virtual categories. A covariant family
assigns a type to each object and an action to each morphism,
functorially. The representable family `hom a _` is the
canonical example, with action given by `yon`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Virtual

module Cat.Covariant {o h} (C : category o h) where

open Virtual C

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Transport using (Singl-contr)
```

## The covariant record

A covariant family is a functor from C to types: a type family
with a functorial action. `act-id` says the identity acts
trivially, and `act-comp` says the action respects composition.

```agda
record covariant o' : Type₊ (o ⊔ h ⊔ o') where
  no-eta-equality
  field
    Fib : ob → Type o'
    act : ∀ {x y} → hom x y → Fib x → Fib y
    act-id : ∀ {x} (p : Fib x) → act idn p ≡ p
    act-comp
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        (p : Fib x)
      → act (f ⨾ g) p ≡ act g (act f p)
```


## Discrete transport

Every covariant family has contractible transport fibers: given
`f : hom x y` and `p : Fib x`, the pair `(act f p, refl)` is
the unique element of `Σ q ∶ Fib y , act f p ≡ q`.

```agda
  act-contr
    : ∀ {x y} (f : hom x y) (p : Fib x)
    → is-contr (Σ q ∶ Fib y , act f p ≡ q)
  act-contr f p = Singl-contr (act f p)
```


## The representable family

For a fixed object `a`, the family `x ↦ hom a x` is covariant
with action `yon f`. The identity law is `absorb-r` and the
composition law is `yon-composite`.

```agda
hom-cov : ob → covariant h
hom-cov a .covariant.Fib x = hom a x
hom-cov a .covariant.act f p = yon f _ p
hom-cov a .covariant.act-id p = absorb-r p
hom-cov a .covariant.act-comp f g p = yon-composite f g _ p
```
