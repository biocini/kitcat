Lane Biocini, February 2026. The h-level-parameterized lifting
monad and partial function type.

Adapted from Escardo's TypeTopology `Lifting.Construction` and
`Lifting.Monad`, generalized from propositional definedness to
arbitrary h-level n. The `is-defined` field is an `nType u n`,
following Escardo's reformulation of the lifting via the subtype
classifier, generalized from propositions to arbitrary h-level.

The lifting is defined as a record to make the h-level parameter `n`
definitionally injective, which allows Agda to infer `n` from the
type when using projections and other operations.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Function.Partial where

open import Core.Type
open import Core.Base
open import Core.Transport.Base
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat.Type using (Nat; S)
open import Core.Data.Dec.Type using (Dec; yes; no)
open import Core.Data.Maybe using (Maybe; nothing; just)
open import Core.HLevel
  using ( is-hlevel; Σ-is-hlevel; is-contr→is-hlevel
        ; is-prop→is-hlevel-suc; nType )
open import Core.Equiv using (_≃_; iso→equiv)

open nType

private variable
  u v w : Level
```


## The lifting

`LiftM u X n` classifies partial elements of `X` whose definedness
predicate has h-level `n`. A value of type `LiftM u X n` bundles an
`nType u n` (a type `P` of h-level `n`) together with a map `P → X`,
so the element of `X` exists precisely when `P` is inhabited. The
universe level of the predicate is a separate parameter from the
codomain.

```agda
record LiftM u {v : Level} (X : Type v) (n : Nat) : Type (u ₊ ⊔ v) where
  no-eta-equality
  field
    is-defined : nType u n
    value      : ∣ is-defined ∣ → X

open LiftM public
{-# INLINE LiftM.constructor #-}

definedness-hlevel
  : ∀ {u v n} {X : Type v}
  → (l : LiftM u X n) → is-hlevel n (∣ is-defined l ∣)
definedness-hlevel l = is-tr (is-defined l)

definedness-is-prop
  : ∀ {u v} {X : Type v}
  → (l : LiftM u X 1) → is-prop (∣ is-defined l ∣)
definedness-is-prop l = is-tr (is-defined l)

definedness-trunc = definedness-hlevel
```


## Equivalence with the Sigma formulation

The record `LiftM u X n` is equivalent to the Sigma type
`Σ P : Type u, (P → X) × is-hlevel n P`.

```agda
LiftM-Σ : ∀ u {v} → Type v → Nat → Type (u ₊ ⊔ v)
LiftM-Σ u {v} X n = Σ P ∶ Type u , (P → X) × is-hlevel n P

LiftM≃Σ : ∀ {u v n} {X : Type v} → LiftM u X n ≃ LiftM-Σ u X n
LiftM≃Σ = iso→equiv fwd bwd sec ret where
  fwd : LiftM _ _ _ → LiftM-Σ _ _ _
  fwd l = ∣ is-defined l ∣ , value l , is-tr (is-defined l)

  bwd : LiftM-Σ _ _ _ → LiftM _ _ _
  bwd (P , v , h) .is-defined .∣_∣ = P
  bwd (P , v , h) .is-defined .is-tr = h
  bwd (P , v , h) .value = v

  sec : ∀ x → bwd (fwd x) ≡ x
  sec l i .is-defined .∣_∣ = ∣ is-defined l ∣
  sec l i .is-defined .is-tr = is-tr (is-defined l)
  sec l i .value = value l

  ret : ∀ y → fwd (bwd y) ≡ y
  ret _ = refl
```


## Distinguished elements

The unit `η` embeds `X` into `LiftM u X n` via the contractible type
`Lift u ⊤`. Since `Lift u ⊤` is contractible, it has h-level `n`
for any `n`.

Bottom `⊥ₗ` uses the empty type, which is a proposition. It works
for any h-level `S m` since propositions lift to higher h-levels.

```agda
module _ {u : Level} where
  ⊥-prop : is-prop (Lift u ⊥)
  ⊥-prop (liftℓ e) = ex-falso e

  η : ∀ {n v} {X : Type v} → X → LiftM u X n
  η x .is-defined .∣_∣ = Lift _ ⊤
  η x .is-defined .is-tr = is-contr→is-hlevel _
    (Contr (liftℓ tt) λ { (liftℓ tt) → refl })
  η x .value _ = x

  ⊥ₗ : ∀ {v m} {X : Type v} → LiftM u X (S m)
  ⊥ₗ .is-defined .∣_∣ = Lift _ ⊥
  ⊥ₗ .is-defined .is-tr = is-prop→is-hlevel-suc ⊥-prop
  ⊥ₗ .value e = ex-falso (e .lower)
```


## Functorial action

Post-compose the value function. The definedness nType is unchanged.

```agda
LiftM-map
  : ∀ {u v w n} {A : Type v} {B : Type w}
  → (A → B) → LiftM u A n → LiftM u B n
LiftM-map f l .is-defined = is-defined l
LiftM-map f l .value = f ∘ value l
```


## Kleisli extension

Given `f : A → LiftM u B n`, the extension `f ♯` takes a partial
`a : LiftM u A n` and produces a partial `b : LiftM u B n` that is
defined when `a` is defined and `f (value a p)` is also defined.
The definedness type `Σ (p : ∣ is-defined a ∣), ∣ is-defined (f (val p)) ∣`
has h-level `n` by closure of h-levels under Σ.

```agda
_♯ : ∀ {u v w n} {A : Type v} {B : Type w}
   → (A → LiftM u B n) → LiftM u A n → LiftM u B n
_♯ {n = n} f a .is-defined .∣_∣ =
  Σ p ∶ ∣ is-defined a ∣ , ∣ is-defined (f (value a p)) ∣
_♯ {n = n} f a .is-defined .is-tr =
  Σ-is-hlevel n (is-tr (is-defined a))
    (λ p → is-tr (is-defined (f (value a p))))
_♯ {n = n} f a .value (p , d) =
  value (f (value a p)) d
```


## Join

The monadic join flattens `LiftM u (LiftM u X n) n` to `LiftM u X n`.
It is the Kleisli extension of the identity.

```agda
μ : ∀ {u v n} {X : Type v}
  → LiftM u (LiftM u X n) n → LiftM u X n
μ = id ♯
```


## Partial function type

A partial function from `A` to `B` is a total function from `A` into
the lifting of `B`. The proposition universe `w` is a third level
parameter since it controls the size of the definedness predicate
independently of the domain and codomain. This uses h-level 1
(propositional definedness), the standard choice.

```agda
infixr 0 _⇀_

_⇀_ : Type u → Type v → Type (u ⊔ w ₊ ⊔ v)
_⇀_ {w = w} A B = A → LiftM w B 1
```


## Total function embedding

Every total function embeds into the partial function type via unit.

```agda
total
  : ∀ {u v w} {A : Type u} {B : Type v}
  → (A → B) → _⇀_ {w = w} A B
total f = η ∘ f
```


## Maybe bridge

Conversion between `Maybe` and the lifting, mediated by decidability
of definedness.

```agda
module _ {u : Level} {v : Level} {B : Type v} where

  from-maybe : Maybe B → LiftM u B 1
  from-maybe nothing  = ⊥ₗ
  from-maybe (just b) = η b

  to-maybe : (l : LiftM u B 1) → Dec (∣ is-defined l ∣) → Maybe B
  to-maybe l (yes d) = just (value l d)
  to-maybe l (no _)  = nothing
```
