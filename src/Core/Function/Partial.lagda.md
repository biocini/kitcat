Lane Biocini, February 2026. The lifting monad specialized at
h-level 1 (propositional definedness).

Adapted from Escardo's TypeTopology `Lifting.Construction` and
`Lifting.Monad`. The `is-defined` field is a bare `Type u` with a
separate `def-prop` witness, rather than a bundled `nType`. This
keeps the record lightweight and avoids the `nType` indirection for
the standard case of propositional partial elements.

The h-level-parameterized version lives in
`Core.Function.Partial.Graded` as `hLiftM`.

```agda
{-# OPTIONS --safe --cubical --no-guardedness --no-sized-types #-}

module Core.Function.Partial where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Dec.Type using (Dec; yes; no)
open import Core.Data.Maybe using (Maybe; nothing; just)
open import Core.HLevel.Base using (Σ-is-prop)
open import Core.Kan using (hcom)

private variable
  u v w : Level
```


## The lifting

`LiftM u X` classifies partial elements of `X` with propositional
definedness. A value bundles a type `P : Type u` with a proof that
`P` is a proposition and a map `P → X`.

```agda
record LiftM u {v : Level} (X : Type v) : Type (u ₊ ⊔ v) where
  no-eta-equality
  field
    is-defined : Type u
    def-prop   : is-prop is-defined
    value      : is-defined → X

open LiftM public
{-# INLINE LiftM.constructor #-}
```


## Distinguished elements

The unit `η` embeds `X` into `LiftM u X` via `Lift u ⊤`, which is
a proposition (being contractible). Bottom `⊥ₗ` uses the empty
type, which is trivially propositional.

```agda
module _ {u : Level} where
  ⊥-prop : is-prop (Lift u ⊥)
  ⊥-prop (liftℓ e) = ex-falso e

  Lift-⊤-prop : is-prop (Lift u ⊤)
  Lift-⊤-prop (liftℓ tt) (liftℓ tt) = refl

  η : ∀ {v} {X : Type v} → X → LiftM u X
  η x .is-defined = Lift _ ⊤
  η x .def-prop   = Lift-⊤-prop
  η x .value _    = x

  ⊥ₗ : ∀ {v} {X : Type v} → LiftM u X
  ⊥ₗ .is-defined = Lift _ ⊥
  ⊥ₗ .def-prop   = ⊥-prop
  ⊥ₗ .value e    = ex-falso (e .lower)
```


## Functorial action

Post-compose the value function. The definedness type and its
propositionality proof are unchanged.

```agda
LiftM-map
  : ∀ {u v w} {A : Type v} {B : Type w}
  → (A → B) → LiftM u A → LiftM u B
LiftM-map f l .is-defined = is-defined l
LiftM-map f l .def-prop   = def-prop l
LiftM-map f l .value      = f ∘ value l
```


## Kleisli extension

Given `f : A → LiftM u B`, the extension `f ♯` takes a partial
`a : LiftM u A` and produces a partial `b : LiftM u B` that is
defined when `a` is defined and `f (value a p)` is also defined.
The definedness type is a Σ of two propositions, hence propositional.

```agda
_♯ : ∀ {u v w} {A : Type v} {B : Type w}
   → (A → LiftM u B) → LiftM u A → LiftM u B
(f ♯) a .is-defined =
  Σ p ∶ is-defined a , is-defined (f (value a p))
(f ♯) a .def-prop =
  Σ-is-prop (def-prop a)
    (λ p → def-prop (f (value a p)))
(f ♯) a .value (p , d) =
  value (f (value a p)) d
```


## Join

The monadic join flattens `LiftM u (LiftM u X)` to `LiftM u X`.
It is the Kleisli extension of the identity.

```agda
μ : ∀ {u v} {X : Type v}
  → LiftM u (LiftM u X) → LiftM u X
μ = id ♯
```


## Partial function type

A partial function from `A` to `B` is a total function from `A`
into the lifting of `B`.

```agda
infixr 0 _⇀_

_⇀_ : Type u → Type v → Type (u ⊔ w ₊ ⊔ v)
_⇀_ {w = w} A B = A → LiftM w B
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

Conversion between `Maybe` and the lifting, mediated by
decidability of definedness.

```agda
module _ {u : Level} {v : Level} {B : Type v} where

  from-maybe : Maybe B → LiftM u B
  from-maybe nothing  = ⊥ₗ
  from-maybe (just b) = η b

  to-maybe : (l : LiftM u B) → Dec (is-defined l) → Maybe B
  to-maybe l (yes d) = just (value l d)
  to-maybe l (no _)  = nothing
```


