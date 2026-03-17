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
open import Core.HLevel using (Σ-is-prop)
open import Core.Set using (propext)
open import Core.Transport.Base using (is-prop→PathP; coe01)
open import Core.Transport.Properties using (is-prop-is-prop)
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


## Path between LiftM values

Two `LiftM` values are equal when their definedness types are
logically equivalent and their value functions agree through the
equivalence. Propositional extensionality gives the type path.

```agda
LiftM-path
  : ∀ {u v} {X : Type v}
  → (l r : LiftM u X)
  → (p : is-defined l → is-defined r)
  → (q : is-defined r → is-defined l)
  → (∀ d → value l d ≡ value r (p d))
  → l ≡ r
LiftM-path l r p q coh i .is-defined =
  propext (def-prop l) (def-prop r) p q i
LiftM-path l r p q coh i .def-prop =
  is-prop→PathP
    (λ i → is-prop-is-prop
      (propext (def-prop l) (def-prop r) p q i))
    (def-prop l) (def-prop r) i
LiftM-path l r p q coh i .value d =
  hcom (∂ i) λ where
    j (i = i0) → coh d (~ j)
    j (i = i1) → value r d
    j (j = i0) → value r
      (coe01 (λ i → propext (def-prop l) (def-prop r) p q i)
        i d)
```


## Monad laws

Each uses `LiftM-path` with the logical equivalence between
propositional definedness types. The value functions agree
definitionally in all cases.

```agda
♯-unitl
  : ∀ {u v w} {A : Type v} {B : Type w}
  → (f : A → LiftM u B) (a : A)
  → (f ♯) (η a) ≡ f a
♯-unitl f a = LiftM-path ((f ♯) (η a)) (f a)
  snd (λ d → liftℓ tt , d) (λ _ → refl)

♯-unitr
  : ∀ {u v} {A : Type v}
  → (a : LiftM u A)
  → (η ♯) a ≡ a
♯-unitr a = LiftM-path ((η ♯) a) a
  fst (λ d → d , liftℓ tt) (λ _ → refl)

♯-assoc
  : ∀ {u v w x} {A : Type v} {B : Type w} {C : Type x}
  → (a : LiftM u A)
    (f : A → LiftM u B)
    (g : B → LiftM u C)
  → (g ♯) ((f ♯) a) ≡ ((λ x → (g ♯) (f x)) ♯) a
♯-assoc a f g = LiftM-path
  ((g ♯) ((f ♯) a)) (((λ x → (g ♯) (f x)) ♯) a)
  (λ ((p , d) , gd) → p , d , gd)
  (λ (p , d , gd) → (p , d) , gd)
  (λ _ → refl)
```
