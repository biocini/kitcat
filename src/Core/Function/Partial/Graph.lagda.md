Lane Biocini, February 2026. Graph-based encoding of partial
functions, parameterized by h-level.

Adapted from Escardo's TypeTopology `MGS.Partial-Functions` (2019).
Where the lifting monad in `Core.Function.Partial` represents partial
functions via a definedness proposition plus a function on it, this
module characterizes partial functions by their *graph*: a partial
function is a relation `R` whose total space `Sigma (A x) (R x)` is
n-truncated at each fiber.

The h-level parameter `n` controls the truncation requirement on
fibers. At n = 1 (propositional), this recovers the standard notion
of a partial function whose graph is single-valued. Higher levels
allow graph-based encodings where fibers carry additional structure.

The graph encoding naturally handles dependent partial functions
`Πₙ n A`, where the lifting approach would need
`(x : X) -> L (A x)`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Function.Partial.Graph where

open import Core.Type
open import Core.Base
open import Core.Data.Nat.Type
open import Core.Data.Sigma
open import Core.Equiv.Base using (_≃_; is-contr-equiv; iso→equiv)
open import Core.Kan using (Σ-contr-contr)
open import Core.Trait.Trunc using (is-hlevel; is-contr→is-hlevel)
open import Core.Transport.Base using (Singl-contr)

private variable
  u v : Level
```


## H-level parameterized partial dependent function type

A partial dependent function from `X` into a family `A` at h-level
`n` is a relation `R : (x : X) -> A x -> Type v` such that for each
`x`, the type `Sigma (A x) (R x)` is n-truncated.

```agda
Πₙ : {X : Type u} → Nat → (X → Type v) → Type (u ⊔ v ₊)
Πₙ {u} {v} {X} n A =
  Σ R ∶ ((x : X) → A x → Type v)
  , ((x : X) → is-hlevel n (Σ a ∶ A x , R x a))
```


## Propositional partial dependent function type

The standard case: fibers are propositions.

```agda
Πₚ : {X : Type u} → (X → Type v) → Type (u ⊔ v ₊)
Πₚ = Πₙ 1
```


## Non-dependent partial function type

The suffix `g` distinguishes from the lifting-based `_⇀_` in
`Core.Function.Partial`.

```agda
infixr 0 _⇀ᵍ_

_⇀ᵍ_ : Type u → Type v → Type (u ⊔ v ₊)
X ⇀ᵍ Y = Πₚ {X = X} (λ _ → Y)
```


## Projections

```agda
module Πₙ {u v} {n : Nat} {X : Type u} {A : X → Type v} where
  graph : Πₙ n A → (x : X) → A x → Type v
  graph (R , _) = R
  {-# INLINE graph #-}

  is-defined : Πₙ n A → X → Type v
  is-defined (R , _) x = Σ a ∶ A x , R x a
  {-# INLINE is-defined #-}

  definedness-hlevel
    : (f : Πₙ n A) (x : X)
    → is-hlevel n (is-defined f x)
  definedness-hlevel (_ , σ) = σ
  {-# INLINE definedness-hlevel #-}

  _[_,_] : (f : Πₙ n A) (x : X) → is-defined f x → A x
  _[_,_] _ _ (a , _) = a
  {-# INLINE _[_,_] #-}
```


## Kleene equality

Two partial dependent functions are Kleene-equal when they agree on
definedness (up to logical equivalence) and produce equal values
wherever both are defined.

```agda
  _≡ₖ_ : Πₙ n A → Πₙ n A → Type (u ⊔ v)
  f ≡ₖ g = ∀ x
    → (is-defined f x → is-defined g x)
    × (is-defined g x → is-defined f x)
    × ((i : is-defined f x) (j : is-defined g x)
        → f [ x , i ] ≡ g [ x , j ])

  infix 4 _≡ₖ_
```


## Totality

```agda
  is-total : Πₙ n A → Type (u ⊔ v)
  is-total f = ∀ x → is-defined f x
```


## Backward-compatible propositional projections

```agda
module Πₚ {u v} {X : Type u} {A : X → Type v} where
  open Πₙ {n = 1} {X = X} {A = A} public
```


## Embedding total functions

Given `f : (x : X) -> A x`, the graph `R x a = (f x == a)` makes
`Sigma a, f x == a` contractible by singleton contractibility, hence
n-truncated for any n.

```agda
from-total
  : ∀ {u v n} {X : Type u} {A : X → Type v}
  → ((x : X) → A x) → Πₙ n A
from-total {v = v} {n = n} {X = X} {A = A} f =
  R , σ where
  R : (x : X) → A x → Type v
  R x a = f x ≡ a

  σ : (x : X) → is-hlevel n (Σ a ∶ A x , R x a)
  σ x = is-contr→is-hlevel n (Singl-contr (f x))
```


## Totality of embedded functions

A function embedded via `from-total` is always total, witnessed by
reflexivity.

```agda
from-total-is-total
  : ∀ {u v n} {X : Type u} {A : X → Type v}
  → (f : (x : X) → A x)
  → Πₙ.is-total (from-total {n = n} f)
from-total-is-total f x = f x , refl
```

Relational composition of graph relations. The composite
`(R ⨾ᵍ T) x z` witnesses that some intermediate `y` exists
with `R x y` and `T y z` both inhabited.

```agda
infixr 9 _⨾ᵍ_

_⨾ᵍ_
  : ∀ {u v w} {X : Type u} {Y : Type v}
    {Z : Type w}
  → (X → Y → Type v) → (Y → Z → Type w)
  → X → Z → Type (v ⊔ w)
(R ⨾ᵍ T) x z = Σ λ y → R x y × T y z
```

## Relational composition

Composing two relations whose fibers are each contractible
yields a relation with contractible fibers. The proof rearranges
the nested Σ-type into a form where `Σ-contr-contr` applies,
then transports back along the rearrangement equivalence.

```agda
contr-chain
  : ∀ {u v w} {X : Type u} {Y : Type v} {Z : Type w}
  → {R : X → Y → Type v} {T : Y → Z → Type w}
  → ((x : X) → is-contr (Σ (R x)))
  → ((y : Y) → is-contr (Σ (T y)))
  → (x : X)
  → is-contr (Σ ((R ⨾ᵍ T) x))
contr-chain {Y = Y} {R = R} {T} cR cT x =
  is-contr-equiv shuffle
    (Σ-contr-contr (cR x) λ (y , _) → cT y)
  where
    Flat = Σ (λ (yr : Σ {A = Y} (R x)) → Σ (T (yr .fst)))

    shuffle : Σ (λ z → Σ λ y → R x y × T y z) ≃ Flat
    shuffle = iso→equiv
      (λ (z , y , r , s) → (y , r) , z , s)
      (λ ((y , r) , z , s) → z , y , r , s)
      (λ _ → refl) (λ _ → refl)
```

Composing two `Πₙ 0` partial functions via `contr-chain`.
Both `Y` and `Z` must live in the same universe so that the
relational composite `R ⨾ᵍ T` lands back in `Type v`.

```agda
Πₙ-comp
  : ∀ {u v} {X : Type u} {Y Z : Type v}
  → Πₙ {X = X} 0 (λ _ → Y)
  → Πₙ {X = Y} 0 (λ _ → Z)
  → Πₙ {X = X} 0 (λ _ → Z)
Πₙ-comp (R , cR) (T , cT) =
  R ⨾ᵍ T , contr-chain cR cT
```
