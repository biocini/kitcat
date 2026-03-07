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
open import Core.Transport using (Singl-contr)
open import Core.Trait.Trunc using (is-hlevel; is-contr→is-hlevel)

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
module Πₙ-mod {u v} {n : Nat} {X : Type u} {A : X → Type v} where
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
module Πₚ-mod {u v} {X : Type u} {A : X → Type v} where
  open Πₙ-mod {n = 1} {X = X} {A = A} public
```


## Embedding total functions

Given `f : (x : X) -> A x`, the graph `R x a = (f x == a)` makes
`Sigma a, f x == a` contractible by singleton contractibility, hence
n-truncated for any n.

```agda
from-total
  : ∀ {u v n} {X : Type u} {A : X → Type v}
  → ((x : X) → A x) → Πₙ n A
from-total {n = n} f = R , σ where
  R : (_ : _) → _ → _
  R x a = f x ≡ a

  σ : (_ : _) → is-hlevel n _
  σ x = is-contr→is-hlevel n (Singl-contr (f x))
```


## Totality of embedded functions

A function embedded via `from-total` is always total, witnessed by
reflexivity.

```agda
from-total-is-total
  : ∀ {u v n} {X : Type u} {A : X → Type v}
  → (f : (x : X) → A x)
  → Πₙ-mod.is-total (from-total {n = n} f)
from-total-is-total f x = f x , refl
```
