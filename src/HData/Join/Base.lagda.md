Elimination principles and basic operations for the join.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Join.Base where

open import HData.Join.Type

open import Core.Type
open import Core.Base

private variable
  u v w : Level
  A A' : Type u
  B B' : Type v
```


## Recursion

```agda

rec : {A : Type u} {B : Type v} {X : Type w}
    → (l : A → X)
    → (r : B → X)
    → (p : (a : A) (b : B) → l a ≡ r b)
    → A ⋆ B → X
rec l r p (inl a)      = l a
rec l r p (inr b)      = r b
rec l r p (push a b i) = p a b i
```


## Dependent elimination

```agda

ind : {A : Type u} {B : Type v}
      {P : A ⋆ B → Type w}
    → (l : (a : A) → P (inl a))
    → (r : (b : B) → P (inr b))
    → (p : (a : A) (b : B)
      → PathP (λ i → P (push a b i)) (l a) (r b))
    → (x : A ⋆ B) → P x
ind l r p (inl a)      = l a
ind l r p (inr b)      = r b
ind l r p (push a b i) = p a b i
```


## Swap

The join is symmetric: `A ⋆ B → B ⋆ A`.

```agda

swap : {A : Type u} {B : Type v} → A ⋆ B → B ⋆ A
swap (inl a)      = inr a
swap (inr b)      = inl b
swap (push a b i) = push b a (~ i)
```


## Functorial map

```agda

map : {A : Type u} {A' : Type v}
      {B : Type u} {B' : Type v}
    → (A → A') → (B → B') → A ⋆ B → A' ⋆ B'
map f g (inl a)      = inl (f a)
map f g (inr b)      = inr (g b)
map f g (push a b i) = push (f a) (g b) i
```
