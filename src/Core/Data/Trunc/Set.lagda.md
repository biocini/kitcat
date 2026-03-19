Set truncation as a higher inductive type.

The set truncation `∥ A ∥₀` of a type `A` freely forces `A` to be a
set, providing the universal map into sets. This is the 0-truncation
in the sense of HoTT: it identifies all parallel paths, collapsing
higher homotopy structure while preserving the points and their
equalities up to h-level 2.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Trunc.Set where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma using (snd)
open import Core.Kan
open import Core.Transport.Base
open import Core.Transport.Properties
open import Core.Equiv.Base
open import Core.HLevel.Base using (is-set→SquareP)

private variable
  u v : Level
  A B : Type u

```


## The set truncation HIT

The set truncation has two constructors: `inc` embeds elements and
`squash₀` forces the result to be a set.

```agda

data ∥_∥₀ {u} (A : Type u) : Type u where
  inc      : A → ∥ A ∥₀
  squash₀  : is-set ∥ A ∥₀

infix 5 ∥_∥₀

```


## H-level

```agda

∥₀-is-set : is-set ∥ A ∥₀
∥₀-is-set = squash₀

```


## Elimination principles

### Recursion (non-dependent elimination)

To define a function out of a set truncation into a set, it suffices
to give a function on the underlying type.

```agda

∥₀-rec : {B : Type v} → is-set B → (A → B) → ∥ A ∥₀ → B
∥₀-rec B-set f (inc a) = f a
∥₀-rec B-set f (squash₀ x y p q i j) =
  B-set (go x) (go y) (ap go p) (ap go q) i j where
    go = ∥₀-rec B-set f

```


### Induction (dependent elimination)

For dependent elimination, the type family must land in sets.

```agda

∥₀-elim : {B : ∥ A ∥₀ → Type v}
         → ((x : ∥ A ∥₀) → is-set (B x))
         → ((a : A) → B (inc a))
         → (x : ∥ A ∥₀) → B x
∥₀-elim B-set f (inc a) = f a
∥₀-elim {B = B} B-set f (squash₀ x y p q i j) =
  is-set→SquareP (λ i j → B (squash₀ x y p q i j))
    (λ i j → B-set (squash₀ x y p q i j))
    (ap go p) refl (ap go q) refl i j
  where
    go = ∥₀-elim B-set f

```


## Functorial action

```agda

∥₀-map : (A → B) → ∥ A ∥₀ → ∥ B ∥₀
∥₀-map f (inc x) = inc (f x)
∥₀-map f (squash₀ x y p q i j) =
  squash₀ (∥₀-map f x) (∥₀-map f y)
    (ap (∥₀-map f) p) (ap (∥₀-map f) q) i j

```


## Idempotency

Set truncation of a set is equivalent to itself: `inc` is an
equivalence when the domain is already a set.

```agda

∥₀-idempotent : is-set A → is-equiv (inc {A = A})
∥₀-idempotent {A = A} A-set = iso→equiv inc out out-inc inc-out .snd
  where
    out : ∥ A ∥₀ → A
    out = ∥₀-rec A-set id

    out-inc : (a : A) → out (inc a) ≡ a
    out-inc _ = refl

    inc-out : (x : ∥ A ∥₀) → inc (out x) ≡ x
    inc-out = ∥₀-elim (λ x → is-prop→is-set (squash₀ (inc (out x)) x))
      λ _ → refl

```
