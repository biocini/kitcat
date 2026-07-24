Elimination for irrelevance.

An `Irr A` records a proof of `A` in an irrelevant field, so its content is
never available in a relevant position directly. When `A` is decidable, however,
the content is recoverable: decide `A`; a `yes` gives the proof outright, and a
`no` contradicts the stored one, which is legal because the contradiction is
formed under `forget`, an irrelevant context.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Irr where

open import Core.Type
open import Core.Data.Empty
open import Core.Data.Dec
open Dec

private variable
  u v : Level
  A B : Type u

map : (A → B) → Irr A → Irr B
map f (forget a) = forget (f a)

absurd : Irr ⊥ → A
absurd (forget ())

out-dec : Dec A → Irr A → A
out-dec (yes a) _ = a
out-dec (no ¬a) x = absurd (map ¬a x)

```
