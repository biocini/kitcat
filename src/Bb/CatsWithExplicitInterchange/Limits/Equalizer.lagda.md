Lane Biocini
July 2026

Equalizers over a `Bb.CatsWithExplicitInterchange.Type` category.

Given `f, g : hom A B`, an equalizer `e : hom E A` satisfies
`e ⨾ f ≡ e ⨾ g` and has a conditional universal property: for any
`h' : hom X A` with `h' ⨾ f ≡ h' ⨾ g`, the cone
`Σ m ∶ hom X E , (m ⨾ e => h')` is contractible. The precondition
`h' ⨾ f ≡ h' ⨾ g` gates access to the mediating morphism.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Limits.Equalizer where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base using (contr-ind)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Base

module _ {o h} (C : category o h) where
  open category C
  open theory C

  equalizer-cone
    : ∀ {A E : ob} → hom E A
    → (X : ob) → hom X A → Type (o ⊔ h)
  equalizer-cone {E = E} e X h' = Sigma (hom X E) λ m → m ⨾ e => h'

  is-equalizer
    : ∀ {A B E : ob}
      (f g : hom A B) (e : hom E A)
    → Type (o ⊔ h)
  is-equalizer f g e =
    (e ⨾ f ≡ e ⨾ g)
    × (∀ {X} (h' : hom X _) → h' ⨾ f ≡ h' ⨾ g
       → is-contr (equalizer-cone e X h'))

  module Equalizer
    {A B E : ob} {f g : hom A B} {e : hom E A}
    (eq : is-equalizer f g e)
    where

    equalizes : e ⨾ f ≡ e ⨾ g
    equalizes = eq .fst

    eq-med
      : ∀ {X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → hom X E
    eq-med h' p = eq .snd h' p .center .fst

    eq-factors
      : ∀ {X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → eq-med h' p ⨾ e => h'
    eq-factors h' p = eq .snd h' p .center .snd

    eq-ind
      : ∀ {u X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → (Q : (m : hom X E) → m ⨾ e => h' → Type u)
      → Q (eq-med h' p) (eq-factors h' p)
      → ∀ m α → Q m α
    eq-ind h' p Q base m α =
      contr-ind (eq .snd h' p)
        (λ where (m , α) → Q m α)
        base (m , α)

    eq-β
      : ∀ {X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → eq-med h' p ⨾ e ≡ h'
    eq-β h' p = cast-path (eq-factors h' p)

    eq-η
      : ∀ {X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → (m : hom X E)
      → m ⨾ e => h'
      → eq-med h' p ≡ m
    eq-η h' p = eq-ind h' p (λ m _ → eq-med h' p ≡ m) refl
```
