Lane Biocini
July 2026

Terminal and initial objects over a
`Bb.CatsWithExplicitInterchange.Type` category.

The simplest universal properties: `hom X T` is contractible for all
`X` (terminal), or `hom I X` is contractible for all `X` (initial).
The induction principle `!-ind` says: to prove `P` for all morphisms
into `T`, prove it for the canonical one. The uniqueness rule
`!-unique` follows from induction at `P = (! ≡_)`.

Duality is definitional: a terminal object of `C` is an initial
object of `op C`, and conversely.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Limits.Terminal where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base using (contr-ind)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Op

module _ {o h} (C : category o h) where
  open category C

  is-terminal : ob → Type (o ⊔ h)
  is-terminal T = ∀ X → is-contr (hom X T)

  module Terminal {T : ob} (term : is-terminal T) where
    ! : ∀ {X} → hom X T
    ! = term _ .center

    !-ind
      : ∀ {u} {X : ob} (P : hom X T → Type u)
      → P !
      → ∀ f → P f
    !-ind = contr-ind (term _)

    !-unique : ∀ {X} (f : hom X T) → ! ≡ f
    !-unique = !-ind (! ≡_) refl

  is-initial : ob → Type (o ⊔ h)
  is-initial I = ∀ X → is-contr (hom I X)

  module Initial {I : ob} (init : is-initial I) where
    ¡ : ∀ {X} → hom I X
    ¡ = init _ .center

    ¡-ind
      : ∀ {u} {X : ob} (P : hom I X → Type u)
      → P ¡
      → ∀ f → P f
    ¡-ind P = contr-ind (init _) P

    ¡-unique : ∀ {X} (f : hom I X) → ¡ ≡ f
    ¡-unique = ¡-ind (¡ ≡_) refl

module _ {o h} (C : category o h) where

  terminal-dual : ∀ {T : category.ob C}
                → is-terminal C T ≡ is-initial (op C) T
  terminal-dual = refl

  initial-dual : ∀ {I : category.ob C}
               → is-initial C I ≡ is-terminal (op C) I
  initial-dual = refl
```
