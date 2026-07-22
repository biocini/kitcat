Lane Biocini
July 2026

Pullbacks over a `Cat.Type` category.

A pullback of `f : hom A C` and `g : hom B C` consists of projections
`p₁ : hom P A` and `p₂ : hom P B` satisfying the commuting square
`p₁ ⨾ f ≡ p₂ ⨾ g`, together with a conditional universal property: for
any `h₁ : hom X A` and `h₂ : hom X B` with `h₁ ⨾ f ≡ h₂ ⨾ g`, the
product-shaped cone is contractible. The cone type is identical to
`product-cone`; the precondition `h₁ ⨾ f ≡ h₂ ⨾ g` is the only
difference from products.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Limits.Pullback where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base using (contr-ind)

open import Cat.Type
open import Cat.Base
open import Cat.Limits.Product

module _ {o h} (C : category o h) where
  open category C
  open theory C

  pullback-cone
    : ∀ {A B P : ob} → hom P A → hom P B
    → (X : ob) → hom X A → hom X B → Type (o ⊔ h)
  pullback-cone = product-cone C

  is-pullback
    : ∀ {A B Cc P : ob}
      (p₁ : hom P A) (p₂ : hom P B)
      (f : hom A Cc) (g : hom B Cc)
    → Type (o ⊔ h)
  is-pullback p₁ p₂ f g =
    (p₁ ⨾ f ≡ p₂ ⨾ g)
    × (∀ {X} (h₁ : hom X _) (h₂ : hom X _)
       → h₁ ⨾ f ≡ h₂ ⨾ g
       → is-contr (pullback-cone p₁ p₂ X h₁ h₂))

  module Pullback
    {A B Cc P : ob}
    {p₁ : hom P A} {p₂ : hom P B}
    {f : hom A Cc} {g : hom B Cc}
    (pb : is-pullback p₁ p₂ f g)
    where

    square : p₁ ⨾ f ≡ p₂ ⨾ g
    square = pb .fst

    pb-med
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → hom X P
    pb-med h₁ h₂ q = pb .snd h₁ h₂ q .center .fst

    pb-factors₁
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → pb-med h₁ h₂ q ⨾ p₁ => h₁
    pb-factors₁ h₁ h₂ q = pb .snd h₁ h₂ q .center .snd .fst

    pb-factors₂
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → pb-med h₁ h₂ q ⨾ p₂ => h₂
    pb-factors₂ h₁ h₂ q = pb .snd h₁ h₂ q .center .snd .snd

    pb-ind
      : ∀ {u X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → (Q : (m : hom X P)
           → m ⨾ p₁ => h₁ → m ⨾ p₂ => h₂
           → Type u)
      → Q (pb-med h₁ h₂ q)
          (pb-factors₁ h₁ h₂ q)
          (pb-factors₂ h₁ h₂ q)
      → ∀ m α β → Q m α β
    pb-ind h₁ h₂ q Q base m α β =
      contr-ind (pb .snd h₁ h₂ q)
        (λ where (m , α , β) → Q m α β)
        base (m , α , β)

    pb-β₁
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → pb-med h₁ h₂ q ⨾ p₁ ≡ h₁
    pb-β₁ h₁ h₂ q = cast-path (pb-factors₁ h₁ h₂ q)

    pb-β₂
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → pb-med h₁ h₂ q ⨾ p₂ ≡ h₂
    pb-β₂ h₁ h₂ q = cast-path (pb-factors₂ h₁ h₂ q)

    pb-η
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → (m : hom X P)
      → m ⨾ p₁ => h₁ → m ⨾ p₂ => h₂
      → pb-med h₁ h₂ q ≡ m
    pb-η h₁ h₂ q =
      pb-ind h₁ h₂ q
        (λ m _ _ → pb-med h₁ h₂ q ≡ m) refl
```
