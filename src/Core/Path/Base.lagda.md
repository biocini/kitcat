---
author: Lane Biocini
date: 2025-10
contents: Path algebra — symmetry, concatenation, squares, and coherences.
---

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Path.Base where

open import Core.Transport.Base
open import Core.Base
open import Core.Type
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Pointed
open import Core.Kan
open import Core.Sub

private
  variable
    u v : Level
    A : I → Type u

ap-comp : ∀ {u v} {A : Type u} {B : Type v} (f : A → B)
        {x y z : A} (p : x ≡ y) (q : y ≡ z)
        → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-comp f p q = ap fst
  (HComposite.unique refl (ap f p) (ap f q)
    (ap f (p ∙ q) , λ i j → f (cat.fill p q i j))
    (ap f p ∙ ap f q , cat.fill (ap f p) (ap f q)))

ap-∘ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
     (g : B → C) (f : A → B)
     {x y : A} (p : x ≡ y)
     → ap (λ a → g (f a)) p ≡ ap g (ap f p)
ap-∘ g f p = refl

ap-merge
  : ∀ {u v} {A : Type u} {B : Type v} (G : A → B) {a a' a'' : A} {w : B}
    (X : w ≡ G a) (p : a ≡ a') (e : a' ≡ a'')
  → (X ∙ ap G p) ∙ ap G e ≡ X ∙ ap G (p ∙ e)
ap-merge G X p e =
  sym (Path.assoc X (ap G p) (ap G e)) ∙ ap (X ∙_) (sym (ap-comp G p e))

Ω : ∀ {u} → Type* u → Type u
Ω (_ , a) = a ≡ a
{-# INLINE Ω #-}

Loop : ∀ {u} → Type* u → Type* u
Loop A .fst = Ω A
Loop A .snd = refl

infix 4 _≢_
_≢_ : {A : Type u} → A → A → Type u
x ≢ y = ¬ (x ≡ y)
```

## Cancellation

Left- and right-cancellation for `_∙_`, the transposition
`move-r` — from `p ∙ sym q ≡ r` conclude `p ≡ r ∙ q` — and the
conjugation cancellation: a loop `ζ` conjugated into a composite
that agrees with the plain composite must be trivial. `move-r`
leans on the definitional involution `sym (sym q) ≐ q` to convert
the cancellation endpoint (the involution is pinned by
`Core.Groupoid.op-invol`).

```agda
cancell
  : ∀ {u} {A : Type u} {a b c : A}
  → (p : a ≡ b) (s : b ≡ c)
  → sym p ∙ p ∙ s ≡ s
cancell p s =
  Path.assoc (sym p) p s
  ∙ ap (_∙ s) (Path.invl p)
  ∙ Path.unitl s

cancelr
  : ∀ {u} {A : Type u} {a b c : A}
  → (q : b ≡ c) (t : a ≡ b)
  → (t ∙ q) ∙ sym q ≡ t
cancelr q t =
  sym (Path.assoc t q (sym q))
  ∙ ap (t ∙_) (Path.invr q)
  ∙ Path.unitr t

move-r
  : ∀ {u} {A : Type u} {a b c : A}
  → (p : a ≡ b) (q : c ≡ b) (r : a ≡ c)
  → p ∙ sym q ≡ r → p ≡ r ∙ q
move-r p q r h =
  sym (cancelr (sym q) p) ∙ ap (_∙ q) h

conj-cancel
  : ∀ {u} {A : Type u} {a b c : A}
  → (p : a ≡ b) (q : b ≡ c) (ζ : b ≡ b)
  → p ∙ q ≡ p ∙ ζ ∙ q
  → ζ ≡ refl
conj-cancel p q ζ h =
  sym (cancelr q ζ)
  ∙ ap (_∙ sym q) (sym cancel-left)
  ∙ Path.invr q
  where
    cancel-left : q ≡ ζ ∙ q
    cancel-left =
      sym (cancell p q)
      ∙ ap (sym p ∙_) h
      ∙ cancell p (ζ ∙ q)
```
