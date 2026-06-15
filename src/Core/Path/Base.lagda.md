Lane Biocini
October 2025

Path algebra: symmetry, concatenation, squares, and coherences.

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
