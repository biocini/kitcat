
```
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Core.Synth where

open import Core.Base bb
open import Core.Data
open import Core.HLevel
open import Core.Kan
open import Core.Equiv
open import Core.Type
open import Core.Transport

record Cat u v : Type₊ (u ⊔ v) where
  field
    Ctx : Type u
    Ob : Ctx → Type v

  Term : Type (u ⊔ v)
  Term = Σ x ∶ Ctx , Ob x

  Hom : ∀ {Γ Δ} → Ob Γ → Ob Δ → Type v
  Hom {Γ} {Δ} x y = Σ f ∶ (Ob Γ → Ob Δ) , f x ≡ y ×

  _⨾_ : ∀ {Γ Δ ψ} {x : Ob Γ} {y : Ob Δ} {z : Ob ψ} → Hom x y → Hom y z → Hom x z
  (f , p) ⨾ (g , q) = g ∘ f , ap g p ∙ q

  -- idn : ∀ {Γ} {x : Ob Γ} → Hom x x
  -- idn .fst = id

  -- cut-contr : ∀ {Γ Δ ψ} {x : Ob Γ} {y : Ob Δ} {z : Ob ψ}
  --           → (f : Hom x y) (g : Hom y z)
  --           → is-contr (Σ s ∶ Hom x z , f ⨾ g ≡ s)
  -- cut-contr f g = Singl-contr (f ⨾ g)

open Cat

record Functor {u v w z} (C : Cat u v) (D : Cat w z) : Typeω where
  field
    ₀ : Term C → Term D
    -- ... more to go under
