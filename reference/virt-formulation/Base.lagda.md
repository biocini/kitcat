Lane Biocini

```
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Virt.Base where

open import Core.Type
open import Core.Base
open import Core.Data
open import Core.HLevel
open import Core.Cast

record Virtual {u} (Γ : Type u) : Typeω where
  field
    l₀ l₁ l₂ : Level
    obj : Γ → Type l₀
    hom : ∀ x → obj x → obj x → Type l₁
    hom2 : ∀ x {a b : obj x} → hom x a b → hom x a b → Type l₂
    cut : ∀ {x} {a b c : obj x} → hom x a b → hom x b c → hom x a c

    -- Composite coherence (forward and opposite share center ceqv)
    cut-unique : ∀ x {a b c : obj x} {f : hom x a b} {g : hom x b c}
               → is-prop (Σ s ∶ hom x a c , hom2 x (cut f g) s)
    cocut-unique : ∀ x {a b c : obj x} {f : hom x a b} {g : hom x b c}
                 → is-prop (Σ t ∶ hom x a c , hom2 x t (cut f g))

    -- 2-cell composition structure
    ceqv : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c}
         → hom2 x (cut f g) (cut f g)
    hcut : ∀ {x} {a b c : obj x} {e1 d1 : hom x a b} {e2 d2 : hom x b c}
         → hom2 x e1 d1 → hom2 x e2 d2 → hom2 x (cut e1 e2) (cut d1 d2)
    vcut : ∀ {x} {a b : obj x} {f g h : hom x a b}
         → hom2 x f g → hom2 x g h → hom2 x f h

    -- ceqv is unital with respect to 2-cell composites
    ceqv-divl : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c} {k : hom x a c}
              → (α : hom2 x (cut f g) k)
              → is-contr (Σ β ∶ hom2 x (cut f g) k , vcut (ceqv {f = f} {g}) β ≡ α)
    ceqv-divr : ∀ {x} {a b c : obj x} {h : hom x a c} {f : hom x a b} {g : hom x b c}
              → (α : hom2 x h (cut f g))
              → is-contr (Σ β ∶ hom2 x h (cut f g) , vcut β (ceqv {f = f} {g}) ≡ α)
    c-wlinear : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c} {s : hom x a c}
              → (α : hom2 x (cut f g) s) → vcut ceqv (vcut ceqv α) ≡ vcut ceqv α
    c-wthunkable : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c} {s : hom x a c}
                 → (α : hom2 x s (cut f g)) → vcut (vcut α ceqv) ceqv ≡ vcut α ceqv

  -- TODO: implement singl-unique lemma or find equivalent
  -- vcut-unique : ∀ {x} {a b : obj x} {f g h : hom x a b}
  --             → {α : hom2 x f g} {β : hom2 x g h}
  --             → is-prop (Σ s ∶ hom2 x f h , vcut α β ≡ s)
  -- vcut-unique = singl-unique

module _ {u} {Γ : Type u} ⦃ V : Virtual Γ ⦄ where
  open Virtual V
  infixr -1 1cell-syntax 2cell-syntax term-syntax

  ob : Γ → Type l₀
  ob = obj

  term-syntax : ∀ Γ → Π ob → ob Γ
  term-syntax C b = b C
  syntax term-syntax 𝓒 (λ x → a) = x ∶ 𝓒 ⊢ a

  1cell-syntax : ∀ C → obj C → obj C → Type l₁
  1cell-syntax = hom
  syntax 1cell-syntax 𝓒 a b = a ↦ b ∶ 𝓒

  2cell-syntax : ∀ C {x y} → x ↦ y ∶ C → x ↦ y ∶ C → Type l₂
  2cell-syntax = hom2
  syntax 2cell-syntax 𝓒 f g = f ⇒ g ∶ 𝓒

  module _ {C : Γ} where
    private
      infix 6 _~>_ _=>_
      _~>_ = hom C
      _=>_ = hom2 C
      _⨾_ = cut
      _⊚_ = vcut; infixr 9 _⨾_ _⊚_
      _●_ = hcut; infixr 8 _●_

    cast-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
              → f ⨾ g => s → f ⨾ g ≡ s
    cast-path {f} {g} {s} α = ap fst (cut-unique C ((f ⨾ g) , ceqv) (s , α))

    cast-pathp : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
               → (α : f ⨾ g => s)
               → PathP (λ i → (f ⨾ g) => cast-path α i) ceqv α
    cast-pathp {f} {g} {s} α = ap snd (cut-unique C ((f ⨾ g) , ceqv) (s , α))
