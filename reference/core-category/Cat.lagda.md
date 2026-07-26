
```
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Core.Cat where

open import Core.Base
open import Core.Data
open import Core.HLevel
open import Core.Kan
open import Core.Equiv
open import Core.Type
open import Core.Transport

open import Lib.Graph.Base hiding (ob)
open import Lib.Graph.Reflexive.Base

singl-contr : ∀ {u} {A : Type u} {x : A} → is-contr (Σ y ∶ A , x ≡ y)
singl-contr {x} .center = x , refl
singl-contr {x} .paths (y , q) = λ i → (q i) , λ j → q (i ∧ j)

singl-unique : ∀ {u} {A : Type u} {x : A} → is-prop (Σ y ∶ A , x ≡ y)
singl-unique {A} {x} = is-contr→is-prop singl-contr

-- a semicategory-like structure without specifying any
-- particular coherences or composite structure other
-- than that attaching to composition itself. notice
-- that this is a displayed reflexive graph on the
-- type universe (see the definition of hom; the hom
-- type is implicitly displayed over 1-cells living in
-- the identity type on Γ; an isomorphism in Γ inhabits
-- an identity system local to the choice of Γ)
record Virtual {u} (Γ : Type u) : Typeω where
  field
    l₀ l₁ l₂ : Level
    obj : Γ → Type l₀
    hom : ∀ x → obj x → obj x → Type l₁
    hom2 : ∀ x {a b : obj x} → hom x a b → hom x a b → Type l₂
    cut : ∀ {x} {a b c : obj x} → hom x a b → hom x b c → hom x a c

    -- the following establishes that composition is coherent with respect
    -- the forward category as well as its opposite, having the same center
    -- ceqv
    cut-unique : ∀ x {a b c : obj x} {f : hom x a b} {g : hom x b c}
               → is-prop (Σ s ∶ hom x a c , hom2 x (cut f g) s)

    -- 2-cell composition structure
    ceqv : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c}
         → hom2 x (cut f g) (cut f g)
    hcut : ∀ {x} {a b c : obj x} {e1 d1 : hom x a b} {e2 d2 : hom x b c}
         → hom2 x e1 d1 → hom2 x e2 d2 → hom2 x (cut e1 e2) (cut d1 d2)
    vcut : ∀ {x} {a b : obj x} {f g h : hom x a b}
         → hom2 x f g → hom2 x g h → hom2 x f h

    -- we require that ceqv is unital with respect to 2-cell composites. this
    -- also entails that if 2-cells are a groupoid, and that ceqv will coincide
    -- with the canonical unit with free source and target symbols
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

  vcut-unique : ∀ {x} {a b : obj x} {f g h : hom x a b}
              → {α : hom2 x f g}
              → {β : hom2 x g h}
              → is-prop (Σ s ∶ hom2 x f h , vcut α β ≡ s)
  vcut-unique = singl-unique

module _ {u} {Γ : Type u} ⦃ V : Virtual Γ ⦄ where
