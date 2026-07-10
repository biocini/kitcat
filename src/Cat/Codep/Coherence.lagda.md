Lane Biocini
July 2026

Associativity and the Mac Lane pentagon for representable codependent
categories. Everything is purely associativity: it consumes only
`compose-contr` and `emb-comp`, never a unit law.

`assoc` is the projection of a path in the contractible triple-composite
fiber. The five pentagon faces (`face₁₂`, `face₂₃`, `face₁₄`, `face₄₅`,
`face₃₅`) each identify a fiber edge with a named associator via
`contr-face`; `hom-identity` is the fiber-level pentagon from
`coh-project`; `pentagon` assembles them into the named identity.

The inner-associator face `face₃₅` is where representability pays off:
`act = emb @ idn` makes the lift `Φ` commute with everything
definitionally, so the coherence collapses to `ap-comp`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Coherence where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using
  ( is-contr→is-prop; _∙_; contr-face; module Path
  ; pcom; module pcom; pcom→∙ )
open import Core.Transport.J using (subst)
open import Core.Path.Base using (ap-comp)
open import Core.Homotopy using (homotopy-natural)
open import Core.Coherence.Base using (coh-project)

open import Cat.Codep.Base
```

## Triple composite, assoc-σ, assoc

```agda
module Derived {o h} {ob : Type o}
  (R : codep-category {o} {h} ob) where
  open codep-category R

  E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w) → loose x w
  E₃ f g h = emb f · g · h

  E₃-contr : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
           → is-contr (fiber emb (E₃ f g h))
  E₃-contr f g h .center =
    (f ⨾ g) ⨾ h , emb-comp (f ⨾ g) h ∙ ap (_· h) (emb-comp f g)
  E₃-contr f g h .paths =
    is-contr→is-prop
      (subst (λ T → is-contr (fiber emb T))
        (ap (_· h) (emb-comp f g))
        (compose-contr (f ⨾ g) h)) _

  assoc-σ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
          → E₃-contr f g h .center
          ≡ (f ⨾ (g ⨾ h) , emb-comp f (g ⨾ h) ∙ ·-comp (emb f) g h)
  assoc-σ f g h = is-contr→is-prop (E₃-contr f g h) _ _

  assoc : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (assoc-σ f g h)
```

## The quadruple composite and the five faces

```agda
module Pentagon {o h} {ob : Type o}
  (R : codep-category {o} {h} ob) where
  open codep-category R
  open Derived R

  E₄ : ∀ {x y z w v}
       (f : hom x y) (g : hom y z) (h : hom z w) (k : hom w v)
     → loose x v
  E₄ f g h k = emb f · g · h · k

  E₄-contr
    : ∀ {x y z w v}
      (f : hom x y) (g : hom y z) (h : hom z w) (k : hom w v)
    → is-contr (fiber emb (E₄ f g h k))
  E₄-contr f g h k .center .fst = ((f ⨾ g) ⨾ h) ⨾ k
  E₄-contr f g h k .center .snd =
      emb-comp ((f ⨾ g) ⨾ h) k
    ∙ ap (_· k) (emb-comp (f ⨾ g) h)
    ∙ ap (λ o → o · h · k) (emb-comp f g)
  E₄-contr f g h k .paths =
    is-contr→is-prop
      (subst (λ T → is-contr (fiber emb T)) path₄
        (compose-contr ((f ⨾ g) ⨾ h) k)) _
    where
      path₄ : emb ((f ⨾ g) ⨾ h) · k ≡ E₄ f g h k
      path₄ = ap (_· k) (emb-comp (f ⨾ g) h)
            ∙ ap (λ o → o · h · k) (emb-comp f g)

  module PentagonFibers {x y z w v}
    (f : hom x y) (g : hom y z) (h : hom z w) (k : hom w v)
    where
    E₄c = E₄-contr f g h k

    pt₁ : fiber emb (E₄ f g h k)
    pt₁ = E₄c .center

    pt₂ : fiber emb (E₄ f g h k)
    pt₂ = (f ⨾ (g ⨾ h)) ⨾ k
        , emb-comp (f ⨾ (g ⨾ h)) k
        ∙ ap (_· k) (emb-comp f (g ⨾ h))
        ∙ ap (_· k) (·-comp (emb f) g h)

    pt₃ : fiber emb (E₄ f g h k)
    pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
        , emb-comp f ((g ⨾ h) ⨾ k)
        ∙ ·-comp (emb f) (g ⨾ h) k
        ∙ ap (_· k) (·-comp (emb f) g h)

    pt₄ : fiber emb (E₄ f g h k)
    pt₄ = (f ⨾ g) ⨾ (h ⨾ k)
        , emb-comp (f ⨾ g) (h ⨾ k)
        ∙ ap (_· (h ⨾ k)) (emb-comp f g)
        ∙ ·-comp (emb f · g) h k

    σ₁₄ : pt₁ ≡ pt₄
    σ₁₄ = is-contr→is-prop E₄c pt₁ pt₄

    σ₂₃ : pt₂ ≡ pt₃
    σ₂₃ = is-contr→is-prop E₄c pt₂ pt₃

    α₁₄ : ((f ⨾ g) ⨾ h) ⨾ k ≡ (f ⨾ g) ⨾ (h ⨾ k)
    α₁₄ = ap fst σ₁₄

    α₂₃ : (f ⨾ (g ⨾ h)) ⨾ k ≡ f ⨾ ((g ⨾ h) ⨾ k)
    α₂₃ = ap fst σ₂₃

    -- face₂₃: both vertices nest under emb f — function-level bridges,
    -- plain Path.assoc, no coherence.
    γ₂₃-pt : ∀ i → fiber emb (E₄ f g h k)
    γ₂₃-pt i = assoc f (g ⨾ h) k i
             , assoc-σ f (g ⨾ h) k i .snd ∙ ap (_· k) (·-comp (emb f) g h)

    w₂ : pt₂ ≡ γ₂₃-pt i0
    w₂ i = _ , Path.assoc
        (emb-comp (f ⨾ (g ⨾ h)) k)
        (ap (_· k) (emb-comp f (g ⨾ h)))
        (ap (_· k) (·-comp (emb f) g h)) i

    w₃ : γ₂₃-pt i1 ≡ pt₃
    w₃ i = _ , sym (Path.assoc
        (emb-comp f ((g ⨾ h) ⨾ k))
        (·-comp (emb f) (g ⨾ h) k)
        (ap (_· k) (·-comp (emb f) g h))) i

    face₂₃ : α₂₃ ≡ assoc f (g ⨾ h) k
    face₂₃ =
      contr-face E₄c σ₂₃ (ap snd w₂) (λ i → γ₂₃-pt i) (ap snd w₃)

    -- face₁₄: composite-base ·-comp (emb f · g) + the free naturality
    -- square of ·-comp along emb-comp f g.
    γ₁₄-pt : ∀ i → fiber emb (E₄ f g h k)
    γ₁₄-pt i = assoc (f ⨾ g) h k i
             , assoc-σ (f ⨾ g) h k i .snd
             ∙ ap (λ o → o · h · k) (emb-comp f g)

    w₁ : pt₁ ≡ γ₁₄-pt i0
    w₁ i = _ , Path.assoc
        (emb-comp ((f ⨾ g) ⨾ h) k)
        (ap (_· k) (emb-comp (f ⨾ g) h))
        (ap (λ o → o · h · k) (emb-comp f g)) i

    w₁₄-nat
      : ·-comp (emb (f ⨾ g)) h k
          ∙ ap (λ o → o · h · k) (emb-comp f g)
      ≡ ap (_· (h ⨾ k)) (emb-comp f g)
          ∙ ·-comp (emb f · g) h k
    w₁₄-nat = sym (homotopy-natural (λ F → ·-comp F h k) (emb-comp f g))

    w₁₄ : γ₁₄-pt i1 ≡ pt₄
    w₁₄ i = _
      , (sym (Path.assoc A₁₄ N₁₄ C₁₄) ∙ ap (A₁₄ ∙_) w₁₄-nat) i
      where
        A₁₄ = emb-comp (f ⨾ g) (h ⨾ k)
        N₁₄ = ·-comp (emb (f ⨾ g)) h k
        C₁₄ = ap (λ o → o · h · k) (emb-comp f g)

    face₁₄ : α₁₄ ≡ assoc (f ⨾ g) h k
    face₁₄ =
      contr-face E₄c σ₁₄ (ap snd w₁) (λ i → γ₁₄-pt i) (ap snd w₁₄)

    -- face₄₅: composite base + Path.assoc bridge.
    pt₅ : fiber emb (E₄ f g h k)
    pt₅ = f ⨾ (g ⨾ (h ⨾ k))
        , emb-comp f (g ⨾ (h ⨾ k))
        ∙ ·-comp (emb f) g (h ⨾ k)
        ∙ ·-comp (emb f · g) h k

    σ₄₅ : pt₄ ≡ pt₅
    σ₄₅ = is-contr→is-prop E₄c pt₄ pt₅

    α₄₅ : (f ⨾ g) ⨾ (h ⨾ k) ≡ f ⨾ (g ⨾ (h ⨾ k))
    α₄₅ = ap fst σ₄₅

    γ₄₅-pt : ∀ i → fiber emb (E₄ f g h k)
    γ₄₅-pt i = assoc f g (h ⨾ k) i
             , assoc-σ f g (h ⨾ k) i .snd ∙ ·-comp (emb f · g) h k

    w₄ : pt₄ ≡ γ₄₅-pt i0
    w₄ i = _ , Path.assoc
        (emb-comp (f ⨾ g) (h ⨾ k))
        (ap (_· (h ⨾ k)) (emb-comp f g))
        (·-comp (emb f · g) h k) i

    w₅ : γ₄₅-pt i1 ≡ pt₅
    w₅ i = _ , sym (Path.assoc
        (emb-comp f (g ⨾ (h ⨾ k)))
        (·-comp (emb f) g (h ⨾ k))
        (·-comp (emb f · g) h k)) i

    face₄₅ : α₄₅ ≡ assoc f g (h ⨾ k)
    face₄₅ =
      contr-face E₄c σ₄₅ (ap snd w₄) (λ i → γ₄₅-pt i) (ap snd w₅)

    -- face₁₂: associator on the left; ap-comp distributes ap (_· k).
    σ₁₂ : pt₁ ≡ pt₂
    σ₁₂ = is-contr→is-prop E₄c pt₁ pt₂

    α₁₂ : ((f ⨾ g) ⨾ h) ⨾ k ≡ (f ⨾ (g ⨾ h)) ⨾ k
    α₁₂ = ap fst σ₁₂

    γ₁₂-pt : ∀ i → fiber emb (E₄ f g h k)
    γ₁₂-pt i = assoc f g h i ⨾ k
             , emb-comp (assoc f g h i) k
             ∙ ap (_· k) (assoc-σ f g h i .snd)

    w₁₂ˡ : pt₁ ≡ γ₁₂-pt i0
    w₁₂ˡ i = _ , sym (ap (emb-comp ((f ⨾ g) ⨾ h) k ∙_)
        (ap-comp (_· k)
          (emb-comp (f ⨾ g) h)
          (ap (_· h) (emb-comp f g)))) i

    w₁₂ʳ : γ₁₂-pt i1 ≡ pt₂
    w₁₂ʳ i = _ , ap (emb-comp (f ⨾ (g ⨾ h)) k ∙_)
        (ap-comp (_· k) (emb-comp f (g ⨾ h)) (·-comp (emb f) g h)) i

    face₁₂ : α₁₂ ≡ ap (_⨾ k) (assoc f g h)
    face₁₂ =
      contr-face E₄c σ₁₂ (ap snd w₁₂ˡ) (λ i → γ₁₂-pt i) (ap snd w₁₂ʳ)

    -- The fiber-level pentagon from E₄-contractibility (needs no face).
    σ₃₅ : pt₃ ≡ pt₅
    σ₃₅ = is-contr→is-prop E₄c pt₃ pt₅

    α₃₅ : f ⨾ ((g ⨾ h) ⨾ k) ≡ f ⨾ (g ⨾ (h ⨾ k))
    α₃₅ = ap fst σ₃₅

    hom-identity : α₁₄ ∙ α₄₅ ≡ pcom (sym α₁₂) α₂₃ α₃₅
    hom-identity =
      coh-project E₄c fst (σ₁₄ ∙ σ₄₅) (pcom (sym σ₁₂) σ₂₃ σ₃₅)
        (ap-comp fst σ₁₄ σ₄₅)
        (pcom.ap (λ _ → fst) (sym σ₁₂) σ₂₃ σ₃₅)
```

## The inner-associator face

`act = emb @ idn` makes the lift `Φ` satisfy, definitionally,
`Φ (emb Z) = emb f · Z`, `Φ (E₃ g h k) = E₄`,
`ap Φ (emb-comp Z W) = ·-comp (emb f) Z W`, and
`Φ ∘ (_· k) = (_· k) ∘ Φ`. So the inner associator lifts as `Λ = ap Φ`
on the E₃ fiber, and the two bridges collapse to a single `ap-comp Φ`
each — no pentagon coherence remains.

```agda
module Pentagon35 {o h} {ob : Type o}
  (R : codep-category {o} {h} ob)
  {x y z w v}
  (f : codep-category.hom R x y) (g : codep-category.hom R y z)
  (h : codep-category.hom R z w) (k : codep-category.hom R w v)
  where
  open codep-category R
  open Derived R
  open Pentagon R
  open PentagonFibers f g h k

  Φ : loose y v → loose x v
  Φ L γ = emb f (γ .fst , L (at y (γ .fst) , γ .snd))

  Λ : fiber emb (E₃ g h k) → fiber emb (E₄ f g h k)
  Λ pr = f ⨾ pr .fst , emb-comp f (pr .fst) ∙ ap Φ (pr .snd)

  γ₃₅ : ∀ i → fiber emb (E₄ f g h k)
  γ₃₅ i = Λ (assoc-σ g h k i)

  v₃ : pt₃ ≡ γ₃₅ i0
  v₃ i = _ , ap (emb-comp f ((g ⨾ h) ⨾ k) ∙_)
      (sym (ap-comp Φ (emb-comp (g ⨾ h) k) (ap (_· k) (emb-comp g h)))) i

  v₅ : γ₃₅ i1 ≡ pt₅
  v₅ i = _ , ap (emb-comp f (g ⨾ (h ⨾ k)) ∙_)
      (ap-comp Φ (emb-comp g (h ⨾ k)) (·-comp (emb g) h k)) i

  face₃₅ : α₃₅ ≡ ap (f ⨾_) (assoc g h k)
  face₃₅ =
    contr-face E₄c σ₃₅ (ap snd v₃) (λ i → γ₃₅ i) (ap snd v₅)
```

## The full pentagon

All five faces + the fiber pentagon assemble into the named Mac Lane
pentagon identity, matching `Cat.Coherence.pentagon`.

```agda
module Pentagon5 {o h} {ob : Type o}
  (R : codep-category {o} {h} ob)
  {x y z w v}
  (f : codep-category.hom R x y) (g : codep-category.hom R y z)
  (h : codep-category.hom R z w) (k : codep-category.hom R w v)
  where
  open codep-category R
  open Derived R
  open Pentagon R
  open PentagonFibers f g h k
  open Pentagon35 R f g h k using (face₃₅)

  pentagon
    : assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
    ≡ ap (_⨾ k) (assoc f g h)
      ∙ assoc f (g ⨾ h) k
      ∙ ap (f ⨾_) (assoc g h k)
  pentagon =
    pcom (ap (_∙ α₄₅) face₁₄ ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
      hom-identity
      (λ i → pcom (sym (face₁₂ i)) (face₂₃ i) (face₃₅ i))
    ∙ pcom→∙
        (ap (_⨾ k) (assoc f g h))
        (assoc f (g ⨾ h) k)
        (ap (f ⨾_) (assoc g h k))
```
