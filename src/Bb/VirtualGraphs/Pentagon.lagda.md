The pentagon. The five bracketings of a four-fold positive cut are
five points of one fiber of `reflect`. The embedding condition makes
that fiber a proposition, hence a set, so any two paths between two
of its points agree. Each classical edge lifts back into the fiber —
the triple's own fiber path, whiskered or with the fourth factor's
rewriting appended — and the fiber being a proposition identifies the
lift with the canonical path. Only the positive hand's data enters:
the telescope is `rx`, the embedding condition, and the positive cut.
The negative hand's pentagon is that theorem read at the opposite
carrier, over the matching telescope of `corx`, the embedding
condition, and the negative cut.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Pentagon where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Groupoid using (sym-distr)
open import Core.Path.Base using (ap-comp)
open import Core.Transport.Properties using (is-prop→is-set)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
```

```agda
module pentagon⁺ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx : (x : ob) → hom x x)
  (S : reflect-is-embedding G) (C⁺ : framing⁻.is-composable⁺ G rx)
  {w x y z v} (f : hom w x) (g : hom x y) (h : hom y z) (k : hom z v)
  where

  open tower⁺ G rx S C⁺

  E : judgment w v
  E γ = reflect f (γ .fst , coact g (coact h (coact k (γ .snd))))

  b₁ b₂ b₃ b₄ b₅ : is-representable G E
  b₁ = ((f ⨾⁺ g) ⨾⁺ h) ⨾⁺ k
     , reflect-⨾⁺ ((f ⨾⁺ g) ⨾⁺ h) k
     ∙ (λ i γ → reflect-⨾⁺ (f ⨾⁺ g) h i (γ .fst , coact k (γ .snd)))
     ∙ (λ i γ → reflect-⨾⁺ f g i (γ .fst , coact h (coact k (γ .snd))))
  b₂ = (f ⨾⁺ (g ⨾⁺ h)) ⨾⁺ k
     , reflect-⨾⁺ (f ⨾⁺ (g ⨾⁺ h)) k
     ∙ (λ i γ → reflect-⨾⁺ f (g ⨾⁺ h) i (γ .fst , coact k (γ .snd)))
     ∙ (λ i γ → reflect f (γ .fst , coact-⨾⁺ g h (coact k (γ .snd)) i))
  b₃ = f ⨾⁺ ((g ⨾⁺ h) ⨾⁺ k)
     , reflect-⨾⁺ f ((g ⨾⁺ h) ⨾⁺ k)
     ∙ (λ j γ → reflect f
         (γ .fst , (γ .snd .fst , tri⁺.a₁ g h k .snd j (var _ , γ .snd))))
  b₄ = (f ⨾⁺ g) ⨾⁺ (h ⨾⁺ k)
     , reflect-⨾⁺ (f ⨾⁺ g) (h ⨾⁺ k)
     ∙ (λ i γ → reflect-⨾⁺ f g i (γ .fst , coact (h ⨾⁺ k) (γ .snd)))
     ∙ (λ i γ → reflect f (γ .fst , coact g (coact-⨾⁺ h k (γ .snd) i)))
  b₅ = f ⨾⁺ (g ⨾⁺ (h ⨾⁺ k))
     , reflect-⨾⁺ f (g ⨾⁺ (h ⨾⁺ k))
     ∙ (λ j γ → reflect f
         (γ .fst , (γ .snd .fst , tri⁺.a₂ g h k .snd j (var _ , γ .snd))))

  pth : (a b : is-representable G E) → a ≡ b
  pth = S E

  identity : pth b₁ b₄ ∙ pth b₄ b₅ ≡ pth b₁ b₂ ∙ (pth b₂ b₃ ∙ pth b₃ b₅)
  identity = is-prop→is-set (S E) b₁ b₅ _ _

  α₁₂ = ap fst (pth b₁ b₂)
  α₂₃ = ap fst (pth b₂ b₃)
  α₃₅ = ap fst (pth b₃ b₅)
  α₁₄ = ap fst (pth b₁ b₄)
  α₄₅ = ap fst (pth b₄ b₅)

  hom-identity : α₁₄ ∙ α₄₅ ≡ α₁₂ ∙ (α₂₃ ∙ α₃₅)
  hom-identity =
    sym (ap-comp fst (pth b₁ b₄) (pth b₄ b₅))
    ∙ ap (ap fst) identity
    ∙ ap-comp fst (pth b₁ b₂) (pth b₂ b₃ ∙ pth b₃ b₅)
    ∙ ap (α₁₂ ∙_) (ap-comp fst (pth b₂ b₃) (pth b₃ b₅))
```

Each face identifies one of the five traces with a whisker of an
associator, by re-deriving the fiber path from the triple's own.

```agda
  γ₁₂ : b₁ ≡ b₂
  γ₁₂ i = tri⁺.σ f g h i .fst ⨾⁺ k
        , reflect-⨾⁺ (tri⁺.σ f g h i .fst) k
        ∙ (λ j γ → tri⁺.σ f g h i .snd j (γ .fst , coact k (γ .snd)))

  face₁₂ : α₁₂ ≡ ap (_⨾⁺ k) (assoc⁺ f g h)
  face₁₂ = ap (ap fst) (is-prop→is-set (S E) b₁ b₂ (pth b₁ b₂) γ₁₂)

  γ₃₅ : b₃ ≡ b₅
  γ₃₅ i = f ⨾⁺ tri⁺.σ g h k i .fst
        , reflect-⨾⁺ f (tri⁺.σ g h k i .fst)
        ∙ (λ j γ → reflect f
            (γ .fst , (γ .snd .fst , tri⁺.σ g h k i .snd j (var _ , γ .snd))))

  face₃₅ : α₃₅ ≡ ap (f ⨾⁺_) (assoc⁺ g h k)
  face₃₅ = ap (ap fst) (is-prop→is-set (S E) b₃ b₅ (pth b₃ b₅) γ₃₅)

  wrap : judgment x v → judgment w v
  wrap α γ = reflect f (γ .fst , (γ .snd .fst , α (var _ , γ .snd)))

  γ₂₃-pt : (i : I) → is-representable G E
  γ₂₃-pt i = tri⁺.σ f (g ⨾⁺ h) k i .fst
           , tri⁺.σ f (g ⨾⁺ h) k i .snd
           ∙ (λ j γ → reflect f (γ .fst , coact-⨾⁺ g h (coact k (γ .snd)) j))

  l₂₃ : γ₂₃-pt i0 ≡ γ₂₃-pt i1
  l₂₃ i = γ₂₃-pt i

  c₂₃⁰ : b₂ ≡ γ₂₃-pt i0
  c₂₃⁰ i = b₂ .fst
         , Path.assoc (reflect-⨾⁺ (f ⨾⁺ (g ⨾⁺ h)) k)
             (λ j γ → reflect-⨾⁺ f (g ⨾⁺ h) j (γ .fst , coact k (γ .snd)))
             (λ j γ → reflect f (γ .fst , coact-⨾⁺ g h (coact k (γ .snd)) j)) i

  c₂₃¹ : γ₂₃-pt i1 ≡ b₃
  c₂₃¹ i = b₃ .fst
         , ( sym (Path.assoc (reflect-⨾⁺ f ((g ⨾⁺ h) ⨾⁺ k))
               (λ j γ → reflect f (γ .fst , coact-⨾⁺ (g ⨾⁺ h) k (γ .snd) j))
               (λ j γ → reflect f (γ .fst , coact-⨾⁺ g h (coact k (γ .snd)) j)))
           ∙ ap (reflect-⨾⁺ f ((g ⨾⁺ h) ⨾⁺ k) ∙_)
               (sym (ap-comp wrap (reflect-⨾⁺ (g ⨾⁺ h) k)
                       (λ j δ → reflect-⨾⁺ g h j (δ .fst , coact k (δ .snd)))))
           ) i

  γ₂₃ : b₂ ≡ b₃
  γ₂₃ = c₂₃⁰ ∙ (l₂₃ ∙ c₂₃¹)

  face₂₃ : α₂₃ ≡ assoc⁺ f (g ⨾⁺ h) k
  face₂₃ =
    ap (ap fst) (is-prop→is-set (S E) b₂ b₃ (pth b₂ b₃) γ₂₃)
    ∙ ap-comp fst c₂₃⁰ (l₂₃ ∙ c₂₃¹)
    ∙ ap (refl ∙_) (ap-comp fst l₂₃ c₂₃¹ ∙ Path.unitr (assoc⁺ f (g ⨾⁺ h) k))
    ∙ Path.unitl (assoc⁺ f (g ⨾⁺ h) k)

  γ₄₅-pt : (i : I) → is-representable G E
  γ₄₅-pt i = tri⁺.σ f g (h ⨾⁺ k) i .fst
           , tri⁺.σ f g (h ⨾⁺ k) i .snd
           ∙ (λ j γ → reflect f (γ .fst , coact g (coact-⨾⁺ h k (γ .snd) j)))

  l₄₅ : γ₄₅-pt i0 ≡ γ₄₅-pt i1
  l₄₅ i = γ₄₅-pt i

  c₄₅⁰ : b₄ ≡ γ₄₅-pt i0
  c₄₅⁰ i = b₄ .fst
         , Path.assoc (reflect-⨾⁺ (f ⨾⁺ g) (h ⨾⁺ k))
             (λ j γ → reflect-⨾⁺ f g j (γ .fst , coact (h ⨾⁺ k) (γ .snd)))
             (λ j γ → reflect f (γ .fst , coact g (coact-⨾⁺ h k (γ .snd) j))) i

  c₄₅¹ : γ₄₅-pt i1 ≡ b₅
  c₄₅¹ i = b₅ .fst
         , ( sym (Path.assoc (reflect-⨾⁺ f (g ⨾⁺ (h ⨾⁺ k)))
               (λ j γ → reflect f (γ .fst , coact-⨾⁺ g (h ⨾⁺ k) (γ .snd) j))
               (λ j γ → reflect f (γ .fst , coact g (coact-⨾⁺ h k (γ .snd) j))))
           ∙ ap (reflect-⨾⁺ f (g ⨾⁺ (h ⨾⁺ k)) ∙_)
               (sym (ap-comp wrap (reflect-⨾⁺ g (h ⨾⁺ k))
                       (λ j δ → reflect g (δ .fst , coact-⨾⁺ h k (δ .snd) j))))
           ) i

  γ₄₅ : b₄ ≡ b₅
  γ₄₅ = c₄₅⁰ ∙ (l₄₅ ∙ c₄₅¹)

  face₄₅ : α₄₅ ≡ assoc⁺ f g (h ⨾⁺ k)
  face₄₅ =
    ap (ap fst) (is-prop→is-set (S E) b₄ b₅ (pth b₄ b₅) γ₄₅)
    ∙ ap-comp fst c₄₅⁰ (l₄₅ ∙ c₄₅¹)
    ∙ ap (refl ∙_) (ap-comp fst l₄₅ c₄₅¹ ∙ Path.unitr (assoc⁺ f g (h ⨾⁺ k)))
    ∙ Path.unitl (assoc⁺ f g (h ⨾⁺ k))
```

The last edge is the one where two appended steps commute rather than
reassociate: the fourth factor's rewriting and the head's cross, and
their square is the head's own witness read at a moving coterm.

```agda
  exch : (i j : I) → judgment w v
  exch i j γ = reflect-⨾⁺ f g i (γ .fst , coact-⨾⁺ h k (γ .snd) j)

  γ₁₄-pt : (i : I) → is-representable G E
  γ₁₄-pt i = tri⁺.σ (f ⨾⁺ g) h k i .fst
           , tri⁺.σ (f ⨾⁺ g) h k i .snd
           ∙ (λ j γ → reflect-⨾⁺ f g j (γ .fst , coact h (coact k (γ .snd))))

  l₁₄ : γ₁₄-pt i0 ≡ γ₁₄-pt i1
  l₁₄ i = γ₁₄-pt i

  c₁₄⁰ : b₁ ≡ γ₁₄-pt i0
  c₁₄⁰ i = b₁ .fst
         , Path.assoc (reflect-⨾⁺ ((f ⨾⁺ g) ⨾⁺ h) k)
             (λ j γ → reflect-⨾⁺ (f ⨾⁺ g) h j (γ .fst , coact k (γ .snd)))
             (λ j γ → reflect-⨾⁺ f g j (γ .fst , coact h (coact k (γ .snd)))) i

  c₁₄¹ : γ₁₄-pt i1 ≡ b₄
  c₁₄¹ i = b₄ .fst
         , ( sym (Path.assoc (reflect-⨾⁺ (f ⨾⁺ g) (h ⨾⁺ k))
               (λ j → exch i0 j)
               (λ j γ → reflect-⨾⁺ f g j (γ .fst , coact h (coact k (γ .snd)))))
           ∙ ap (reflect-⨾⁺ (f ⨾⁺ g) (h ⨾⁺ k) ∙_)
               (Path.commutes (λ j → exch i0 j) (λ j → exch j i1)
                              (λ j → exch j i0) (λ j → exch i1 j)
                              (λ i j → exch i j))
           ) i

  γ₁₄ : b₁ ≡ b₄
  γ₁₄ = c₁₄⁰ ∙ (l₁₄ ∙ c₁₄¹)

  face₁₄ : α₁₄ ≡ assoc⁺ (f ⨾⁺ g) h k
  face₁₄ =
    ap (ap fst) (is-prop→is-set (S E) b₁ b₄ (pth b₁ b₄) γ₁₄)
    ∙ ap-comp fst c₁₄⁰ (l₁₄ ∙ c₁₄¹)
    ∙ ap (refl ∙_) (ap-comp fst l₁₄ c₁₄¹ ∙ Path.unitr (assoc⁺ (f ⨾⁺ g) h k))
    ∙ Path.unitl (assoc⁺ (f ⨾⁺ g) h k)

  pentagon : assoc⁺ (f ⨾⁺ g) h k ∙ assoc⁺ f g (h ⨾⁺ k)
           ≡ ap (_⨾⁺ k) (assoc⁺ f g h)
           ∙ (assoc⁺ f (g ⨾⁺ h) k ∙ ap (f ⨾⁺_) (assoc⁺ g h k))
  pentagon =
    sym (ap (α₁₄ ∙_) face₄₅ ∙ ap (_∙ assoc⁺ f g (h ⨾⁺ k)) face₁₄)
    ∙ hom-identity
    ∙ ap (_∙ (α₂₃ ∙ α₃₅)) face₁₂
    ∙ ap (ap (_⨾⁺ k) (assoc⁺ f g h) ∙_)
        (ap (_∙ α₃₅) face₂₃ ∙ ap (assoc⁺ f (g ⨾⁺ h) k ∙_) face₃₅)
```

The negative hand reads the four factors in reverse order at the
opposite carrier, so each of the five sides of the positive
pentagon there is a negative associator reversed. Reversal turns
the transported identity around, and reassociating the right leg
puts it in the negative hand's own bracketing.

```agda
module pentagon⁻ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G) (C⁻ : framing⁺.is-composable⁻ G corx)
  {w x y z v} (f : hom w x) (g : hom x y) (h : hom y z) (k : hom z v)
  where

  open op-tower G corx S C⁻

  module op-pentagon = pentagon⁺ (opⱽ G) corx op-embed op-cut⁺ k h g f

  α₁₂ : ((f ⨾⁻ g) ⨾⁻ h) ⨾⁻ k ≡ (f ⨾⁻ (g ⨾⁻ h)) ⨾⁻ k
  α₁₂ = ap (_⨾⁻ k) (assoc⁻ f g h)

  α₂₃ : (f ⨾⁻ (g ⨾⁻ h)) ⨾⁻ k ≡ f ⨾⁻ ((g ⨾⁻ h) ⨾⁻ k)
  α₂₃ = assoc⁻ f (g ⨾⁻ h) k

  α₃₅ : f ⨾⁻ ((g ⨾⁻ h) ⨾⁻ k) ≡ f ⨾⁻ (g ⨾⁻ (h ⨾⁻ k))
  α₃₅ = ap (f ⨾⁻_) (assoc⁻ g h k)

  α₁₄ : ((f ⨾⁻ g) ⨾⁻ h) ⨾⁻ k ≡ (f ⨾⁻ g) ⨾⁻ (h ⨾⁻ k)
  α₁₄ = assoc⁻ (f ⨾⁻ g) h k

  α₄₅ : (f ⨾⁻ g) ⨾⁻ (h ⨾⁻ k) ≡ f ⨾⁻ (g ⨾⁻ (h ⨾⁻ k))
  α₄₅ = assoc⁻ f g (h ⨾⁻ k)

  e₁₂ : ap (_⨾⁻ k) (op.assoc⁺ h g f) ≡ sym α₁₂
  e₁₂ = ap (ap (_⨾⁻ k)) (op-assoc⁺ f g h)

  e₂₃ : op.assoc⁺ k (g ⨾⁻ h) f ≡ sym α₂₃
  e₂₃ = op-assoc⁺ f (g ⨾⁻ h) k

  e₃₅ : ap (f ⨾⁻_) (op.assoc⁺ k h g) ≡ sym α₃₅
  e₃₅ = ap (ap (f ⨾⁻_)) (op-assoc⁺ g h k)

  e₁₄ : op.assoc⁺ k h (f ⨾⁻ g) ≡ sym α₁₄
  e₁₄ = op-assoc⁺ (f ⨾⁻ g) h k

  e₄₅ : op.assoc⁺ (h ⨾⁻ k) g f ≡ sym α₄₅
  e₄₅ = op-assoc⁺ f g (h ⨾⁻ k)

  reversed : sym α₄₅ ∙ sym α₁₄ ≡ sym α₃₅ ∙ (sym α₂₃ ∙ sym α₁₂)
  reversed =
    sym (ap2s _∙_ e₄₅ e₁₄)
    ∙ op-pentagon.pentagon
    ∙ ap2s _∙_ e₃₅ (ap2s _∙_ e₂₃ e₁₂)

  pentagon : assoc⁻ (f ⨾⁻ g) h k ∙ assoc⁻ f g (h ⨾⁻ k)
           ≡ ap (_⨾⁻ k) (assoc⁻ f g h)
           ∙ (assoc⁻ f (g ⨾⁻ h) k ∙ ap (f ⨾⁻_) (assoc⁻ g h k))
  pentagon = ap sym
    ( sym-distr α₁₄ α₄₅
    ∙ reversed
    ∙ Path.assoc (sym α₃₅) (sym α₂₃) (sym α₁₂)
    ∙ ap (_∙ sym α₁₂) (sym (sym-distr α₂₃ α₃₅))
    ∙ sym (sym-distr α₁₂ (α₂₃ ∙ α₃₅)) )
```
