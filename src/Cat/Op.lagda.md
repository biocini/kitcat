Lane Biocini
July 2026

The dual category.

Duality acts on contexts by swapping the over and under parts, so
composites transport along the swap. The axioms dualize pointwise,
and `op` is involutive definitionally.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Op where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Path.Base

open import Cat.Type

opᴿ : ∀ {o h} → reflexive-graph o h → reflexive-graph o h
opᴿ structure .reflexive-graph.ob       = structure .reflexive-graph.ob
opᴿ structure .reflexive-graph.edge x y = structure .reflexive-graph.edge y x
opᴿ structure .reflexive-graph.rx       = structure .reflexive-graph.rx

module op {o h} (C : category o h) where
  open category C
  module V  = virtual structure
  module Vᵒ = virtual (opᴿ structure)
  module A  = category-axioms axioms

  σ  : ∀ {x y} → Vᵒ.ctx x y → V.ctx y x  ;  σ  γ = γ .snd , γ .fst
  σ' : ∀ {x y} → V.ctx y x → Vᵒ.ctx x y  ;  σ' δ = δ .snd , δ .fst

  ⟲ : ∀ {x y} → V.composite y x → Vᵒ.composite x y  ;  ⟲ F γ = F (σ γ)
  ⟳ : ∀ {x y} → Vᵒ.composite x y → V.composite y x  ;  ⟳ G δ = G (σ' δ)

  -- both by Σ-η + function η
  ⟲⟳ : ∀ {x y} (G : Vᵒ.composite x y) → ⟲ (⟳ G) ≡ G  ;  ⟲⟳ _ = refl
  ⟳⟲ : ∀ {x y} (F : V.composite y x) → ⟳ (⟲ F) ≡ F  ;  ⟳⟲ _ = refl

  Spineᵒ : ∀ {x y z} (f : Vᵒ.hom x y) (g : Vᵒ.hom y z) → Type (o ⊔ h)
  Spineᵒ {x} {z = z} f g =
    Σ k ∶ Vᵒ.hom x z ,
    Σ p ∶ (⟲ (A.emb k) ≡ ⟲ (g A.·ᵒᵖ A.emb f)) ,
    Σ q ∶ (⟲ (A.emb k) ≡ ⟲ (A.emb g A.· f)) ,
      PathP (λ i → ⟲ (A.emb k) ≡ ap ⟲ (sym (A.interchange g f)) i) p q

  to  : ∀ {x y z} {f : Vᵒ.hom x y} {g : Vᵒ.hom y z} → A.spine g f → Spineᵒ f g
  to  (k , p , q , θ) = k , ap ⟲ q , ap ⟲ p , λ i j → ⟲ (θ (~ i) j)

  fro : ∀ {x y z} {f : Vᵒ.hom x y} {g : Vᵒ.hom y z} → Spineᵒ f g → A.spine g f
  fro (k , p , q , θ) = k , ap ⟳ q , ap ⟳ p , λ i j → ⟳ (θ (~ i) j)

  op-axioms : category-axioms (opᴿ structure)
  op-axioms .category-axioms.emb f = ⟲ (A.emb f)
  op-axioms .category-axioms.interchange♭ (m , p) (n , q) =
    ap ⟲ (sym (A.interchange♭ (n , ap ⟳ q) (m , ap ⟳ p)))
  op-axioms .category-axioms.spine-contr f g .center = to (A.spine-contr g f .center)
  op-axioms .category-axioms.spine-contr f g .paths t = ap to (A.spine-contr g f .paths (fro t))
  op-axioms .category-axioms.unit f = A.unit f

op : ∀ {o h} → category o h → category o h
op C .category.structure = opᴿ (C .category.structure)
op C .category.axioms    = op.op-axioms C

op-invol : ∀ {o h} (C : category o h) → op (op C) ≡ C
op-invol C = refl
```
