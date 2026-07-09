Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Structures/PartialSemigroup.agda`.

A ternary relation is a *partial semigroup* when it has an equivalence on
the carrier, the relation respects that equivalence in all three positions,
and it is associative in both directions. This unlocks the currying and
composition laws of the separating conjunction `_✴_` and wand `_─✴_`, and
transitivity of the extension order `_≤_`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Structures.PartialSemigroup where

open import Core.Type using (Type; Level; _⊔_; 0ℓ; _∘_)
open import Core.Data.Sigma using (Sigma; _,_; fst; snd; _×_; Σ-syntax)
open import Lib.Relation.Unary hiding (_∪_; _∩_; ∅)
open import Lib.Relation.Binary
open import Lib.Ternary.Core

record IsPartialSemigroup {a} {A : Type a} {e}
  (_≈_ : A → A → Type e) (rel : Rel₃ A) : Type (a ⊔ e) where
  open Rel₃ rel

  field
    overlap {{ ≈-equivalence }} : IsEquivalence _≈_

    -- the relation respects the equivalence in all positions
    overlap {{∙-respects-≈}}  : ∀ {Φ₁ Φ₂} → Respect _≈_ (Φ₁ ∙ Φ₂)
    overlap {{∙-respects-≈ˡ}} : ∀ {Φ₂ Φ}  → Respect _≈_ (_∙ Φ₂ ≣ Φ)
    overlap {{∙-respects-≈ʳ}} : ∀ {Φ₁ Φ}  → Respect _≈_ (Φ₁ ∙_≣ Φ)

    ∙-assocᵣ : RightAssoc rel
    ∙-assocₗ : LeftAssoc rel

  -- the "product" and arrow respect the equivalence
  module _ where

    instance ✴-respect-≈ : ∀ {p q} {P : Pred A p} {Q : ∀ {Φ} → P Φ → Pred A q} → Respect _≈_ (Conj P Q)
    Respect.coe ✴-respect-≈ eq (px ∙⟨ σ ⟩ qx) = px ∙⟨ coe eq σ ⟩ qx

    instance ─✴-respect-≈ : ∀ {p q} {P : Pred A p} {Q : Pred A q} → Respect _≈_ (P ─✴ Q)
    Respect.coe ─✴-respect-≈ eq f ⟨ σ ⟩ px = f ⟨ coe (sym eq) σ ⟩ px

  module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where
    ✴-assocₗ : ∀[ P ✴ (Q ✴ R) ⇒ (P ✴ Q) ✴ R ]
    ✴-assocₗ (p ∙⟨ σ₁ ⟩ (q ∙⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ∙-assocₗ σ₁ σ₂ in
      (p ∙⟨ σ₃ ⟩ q) ∙⟨ σ₄ ⟩ r

    ✴-assocᵣ : ∀[ (P ✴ Q) ✴ R ⇒ P ✴ (Q ✴ R) ]
    ✴-assocᵣ ((p ∙⟨ σ₁ ⟩ q) ∙⟨ σ₂ ⟩ r) =
      let _ , σ₃ , σ₄ = ∙-assocᵣ σ₁ σ₂ in
      p ∙⟨ σ₃ ⟩ q ∙⟨ σ₄ ⟩ r

  {- Weak mapping _✴_ -}
  module _ {p q p' q'}
    {P : Pred A p} {Q : Pred A q} {P' : Pred A p'} {Q' : Pred A q'} where

    ⟨_⟨✴⟩_⟩ : ∀[ P ⇒ P' ] → ∀[ Q ⇒ Q' ] → ∀[ P ✴ Q ⇒ P' ✴ Q' ]
    ⟨_⟨✴⟩_⟩ f g (px ∙⟨ sep ⟩ qx) = f px ∙⟨ sep ⟩ g qx

  {- Magic composition -}
  module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

    com : ∀[ (Q ─✴ R) ⇒ (P ─✴ Q) ─✴ (P ─✴ R) ]
    com g ⟨ σ₁ ⟩ f ⟨ σ₂ ⟩ px = let _ , σ₃ , σ₄ = ∙-assocᵣ σ₁ σ₂ in g ⟨ σ₃ ⟩ (f ⟨ σ₄ ⟩ px)

    com-syntax : ∀ {Φ₁ Φ₂ Φ} → (Q ─✴ R) Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → (P ─✴ Q) Φ₂ → (P ─✴ R) Φ
    com-syntax g σ f = com g ⟨ σ ⟩ f

    syntax com-syntax f σ g = f ∘⟨ σ ⟩ g

  {- Magic curry -}
  module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

    ✴-curry : ∀[ (P ─✴ (Q ─✴ R)) ⇒ (P ✴ Q) ─✴ R ]
    ✴-curry f ⟨ σ₂ ⟩ (p ∙⟨ σ₁ ⟩ q) =
      let _ , σ₃ , σ₄ = ∙-assocₗ σ₂ σ₁ in f ⟨ σ₃ ⟩ p ⟨ σ₄ ⟩ q

    ✴-uncurry : ∀[ (P ✴ Q ─✴ R) ⇒ P ─✴ (Q ─✴ R) ]
    ✴-uncurry f ⟨ σ₁ ⟩ p ⟨ σ₂ ⟩ q =
      let _ , σ₃ , σ₄ = ∙-assocᵣ σ₁ σ₂ in f ⟨ σ₃ ⟩ (p ∙⟨ σ₄ ⟩ q)

    intro : ∀[ (P ✴ Q) ⇒ R ] → ∀[ P ⇒ (Q ─✴ R) ]
    intro f px ⟨ s ⟩ qx = f (px ∙⟨ s ⟩ qx)

  module _ where

    ≤-trans : ∀ {Φ₁ Φ₂ Φ₃} → Φ₁ ≤ Φ₂ → Φ₂ ≤ Φ₃ → Φ₁ ≤ Φ₃
    ≤-trans (τ₁ , Φ₁∙τ₁=Φ₂) (τ₂ , Φ₂∙τ₂=Φ₃) =
      let τ₃ , p , q = ∙-assocᵣ Φ₁∙τ₁=Φ₂ Φ₂∙τ₂=Φ₃ in τ₃ , p

```
