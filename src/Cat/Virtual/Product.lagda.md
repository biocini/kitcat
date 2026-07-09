Lane Biocini
June 2026

Product of virtual categories with set-valued hom-types.
Composition is classified componentwise. The set assumption
is needed because paths in the product ternary action couple
the V and W components; their contractibility requires the
component hom-types to be sets.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Virtual.Product where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Sigma.Type using (Sigma; _,_; fst; snd)
open import Core.Kan
open import Core.Transport.Base
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv)
open import Core.Equiv.Properties using (×-is-equiv)
open import Core.HLevel.Base using (is-prop-×; Π-is-set; ×-is-hlevel)
open import Core.Base using (is-set)
open import Core.Function.Embedding using (is-embedding; injective→is-embedding)
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Cat.Virtual

private
  Σ-path
    : ∀ {u v} {A : Type u} {B : A → Type v}
      {x y : Σ B}
    → (p : fst x ≡ fst y)
    → PathP (λ i → B (p i)) (snd x) (snd y)
    → x ≡ y
  Σ-path p q i = p i , q i
```

## Product of virtual categories

Given virtual categories `V` and `W`, the product has pairs of
objects, pairs of morphisms, and the componentwise ternary
action. Composition is classified by the product of the
component classifiers.

```agda
module _
  {o₁ h₁ p₁ o₂ h₂ p₂}
  (V : virtual-category o₁ h₁ p₁)
  (W : virtual-category o₂ h₂ p₂)
  (V-hom-set : ∀ {x y} → is-set (virtual-category.hom V x y))
  (W-hom-set : ∀ {x y} → is-set (virtual-category.hom W x y))
  where

  private
    module V = virtual-category V
    module W = virtual-category W
    module VC = Classified V
    module WC = Classified W

  private
    ob× : Type (o₁ ⊔ o₂)
    ob× = V.ob × W.ob

    hom× : ob× → ob× → Type (h₁ ⊔ h₂)
    hom× (x₁ , x₂) (y₁ , y₂) = V.hom x₁ y₁ × W.hom x₂ y₂

    emb×
      : ∀ {x y} → hom× x y
      → ∀ w → hom× w x → ∀ v → hom× y v → hom× w v
    emb× (f₁ , f₂) (w₁ , w₂) (a₁ , a₂) (v₁ , v₂) (b₁ , b₂) =
      V.emb f₁ w₁ a₁ v₁ b₁
      , W.emb f₂ w₂ a₂ v₂ b₂

    noy× : ∀ {x y} → hom× x y → ∀ z → hom× y z → hom× x z
    noy× (f₁ , f₂) (z₁ , z₂) (h₁ , h₂) =
      emb× (f₁ , f₂) _ (V.idn , W.idn) _ (h₁ , h₂)

    yon× : ∀ {x y} → hom× x y → ∀ w → hom× w x → hom× w y
    yon× (f₁ , f₂) (w₁ , w₂) (g₁ , g₂) =
      emb× (f₁ , f₂) (w₁ , w₂) (g₁ , g₂) _ (V.idn , W.idn)

    idn× : ∀ {x} → hom× x x
    idn× = V.idn , W.idn

  private
    -- With set-valued hom-types, the product ternary action is an
    -- embedding, so composition fibers are contractible.
    Target×-is-set
      : ∀ {x y}
      → is-set
          ((w : ob×) → hom× w x → (v : ob×) → hom× y v → hom× w v)
    Target×-is-set =
      Π-is-set λ _ →
        Π-is-set λ _ →
          Π-is-set λ _ →
            Π-is-set λ _ →
              ×-is-hlevel 2 V-hom-set W-hom-set

    emb×-inj : ∀ {x y} {s t : hom× x y} → emb× s ≡ emb× t → s ≡ t
    emb×-inj {x = x₁ , x₂} {y = y₁ , y₂} {s = s₁ , s₂} {t₁ , t₂} γ =
      Σ-path
        (VC.emb-inj λ w a v b →
          ap (λ F → F (w , x₂) (a , W.idn) (v , y₂) (b , W.idn) .fst) γ)
        (WC.emb-inj λ w a v b →
          ap (λ F → F (x₁ , w) (V.idn , a) (y₁ , v) (V.idn , b) .snd) γ)

    emb×-is-embedding : ∀ {x y} → is-embedding (emb× {x} {y})
    emb×-is-embedding =
      injective→is-embedding Target×-is-set emb× emb×-inj

    compose-contr
      : ∀ {x₁ x₂ y₁ y₂ z₁ z₂}
        (f₁ : V.hom x₁ y₁) (f₂ : W.hom x₂ y₂)
        (g₁ : V.hom y₁ z₁) (g₂ : W.hom y₂ z₂)
        (c₁ : V.classifier f₁ g₁)
        (c₂ : W.classifier f₂ g₂)
      → is-contr
          (Σ s ∶ hom× (x₁ , x₂) (z₁ , z₂)
           , emb× s ≡ λ w a v b → emb× (f₁ , f₂) w a v (noy× (g₁ , g₂) v b))
    compose-contr f₁ f₂ g₁ g₂ c₁ c₂ =
      prop-inhabited→is-contr
        (emb×-is-embedding _)
        ((V.comp f₁ g₁ c₁ , W.comp f₂ g₂ c₂) , emb×-composite)
      where
        emb×-composite
          : emb× (V.comp f₁ g₁ c₁ , W.comp f₂ g₂ c₂)
          ≡ λ w a v b → emb× (f₁ , f₂) w a v (noy× (g₁ , g₂) v b)
        emb×-composite =
          funext λ (w₁ , w₂) → funext λ (a₁ , a₂) →
            funext λ (v₁ , v₂) → funext λ (b₁ , b₂) →
              Σ-path
                (V.emb-composite-pt f₁ g₁ c₁ w₁ a₁ v₁ b₁)
                (W.emb-composite-pt f₂ g₂ c₂ w₂ a₂ v₂ b₂)

  unit× : (x : ob×) → Σ e ∶ hom× x x
          , (∀ {z} → is-equiv (λ (h : hom× x z) → emb× e x e z h))
          × (∀ {w} → is-equiv (λ (g : hom× w x) → emb× e w g x e))
  unit× (x₁ , x₂) =
    idn×
    , (λ {z} → ×-is-equiv
         (V.unit .snd .fst {z = z .fst})
         (W.unit .snd .fst {z = z .snd}))
    , (λ {w} → ×-is-equiv
         (V.unit .snd .snd {w = w .fst})
         (W.unit .snd .snd {w = w .snd}))

  -- This construction requires set-valued hom-types. The general
  -- virtual-category product is obstructed: paths in the product
  -- ternary action couple the V and W components, and their
  -- contractibility needs the component hom-types to be sets.
  _×vc_ : virtual-category (o₁ ⊔ o₂) (h₁ ⊔ h₂) (p₁ ⊔ p₂)
  _×vc_ .virtual-category.ob = ob×
  _×vc_ .virtual-category.hom = hom×
  _×vc_ .virtual-category.emb = emb×
  _×vc_ .virtual-category.unit {x} = unit× x
  _×vc_ .virtual-category.yon-eval (f₁ , f₂) =
    Σ-path (V.yon-eval f₁) (W.yon-eval f₂)
  _×vc_ .virtual-category.classifier (f₁ , f₂) (g₁ , g₂) =
    V.classifier f₁ g₁ × W.classifier f₂ g₂
  _×vc_ .virtual-category.classifier-prop =
    is-prop-× V.classifier-prop W.classifier-prop
  _×vc_ .virtual-category.compose-classified
    {x = x₁ , x₂} {y = y₁ , y₂} {z = z₁ , z₂}
    (f₁ , f₂) (g₁ , g₂) (c₁ , c₂) =
    compose-contr f₁ f₂ g₁ g₂ c₁ c₂
  _×vc_ .virtual-category.interchange-classified
    (f₁ , f₂) (g₁ , g₂) (c₁ , c₂)
    (w₁ , w₂) (a₁ , a₂) (v₁ , v₂) (b₁ , b₂) =
    Σ-path
      (V.interchange-classified f₁ g₁ c₁ w₁ a₁ v₁ b₁)
      (W.interchange-classified f₂ g₂ c₂ w₂ a₂ v₂ b₂)
  _×vc_ .virtual-category.classifier-idn-l (f₁ , f₂) =
    V.classifier-idn-l f₁ , W.classifier-idn-l f₂
  _×vc_ .virtual-category.classifier-idn-r (f₁ , f₂) =
    V.classifier-idn-r f₁ , W.classifier-idn-r f₂
  _×vc_ .virtual-category.classifier-assoc cfg cgh =
    (V.classifier-assoc (cfg .fst) (cgh .fst) .fst
    , W.classifier-assoc (cfg .snd) (cgh .snd) .fst)
    , (V.classifier-assoc (cfg .fst) (cgh .fst) .snd
    , W.classifier-assoc (cfg .snd) (cgh .snd) .snd)
```

## Product of `Cat.Type` categories

A product of two `T.category` values could be obtained from the
virtual-category product via `to-category (from-category C ×vc
from-category D)` with the total classifier. However, the
virtual-category product above requires set-valued hom-types,
which `T.category` does not assume. A direct product in
`Cat.Type.category` hits the same coherence problem; it would
need a `hom-is-set` field on `category`.
