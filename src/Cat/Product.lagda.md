Lane Biocini
March 2026

Product category. The `compose-contr` helpers are defined before
the record to break a termination-checker cycle through
`_×cat_.category.emb`. Contractibility of the product compose
fiber uses an equivalence (with refl round-trips) to decompose
the product fiber into overcounted factors, each propositional
(via `total-contr-unique` and `coe10`) and inhabited, hence
contractible.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Product where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Sub using (inS; outS)
open import Core.Equiv.Base
  using (is-equiv; eqv-fibers; is-contr-equiv; iso→equiv; _≃_)
open import Core.Equiv.Properties
  using (×-is-equiv; esym; Σ-fiber-swap; Σ-equiv-snd; Σ-×-swap;
         _∙e_)
open import Core.Transport.Base using (coe10; contr-ind)
open import Core.Transport.Properties
  using (is-contr-×; prop-inhabited→is-contr)
open import Cat.Type
open import Cat.Base using (functor)
```

## Helpers

```agda
private
  Σ-path
    : ∀ {u v} {A : Type u} {B : A → Type v}
      {x y : Σ B}
    → (p : fst x ≡ fst y)
    → PathP (λ i → B (p i)) (snd x) (snd y)
    → x ≡ y
  Σ-path p q i = p i , q i

  is-contr-fst
    : ∀ {u v} {A : Type u} {B : Type v}
    → is-contr (A × B) → is-contr A
  is-contr-fst cc .center = fst (cc .center)
  is-contr-fst cc .paths a =
    ap fst (cc .paths (a , snd (cc .center)))

  is-contr-snd
    : ∀ {u v} {A : Type u} {B : Type v}
    → is-contr (A × B) → is-contr B
  is-contr-snd cc .center = snd (cc .center)
  is-contr-snd cc .paths b =
    ap snd (cc .paths (fst (cc .center) , b))

  ×-is-equiv-fst
    : ∀ {u₁ u₂ v₁ v₂}
      {A : Type u₁} {B : Type u₂}
      {C : Type v₁} {D : Type v₂}
      {f : A → C} {g : B → D}
    → B → is-equiv (λ (x , y) → f x , g y)
    → is-equiv f
  ×-is-equiv-fst {g = g} b₀ e .eqv-fibers c =
    is-contr-fst
      (is-contr-equiv (esym Σ-fiber-swap)
        (e .eqv-fibers (c , g b₀)))

  ×-is-equiv-snd
    : ∀ {u₁ u₂ v₁ v₂}
      {A : Type u₁} {B : Type u₂}
      {C : Type v₁} {D : Type v₂}
      {f : A → C} {g : B → D}
    → A → is-equiv (λ (x , y) → f x , g y)
    → is-equiv g
  ×-is-equiv-snd {f = f} a₀ e .eqv-fibers d =
    is-contr-snd
      (is-contr-equiv (esym Σ-fiber-swap)
        (e .eqv-fibers (f a₀ , d)))
```

## The product category

The product compose-contr fiber decomposes via an equivalence
(with refl round-trips) into a product of "overcounted" factors.
Each overcounted factor `Σ s₁, (∀ D-args → C.emb s₁ ≡ target₁)`
is propositional: given two elements, the morphism path comes
from the contractible extensional fiber, and the equation PathP
is coerced via `total-contr-unique` (which equates the
first-component paths from different D-arg evaluations). Since
each factor is also inhabited, it is contractible.

```agda
module _ {o₁ h₁ o₂ h₂}
  (C : category o₁ h₁) (D : category o₂ h₂) where
  private
    module C = Virtual C
    module D = Virtual D

  private
    emb×
      : ∀ {x₁ x₂ z₁ z₂}
      → C.hom x₁ z₁ → D.hom x₂ z₂
      → ∀ (w : C.ob × D.ob)
      → C.hom (fst w) x₁ × D.hom (snd w) x₂
      → ∀ (v : C.ob × D.ob)
      → C.hom z₁ (fst v) × D.hom z₂ (snd v)
      → C.hom (fst w) (fst v)
        × D.hom (snd w) (snd v)
    emb× t₁ t₂ (w₁ , w₂) (a₁ , a₂) (v₁ , v₂)
      (b₁ , b₂) =
      C.emb t₁ w₁ a₁ v₁ b₁
      , D.emb t₂ w₂ a₂ v₂ b₂

    target×
      : ∀ {x₁ x₂ y₁ y₂ z₁ z₂}
      → C.hom x₁ y₁ → D.hom x₂ y₂
      → C.hom y₁ z₁ → D.hom y₂ z₂
      → ∀ (w : C.ob × D.ob)
      → C.hom (fst w) x₁ × D.hom (snd w) x₂
      → ∀ (v : C.ob × D.ob)
      → C.hom z₁ (fst v) × D.hom z₂ (snd v)
      → C.hom (fst w) (fst v)
        × D.hom (snd w) (snd v)
    target× f₁ f₂ g₁ g₂
      (w₁ , w₂) (a₁ , a₂) (v₁ , v₂) (b₁ , b₂) =
      C.emb f₁ w₁ a₁ v₁ (C.noy g₁ v₁ b₁)
      , D.emb f₂ w₂ a₂ v₂ (D.noy g₂ v₂ b₂)

    prod-compose-contr
      : ∀ {x₁ x₂ y₁ y₂ z₁ z₂}
        (f₁ : C.hom x₁ y₁) (f₂ : D.hom x₂ y₂)
        (g₁ : C.hom y₁ z₁) (g₂ : D.hom y₂ z₂)
      → is-contr
          (Σ s ∶ C.hom x₁ z₁ × D.hom x₂ z₂
          , emb× (fst s) (snd s)
            ≡ target× f₁ f₂ g₁ g₂)
    prod-compose-contr
      {x₁ = x₁} {x₂ = x₂}
      {z₁ = z₁} {z₂ = z₂}
      f₁ f₂ g₁ g₂ =
      is-contr-equiv (esym split-equiv)
        (is-contr-× F₁-contr F₂-contr)
      where
        target₁ = λ w₁ (a₁ : C.hom w₁ x₁) v₁
          (b₁ : C.hom z₁ v₁) →
          C.emb f₁ w₁ a₁ v₁ (C.noy g₁ v₁ b₁)

        target₂ = λ w₂ (a₂ : D.hom w₂ x₂) v₂
          (b₂ : D.hom z₂ v₂) →
          D.emb f₂ w₂ a₂ v₂ (D.noy g₂ v₂ b₂)

        -- Pointwise compose-contr for each component
        cc₁ = C.composable-contr f₁ g₁
        cc₂ = D.composable-contr f₂ g₂

        -- The cc₁ fiber type, with B explicit
        CC₁ = Σ s₁ ∶ C.hom x₁ z₁
            , ∀ w (a : C.hom w x₁) v (b : C.hom z₁ v)
              → C.emb s₁ w a v b ≡ target₁ w a v b

        CC₂ = Σ s₂ ∶ D.hom x₂ z₂
            , ∀ w (a : D.hom w x₂) v (b : D.hom z₂ v)
              → D.emb s₂ w a v b ≡ target₂ w a v b

        -- Overcounted factors with pointwise equalities
        F₁ : Type _
        F₁ = Σ s₁ ∶ C.hom x₁ z₁
           , ∀ w₂ (a₂ : D.hom w₂ x₂) v₂
               (b₂ : D.hom z₂ v₂)
               w₁ (a₁ : C.hom w₁ x₁) v₁
               (b₁ : C.hom z₁ v₁)
             → C.emb s₁ w₁ a₁ v₁ b₁
               ≡ target₁ w₁ a₁ v₁ b₁

        F₂ : Type _
        F₂ = Σ s₂ ∶ D.hom x₂ z₂
           , ∀ w₁ (a₁ : C.hom w₁ x₁) v₁
               (b₁ : C.hom z₁ v₁)
               w₂ (a₂ : D.hom w₂ x₂) v₂
               (b₂ : D.hom z₂ v₂)
             → D.emb s₂ w₂ a₂ v₂ b₂
               ≡ target₂ w₂ a₂ v₂ b₂

        fwd
          : F₁ × F₂
          → Σ s ∶ C.hom x₁ z₁ × D.hom x₂ z₂
            , emb× (fst s) (snd s)
              ≡ target× f₁ f₂ g₁ g₂
        fwd ((s₁ , g₁') , (s₂ , g₂')) =
          (s₁ , s₂)
          , λ i (w₁ , w₂) (a₁ , a₂)
                (v₁ , v₂) (b₁ , b₂) →
              g₁' w₂ a₂ v₂ b₂ w₁ a₁ v₁ b₁ i
            , g₂' w₁ a₁ v₁ b₁ w₂ a₂ v₂ b₂ i

        bwd
          : Σ s ∶ C.hom x₁ z₁ × D.hom x₂ z₂
            , emb× (fst s) (snd s)
              ≡ target× f₁ f₂ g₁ g₂
          → F₁ × F₂
        bwd ((s₁ , s₂) , p) =
          ( s₁
          , λ w₂ a₂ v₂ b₂ w₁ a₁ v₁ b₁ i →
              fst (p i (w₁ , w₂) (a₁ , a₂)
                     (v₁ , v₂) (b₁ , b₂)))
          , ( s₂
            , λ w₁ a₁ v₁ b₁ w₂ a₂ v₂ b₂ i →
                snd (p i (w₁ , w₂) (a₁ , a₂)
                       (v₁ , v₂) (b₁ , b₂)))

        split-equiv
          : (F₁ × F₂) ≃
            Σ s ∶ C.hom x₁ z₁ × D.hom x₂ z₂
            , emb× (fst s) (snd s)
              ≡ target× f₁ f₂ g₁ g₂
        split-equiv .fst = fwd
        split-equiv .snd = iso→equiv fwd bwd
          (λ _ → refl) (λ _ → refl) .snd

        -- Typed snd projectors that avoid metavariable
        -- issues from no-eta-equality record projections.
        cc₁-snd : (x : CC₁)
          → ∀ w (a : C.hom w x₁) v (b : C.hom z₁ v)
          → C.emb (x .fst) w a v b
            ≡ target₁ w a v b
        cc₁-snd x = x .snd

        cc₂-snd : (x : CC₂)
          → ∀ w (a : D.hom w x₂) v (b : D.hom z₂ v)
          → D.emb (x .fst) w a v b
            ≡ target₂ w a v b
        cc₂-snd x = x .snd

        abstract
          F₁-contr : is-contr F₁
          F₁-contr .center =
            C._⨾_ f₁ g₁
            , λ _ _ _ _ →
                C.emb-composite-pt f₁ g₁
          F₁-contr .paths (s₁ , g') i =
            fst (cc₁-pt i)
            , λ w₂ a₂ v₂ b₂ →
                cc₁-snd (cc₁-wt w₂ a₂ v₂ b₂ i)
            where
              cc₁-pt = cc₁ .paths
                (s₁ , g' x₂ D.idn z₂ D.idn)
              cc₁-wt = λ w₂ a₂ v₂ b₂ →
                cc₁ .paths (s₁ , g' w₂ a₂ v₂ b₂)

          F₂-contr : is-contr F₂
          F₂-contr .center =
            D._⨾_ f₂ g₂
            , λ _ _ _ _ →
                D.emb-composite-pt f₂ g₂
          F₂-contr .paths (s₂ , g') i =
            fst (cc₂-pt i)
            , λ w₁ a₁ v₁ b₁ →
                cc₂-snd (cc₂-wt w₁ a₁ v₁ b₁ i)
            where
              cc₂-pt = cc₂ .paths
                (s₂ , g' x₁ C.idn z₁ C.idn)
              cc₂-wt = λ w₁ a₁ v₁ b₁ →
                cc₂ .paths (s₂ , g' w₁ a₁ v₁ b₁)

  _×cat_ : category (o₁ ⊔ o₂) (h₁ ⊔ h₂)
  _×cat_ .category.ob = C.ob × D.ob
  _×cat_ .category.hom (x₁ , x₂) (y₁ , y₂) =
    C.hom x₁ y₁ × D.hom x₂ y₂
  _×cat_ .category.emb (f₁ , f₂)
    (w₁ , w₂) (a₁ , a₂) (z₁ , z₂) (b₁ , b₂) =
    C.emb f₁ w₁ a₁ z₁ b₁ , D.emb f₂ w₂ a₂ z₂ b₂
  _×cat_ .category.unit =
    (C.idn , D.idn)
    , ×-is-equiv C.unit-eqvl D.unit-eqvl
    , ×-is-equiv C.unit-eqvr D.unit-eqvr
  _×cat_ .category.compose-contr
    (f₁ , f₂) (g₁ , g₂) =
    prod-compose-contr f₁ f₂ g₁ g₂
  _×cat_ .category.interchange
    (f₁ , f₂) (g₁ , g₂)
    (w₁ , w₂) (a₁ , a₂) (v₁ , v₂) (b₁ , b₂) i =
    C.interchange f₁ g₁ w₁ a₁ v₁ b₁ i
    , D.interchange f₂ g₂ w₂ a₂ v₂ b₂ i
  _×cat_ .category.yon-eval (f₁ , f₂) i =
    C.yon-eval f₁ i , D.yon-eval f₂ i
```


## Projection functors

```agda
module _ {o₁ h₁ o₂ h₂}
  {C : category o₁ h₁} {D : category o₂ h₂} where
  private
    module C = Virtual C
    module D = Virtual D

  -- π₁ : functor (C ×cat D) C
  -- π₁ .functor.map = fst
  -- π₁ .functor.hmap = fst
  -- π₁ .functor.preserves-comp _ _ = ?
  -- π₁ .functor.preserves-neutral {f = f₁ , f₂} (nl , nr) =
  --   (×-is-equiv-fst D.idn nl) , (×-is-equiv-fst D.idn nr)

  -- π₂ : functor (C ×cat D) D
  -- π₂ .functor.map = snd
  -- π₂ .functor.hmap = snd
  -- π₂ .functor.preserves-comp _ _ = refl
  -- π₂ .functor.preserves-neutral {f = f₁ , f₂} (nl , nr) =
  --   (×-is-equiv-snd C.idn nl) , (×-is-equiv-snd C.idn nr)
```
