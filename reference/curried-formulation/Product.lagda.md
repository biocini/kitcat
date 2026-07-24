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

module Cat.Depreciated.Product where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Sub using (inS; outS)
open import Core.Equiv.Base
  using (is-equiv; eqv-fibers; is-contr-equiv; iso→equiv; _≃_)
open import Core.Equiv.Properties
  using ( ×-is-equiv; esym; Σ-fiber-swap; Σ-equiv-snd; Σ-×-swap
        ; _∙e_; comp-equiv; ×-path-equiv)
open import Core.Transport.Base using (contr-ind)
open import Core.Transport.J using (J; subst)
open import Core.Transport.Properties
  using (is-contr-×; prop-inhabited→is-contr)
open import Core.Function.Embedding
  using ( is-embedding; is-embedding→contr-fibers
        ; is-embedding→ap-equiv; ap-equiv→image-fibers-contr
        ; image-fibers-contr→is-embedding
        ; is-equiv→is-embedding )
open import Core.HLevel.Base
  using (is-prop-×; is-prop-equiv)
open import Cat.Depreciated.Type
open import Cat.Depreciated.Base using (functor)
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

The product composition fiber is the fiber of the componentwise
ternary embedding `emb×`. We prove `emb×` is an embedding by
showing that `ap emb×` is an equivalence. The key step is an
equivalence between pairs of component `emb`-paths and `emb×`-paths,
proved by restricting to dummy identities and using the
contractibility of each component's `emb`-fiber.

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
      is-embedding→contr-fibers emb×-is-embedding
        ((f₁ C.⨾ g₁ , f₂ D.⨾ g₂) , emb×-composite)
      where
        sym-sym
          : ∀ {ℓ} {A : Type ℓ} {a b : A}
            (p : a ≡ b)
          → sym (sym p) ≡ p
        sym-sym p = J (λ b p → sym (sym p) ≡ p) refl p

        -- Equivalence between componentwise emb-paths and emb×-paths.
        emb×-≡-equiv
          : ∀ {s₁ s₁' : C.hom x₁ z₁}
              {s₂ s₂' : D.hom x₂ z₂}
          → (C.emb s₁ ≡ C.emb s₁')
          × (D.emb s₂ ≡ D.emb s₂')
          ≃ (emb× s₁ s₂ ≡ emb× s₁' s₂')
        emb×-≡-equiv {s₁ = s₁} {s₁' = s₁'}
          {s₂ = s₂} {s₂' = s₂'} =
          iso→equiv fwd bwd (λ _ → refl) retr
          where
            fwd
              : (C.emb s₁ ≡ C.emb s₁')
              × (D.emb s₂ ≡ D.emb s₂')
              → emb× s₁ s₂ ≡ emb× s₁' s₂'
            fwd (α , β) i w a v b =
              α i (fst w) (fst a) (fst v) (fst b)
              , β i (snd w) (snd a) (snd v) (snd b)

            bwd
              : emb× s₁ s₂ ≡ emb× s₁' s₂'
              → (C.emb s₁ ≡ C.emb s₁')
              × (D.emb s₂ ≡ D.emb s₂')
            bwd γ =
              let
                α = λ i w₁ a₁ v₁ b₁ →
                      fst (γ i (w₁ , x₂) (a₁ , D.idn)
                             (v₁ , z₂) (b₁ , D.idn))
                β = λ i w₂ a₂ v₂ b₂ →
                      snd (γ i (x₁ , w₂) (C.idn , a₂)
                             (z₁ , v₂) (C.idn , b₂))
              in α , β

            retr
              : (γ : emb× s₁ s₂ ≡ emb× s₁' s₂')
              → fwd (bwd γ) ≡ γ
            retr γ =
              funext λ i → funext λ w → funext λ a
                → funext λ v → funext λ b →
                  Σ-path (V-eq i w a v b) (W-eq i w a v b)
              where
                V-eq
                  : ∀ i w a v b
                  → fst (fwd (bwd γ) i w a v b)
                    ≡ fst (γ i w a v b)
                V-eq i w a v b =
                  let
                    w₂ = snd w; a₂ = snd a
                    v₂ = snd v; b₂ = snd b

                    δC
                      : C.emb s₁ ≡ C.emb s₁'
                    δC i w₁ a₁ v₁ b₁ =
                      fst (γ i (w₁ , w₂) (a₁ , a₂)
                             (v₁ , v₂) (b₁ , b₂))

                    δC-dummy
                      : C.emb s₁ ≡ C.emb s₁'
                    δC-dummy i w₁ a₁ v₁ b₁ =
                      fst (γ i (w₁ , x₂) (a₁ , D.idn)
                             (v₁ , z₂) (b₁ , D.idn))

                    fib : fiber C.emb (C.emb s₁)
                    fib = s₁' , sym δC

                    fib-dummy : fiber C.emb (C.emb s₁)
                    fib-dummy = s₁' , sym δC-dummy

                    eq : fib ≡ fib-dummy
                    eq = is-contr→is-prop
                           (is-embedding→contr-fibers
                             C.emb-is-embedding (s₁ , refl))
                           fib fib-dummy

                    δC≡δC-dummy : δC ≡ δC-dummy
                    δC≡δC-dummy =
                      sym (sym-sym δC)
                      ∙ ap sym (ap snd eq)
                      ∙ sym-sym δC-dummy
                  in ap (λ p → p _ w a v b)
                       (sym δC≡δC-dummy)

                W-eq
                  : ∀ i w a v b
                  → snd (fwd (bwd γ) i w a v b)
                    ≡ snd (γ i w a v b)
                W-eq i w a v b =
                  let
                    w₁ = fst w; a₁ = fst a
                    v₁ = fst v; b₁ = fst b

                    δD
                      : D.emb s₂ ≡ D.emb s₂'
                    δD i w₂ a₂ v₂ b₂ =
                      snd (γ i (w₁ , w₂) (a₁ , a₂)
                             (v₁ , v₂) (b₁ , b₂))

                    δD-dummy
                      : D.emb s₂ ≡ D.emb s₂'
                    δD-dummy i w₂ a₂ v₂ b₂ =
                      snd (γ i (x₁ , w₂) (C.idn , a₂)
                             (z₁ , v₂) (C.idn , b₂))

                    fib : fiber D.emb (D.emb s₂)
                    fib = s₂' , sym δD

                    fib-dummy : fiber D.emb (D.emb s₂)
                    fib-dummy = s₂' , sym δD-dummy

                    eq : fib ≡ fib-dummy
                    eq = is-contr→is-prop
                           (is-embedding→contr-fibers
                             D.emb-is-embedding (s₂ , refl))
                           fib fib-dummy

                    δD≡δD-dummy : δD ≡ δD-dummy
                    δD≡δD-dummy =
                      sym (sym-sym δD)
                      ∙ ap sym (ap snd eq)
                      ∙ sym-sym δD-dummy
                  in ap (λ p → p _ w a v b)
                       (sym δD≡δD-dummy)

        -- `ap emb×` is an equivalence by composing the component
        -- ap-equivalences with emb×-≡-equiv.
        emb×-ap-equiv
          : ∀ {s s' : C.hom x₁ z₁ × D.hom x₂ z₂}
          → is-equiv (ap emb× {x = s} {s'})
        emb×-ap-equiv {s = s} {s' = s'} =
          subst is-equiv path
            (comp-equiv (esym ×-path-equiv .snd)
              (comp-equiv
                (×-is-equiv
                  (is-embedding→ap-equiv C.emb-is-embedding)
                  (is-embedding→ap-equiv D.emb-is-embedding))
                (emb×-≡-equiv .snd)))
          where
            path
              : (λ p → emb×-≡-equiv .fst
                  (ap C.emb (ap fst p) , ap D.emb (ap snd p)))
              ≡ ap emb×
            path = refl

        emb×-is-embedding : is-embedding emb×
        emb×-is-embedding =
          image-fibers-contr→is-embedding λ s →
            ap-equiv→image-fibers-contr λ s' →
              emb×-ap-equiv {s = s} {s' = s'}

        emb×-composite
          : emb× (f₁ C.⨾ g₁) (f₂ D.⨾ g₂)
            ≡ target× f₁ f₂ g₁ g₂
        emb×-composite =
          funext λ w → funext λ a → funext λ v → funext λ b →
            Σ-path
              (C.emb-composite-pt f₁ g₁
                (fst w) (fst a) (fst v) (fst b))
              (D.emb-composite-pt f₂ g₂
                (snd w) (snd a) (snd v) (snd b))

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

  π₁ : functor (C ×cat D) C
  π₁ .functor.map = fst
  π₁ .functor.hmap = fst
  π₁ .functor.preserves-comp _ _ = refl
  π₁ .functor.preserves-neutral {f = f₁ , f₂} (nl , nr) =
    (×-is-equiv-fst D.idn nl) , (×-is-equiv-fst D.idn nr)

  π₂ : functor (C ×cat D) D
  π₂ .functor.map = snd
  π₂ .functor.hmap = snd
  π₂ .functor.preserves-comp _ _ = refl
  π₂ .functor.preserves-neutral {f = f₁ , f₂} (nl , nr) =
    (×-is-equiv-snd C.idn nl) , (×-is-equiv-snd C.idn nr)
```
