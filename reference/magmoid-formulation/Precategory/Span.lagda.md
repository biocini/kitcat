Lane Biocini, February 2025

Wild category of spans over a category with pullbacks.

References:
- Halley, Mimram (2024), "Polynomials in Homotopy Type Theory as a Kleisli Category"

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Span where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel
open import Core.Kan hiding (assoc; unitl; unitr)
open import Core.Transport
open import Core.Equiv

open import Cat.Base

private variable
  u v : Level

module span-def {u v} (C : precategory u v) where
  open Cat C

  Span : ob → ob → Type (u ⊔ v)
  Span a b = Σ x ∶ ob , hom x a × hom x b

  pattern span x s t = x , s , t

  apex : ∀ {a b} → Span a b → ob
  apex (span x _ _) = x

  src : ∀ {a b} (σ : Span a b) → hom (apex σ) a
  src (span _ s _) = s

  tgt : ∀ {a b} (σ : Span a b) → hom (apex σ) b
  tgt (span _ _ t) = t

module span-ops {u v} (C : precategory u v) where
  open Cat C
  open span-def C

  flip-span : ∀ {a b} → Span a b → Span b a
  flip-span (span x s t) = span x t s

  flip-invol : ∀ {a b} (σ : Span a b) → flip-span (flip-span σ) ≡ σ
  flip-invol σ = refl

  L : ∀ {a b} → hom a b → Span a b
  L {a} f = span a idn f

  R : ∀ {a b} → hom a b → Span b a
  R {a} f = span a f idn

  R≡flip-L : ∀ {a b} (f : hom a b) → R f ≡ flip-span (L f)
  R≡flip-L f = refl

  L-id : ∀ {a} → L (idn {a}) ≡ span a idn idn
  L-id = refl

  R-id : ∀ {a} → R (idn {a}) ≡ span a idn idn
  R-id = refl

module span-comp {u v} (C : precategory u v) where
  open Cat C
  open span-def C

  module _ (has-pb : ∀ {b c d} (f : hom b d) (g : hom c d) → pullback f g) where

    id-span : ∀ {a} → Span a a
    id-span {a} = span a idn idn

    module compose {a b c : ob} (σ : Span a b) (τ : Span b c) where
      private
        pb : pullback (tgt σ) (src τ)
        pb = has-pb (tgt σ) (src τ)
        module pb = pullback pb

      comp-apex : ob
      comp-apex = pb.apex

      comp-src : hom comp-apex a
      comp-src = pb.π₁ ⨾ src σ

      comp-tgt : hom comp-apex c
      comp-tgt = pb.π₂ ⨾ tgt τ

      comp : Span a c
      comp = span comp-apex comp-src comp-tgt

    _⨾ˢ_ : ∀ {a b c} → Span a b → Span b c → Span a c
    σ ⨾ˢ τ = compose.comp σ τ

    infixr 40 _⨾ˢ_

module span-iso {u v} (C : precategory u v) where
  open Cat C
  open span-def C

  is-span-iso : ∀ {a b} → Span a b → Type (u ⊔ v)
  is-span-iso (span x s t) = is-eqv s × is-eqv t

module span-functorial {u v u' v'} (C : precategory u v) (D : precategory u' v') where
  open span-def

  module _ (F : functor C D) where
    private
      module C = Cat C
      module D = Cat D
      module F = functor F

    map-span : ∀ {a b} → Span C a b → Span D (F.ob a) (F.ob b)
    map-span (span x s t) = span (F.ob x) (F.map s) (F.map t)

module Span-U {u} where
  open import Core.Data.Sum
  open import Cat.Braid

  Span : Type u → Type u → Type (u ₊)
  Span A B = Σ X ∶ Type u , (X → A) × (X → B)

  pattern span X s t = X , s , t

  id-span : {A : Type u} → Span A A
  id-span {A} = span A id id

  flip-span : {A B : Type u} → Span A B → Span B A
  flip-span (span X s t) = span X t s

  flip-invol : {A B : Type u} (σ : Span A B) → flip-span (flip-span σ) ≡ σ
  flip-invol σ = refl

  L : {A B : Type u} → (A → B) → Span A B
  L {A} f = span A id f

  R : {A B : Type u} → (A → B) → Span B A
  R {A} f = span A f id

  R≡flip-L : {A B : Type u} (f : A → B) → R f ≡ flip-span (L f)
  R≡flip-L f = refl

  module _ {A B C : Type u} where
    _⨾ˢ_ : Span A B → Span B C → Span A C
    span X s t ⨾ˢ span Y s' t' = span pullback-type (s ∘ pb-π₁) (t' ∘ pb-π₂)
      where
        pullback-type : Type u
        pullback-type = Σ (x , y) ∶ X × Y , t x ≡ s' y

        pb-π₁ : pullback-type → X
        pb-π₁ ((x , _) , _) = x

        pb-π₂ : pullback-type → Y
        pb-π₂ ((_ , y) , _) = y

  module span-products where
    _⊕_ : Type u → Type u → Type u
    A ⊕ B = A ⊎ B

    ⊕-proj₁ : {A B : Type u} → Span (A ⊕ B) A
    ⊕-proj₁ {A} = span A inl id

    ⊕-proj₂ : {A B : Type u} → Span (A ⊕ B) B
    ⊕-proj₂ {B = B} = span B inr id

    module _ {A B X : Type u} where
      ⊕-pair : Span X A → Span X B → Span X (A ⊕ B)
      ⊕-pair (P , f , p) (Q , g , q) = (P ⊎ Q) , src-map , tgt-map
        where
          src-map : P ⊎ Q → X
          src-map (inl x) = f x
          src-map (inr y) = g y
          tgt-map : P ⊎ Q → A ⊎ B
          tgt-map (inl x) = inl (p x)
          tgt-map (inr y) = inr (q y)

      ⊕-split : Span X (A ⊕ B) → Span X A × Span X B
      ⊕-split σ = (Wa , ha , ka) , (Wb , hb , kb)
        where
          W = σ .fst
          h = σ .snd .fst
          k = σ .snd .snd
          Wa = Σ w ∶ W , Σ a ∶ A , k w ≡ inl a
          Wb = Σ w ∶ W , Σ b ∶ B , k w ≡ inr b
          ha : Wa → X
          ha (w , _ , _) = h w
          ka : Wa → A
          ka (_ , a , _) = a
          hb : Wb → X
          hb (w , _ , _) = h w
          kb : Wb → B
          kb (_ , b , _) = b

  module span-monoidal where
    _⊗_ : Type u → Type u → Type u
    A ⊗ B = A × B

    𝟙 : Type u
    𝟙 = Unit

    ⊗-assoc : {A B C : Type u} → ((A ⊗ B) ⊗ C) ≃ (A ⊗ (B ⊗ C))
    ⊗-assoc = iso→equiv
      (λ ((a , b) , c) → a , b , c)
      (λ (a , b , c) → (a , b) , c)
      (λ _ → refl)
      (λ _ → refl)

    ⊗-comm : {A B : Type u} → (A ⊗ B) ≃ (B ⊗ A)
    ⊗-comm = iso→equiv (λ (a , b) → b , a) (λ (b , a) → a , b) (λ _ → refl) (λ _ → refl)

    ⊗-unit-l : {A : Type u} → (𝟙 ⊗ A) ≃ A
    ⊗-unit-l = iso→equiv (λ (_ , a) → a) (λ a → liftℓ tt , a) (λ _ → refl) (λ _ → refl)

    ⊗-unit-r : {A : Type u} → (A ⊗ 𝟙) ≃ A
    ⊗-unit-r = iso→equiv (λ (a , _) → a) (λ a → a , liftℓ tt) (λ _ → refl) (λ _ → refl)

  module span-closed where
    open span-monoidal

    _⊸_ : Type u → Type u → Type u
    A ⊸ B = A ⊗ B

    hom-eq : {A B C : Type u} → Span (A ⊗ B) C ≃ Span A (B ⊗ C)
    hom-eq {A} {B} {C} = iso→equiv fwd bwd sec retr
      where
        fwd : Span (A × B) C → Span A (B × C)
        fwd (span X s t) = span X (fst ∘ s) (λ x → snd (s x) , t x)

        bwd : Span A (B × C) → Span (A × B) C
        bwd (span Y s' t') = span Y (λ y → s' y , fst (t' y)) (snd ∘ t')

        sec : (σ : Span (A × B) C) → bwd (fwd σ) ≡ σ
        sec (span X s t) = refl

        retr : (τ : Span A (B × C)) → fwd (bwd τ) ≡ τ
        retr (span Y s' t') = refl
```
