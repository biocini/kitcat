Lane Biocini
July 2026

Products over a `Cat.Type` category.

A product cone over projections `π₁ : P → A` and `π₂ : P → B` from an
object `X` consists of a mediating morphism `m : X → P` together with
composite witnesses `m ⨾ π₁ => f` and `m ⨾ π₂ => g`. The product
condition asks this cone type to be contractible for all `f` and `g`.

- β-rules are the commuting conditions, extracted from the composite
  witnesses;
- the η-rule is uniqueness of the mediating morphism, obtained by
  induction at `Q = ⟨ f , g ⟩ ≡_`;
- induction is the full dependent eliminator, subsuming both.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Limits.Product where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base using (contr-ind)

open import Cat.Type
open import Cat.Base
open import Cat.Morphism
open import Cat.Morphism.Iso

module _ {o h} (C : category o h) where
  open category C
  open theory C
  open morphism C
  open iso C

  product-cone
    : ∀ {A B P : ob} → hom P A → hom P B
    → (X : ob) → hom X A → hom X B → Type (o ⊔ h)
  product-cone {P = P} π₁ π₂ X f g =
    Sigma (hom X P) λ m → (m ⨾ π₁ => f) × (m ⨾ π₂ => g)

  is-product
    : ∀ {A B P : ob}
      (π₁ : hom P A) (π₂ : hom P B)
    → Type (o ⊔ h)
  is-product π₁ π₂ =
    ∀ {X} (f : hom X _) (g : hom X _)
    → is-contr (product-cone π₁ π₂ X f g)

  module Product
    {A B P : ob} {π₁ : hom P A} {π₂ : hom P B}
    (prod : is-product π₁ π₂)
    where

    ⟨_,_⟩ : ∀ {X} → hom X A → hom X B → hom X P
    ⟨ f , g ⟩ = prod f g .center .fst

    ⟨,⟩-factors₁
      : ∀ {X} (f : hom X A) (g : hom X B)
      → ⟨ f , g ⟩ ⨾ π₁ => f
    ⟨,⟩-factors₁ f g = prod f g .center .snd .fst

    ⟨,⟩-factors₂
      : ∀ {X} (f : hom X A) (g : hom X B)
      → ⟨ f , g ⟩ ⨾ π₂ => g
    ⟨,⟩-factors₂ f g = prod f g .center .snd .snd

    ⟨,⟩-ind
      : ∀ {u X} (f : hom X A) (g : hom X B)
      → (Q : (m : hom X P)
           → m ⨾ π₁ => f → m ⨾ π₂ => g
           → Type u)
      → Q ⟨ f , g ⟩
          (⟨,⟩-factors₁ f g) (⟨,⟩-factors₂ f g)
      → ∀ m α β → Q m α β
    ⟨,⟩-ind f g Q base m α β =
      contr-ind (prod f g)
        (λ where (m , α , β) → Q m α β)
        base (m , α , β)

    ⟨,⟩-β₁
      : ∀ {X} (f : hom X A) (g : hom X B)
      → ⟨ f , g ⟩ ⨾ π₁ ≡ f
    ⟨,⟩-β₁ f g = cast-path (⟨,⟩-factors₁ f g)

    ⟨,⟩-β₂
      : ∀ {X} (f : hom X A) (g : hom X B)
      → ⟨ f , g ⟩ ⨾ π₂ ≡ g
    ⟨,⟩-β₂ f g = cast-path (⟨,⟩-factors₂ f g)

    ⟨,⟩-η
      : ∀ {X} (f : hom X A) (g : hom X B)
      → (m : hom X P)
      → m ⨾ π₁ => f → m ⨾ π₂ => g
      → ⟨ f , g ⟩ ≡ m
    ⟨,⟩-η f g =
      ⟨,⟩-ind f g (λ m _ _ → ⟨ f , g ⟩ ≡ m) refl
```

## Product η-expansion

The pairing of the projections is the identity: `idn` factors through
each projection as itself, since `idn ⨾ π => π` is exactly
`emb π ≡ emb (idn) · π`, and `emb-idn-absorb` proves the composite
`emb (idn) · π` collapses to `emb π`. Uniqueness of the product cone
does the rest.

```agda
  module _
    {A B P : ob} {π₁ : hom P A} {π₂ : hom P B}
    (prod : is-product π₁ π₂)
    where
    open Product prod

    private
      idn-factors₁ : idn P ⨾ π₁ => π₁
      idn-factors₁ = sym (emb-idn-absorb π₁)

      idn-factors₂ : idn P ⨾ π₂ => π₂
      idn-factors₂ = sym (emb-idn-absorb π₂)

    ⟨,⟩-η-idn : ⟨ π₁ , π₂ ⟩ ≡ idn P
    ⟨,⟩-η-idn = ⟨,⟩-η π₁ π₂ (idn P) idn-factors₁ idn-factors₂
```

## Product uniqueness up to isomorphism

Two products for the same diagram are isomorphic. The mediating
morphisms from each product's universal property compose to the
identity by η-expansion.

```agda
  product-unique
    : ∀ {A B P P' : ob}
      {π₁ : hom P A} {π₂ : hom P B}
      {π₁' : hom P' A} {π₂' : hom P' B}
    → (prod : is-product π₁ π₂)
    → (prod' : is-product π₁' π₂')
    → P ≅ P'
  product-unique {π₁ = π₁} {π₂} {π₁'} {π₂'} prod prod' =
    ψ , φ , ψφ≡idn , φψ≡idn
    where
      module Π  = Product prod
      module Π' = Product prod'
      φ : hom _ _
      φ = Π.⟨ π₁' , π₂' ⟩
      ψ : hom _ _
      ψ = Π'.⟨ π₁ , π₂ ⟩

      ψφ≡idn : ψ ⨾ φ ≡ idn _
      ψφ≡idn =
        sym (Π.⟨,⟩-η π₁ π₂ (ψ ⨾ φ)
          (cast-path⁻¹ (sym (assoc ψ φ π₁)
            ∙ ψ ◃ Π.⟨,⟩-β₁ π₁' π₂'
            ∙ Π'.⟨,⟩-β₁ π₁ π₂))
          (cast-path⁻¹ (sym (assoc ψ φ π₂)
            ∙ ψ ◃ Π.⟨,⟩-β₂ π₁' π₂'
            ∙ Π'.⟨,⟩-β₂ π₁ π₂)))
        ∙ ⟨,⟩-η-idn prod

      φψ≡idn : φ ⨾ ψ ≡ idn _
      φψ≡idn =
        sym (Π'.⟨,⟩-η π₁' π₂' (φ ⨾ ψ)
          (cast-path⁻¹ (sym (assoc φ ψ π₁')
            ∙ φ ◃ Π'.⟨,⟩-β₁ π₁ π₂
            ∙ Π.⟨,⟩-β₁ π₁' π₂'))
          (cast-path⁻¹ (sym (assoc φ ψ π₂')
            ∙ φ ◃ Π'.⟨,⟩-β₂ π₁ π₂
            ∙ Π.⟨,⟩-β₂ π₁' π₂')))
        ∙ ⟨,⟩-η-idn prod'
```
