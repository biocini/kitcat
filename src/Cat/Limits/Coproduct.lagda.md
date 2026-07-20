Lane Biocini
July 2026

Coproducts over a `Cat.Type` category.

Dual of products. A coproduct cocone over injections `ι₁ : A → S` and
`ι₂ : B → S` from an object `X` consists of a mediating morphism
`m : S → X` together with composite witnesses `ι₁ ⨾ m => f` and
`ι₂ ⨾ m => g`. The mediating morphism goes *out* of the coproduct,
reversing the product's direction; the same β/η reading applies.

Duality is a theorem: a coproduct in `C` is a product in `op C` —
the cocone and the op-cone are fiberwise equivalent, with
`interchange` mediating between the two composite orders.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Limits.Coproduct where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.Base using (contr-ind)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Equiv.Base
  using (_≃_; iso→equiv; is-contr-equiv; Equiv)
open import Core.Equiv.Properties
  using (Σ-equiv-snd; esym; comp-equiv; path-equiv-r)

open import Cat.Type
open import Cat.Op
open import Cat.Base
open import Cat.Morphism
open import Cat.Iso
open import Cat.Limits.Product

module _ {o h} (C : category o h) where
  open category C
  open theory C
  open morphism C
  open iso C

  coproduct-cocone
    : ∀ {A B S : ob} → hom A S → hom B S
    → (X : ob) → hom A X → hom B X → Type (o ⊔ h)
  coproduct-cocone {S = S} ι₁ ι₂ X f g =
    Sigma (hom S X) λ m → (ι₁ ⨾ m => f) × (ι₂ ⨾ m => g)

  is-coproduct
    : ∀ {A B S : ob}
      (ι₁ : hom A S) (ι₂ : hom B S)
    → Type (o ⊔ h)
  is-coproduct ι₁ ι₂ =
    ∀ {X} (f : hom _ X) (g : hom _ X)
    → is-contr (coproduct-cocone ι₁ ι₂ X f g)

  module Coproduct
    {A B S : ob} {ι₁ : hom A S} {ι₂ : hom B S}
    (coprod : is-coproduct ι₁ ι₂)
    where
    copair : ∀ {X} → hom A X → hom B X → hom S X
    copair f g = coprod f g .center .fst

    copair-factors₁
      : ∀ {X} (f : hom A X) (g : hom B X)
      → ι₁ ⨾ copair f g => f
    copair-factors₁ f g = coprod f g .center .snd .fst

    copair-factors₂
      : ∀ {X} (f : hom A X) (g : hom B X)
      → ι₂ ⨾ copair f g => g
    copair-factors₂ f g = coprod f g .center .snd .snd

    copair-ind
      : ∀ {u X} (f : hom A X) (g : hom B X)
      → (Q : (m : hom S X)
           → ι₁ ⨾ m => f → ι₂ ⨾ m => g
           → Type u)
      → Q (copair f g)
          (copair-factors₁ f g) (copair-factors₂ f g)
      → ∀ m α β → Q m α β
    copair-ind f g Q base m α β =
      contr-ind (coprod f g)
        (λ where (m , α , β) → Q m α β)
        base (m , α , β)

    copair-β₁
      : ∀ {X} (f : hom A X) (g : hom B X)
      → ι₁ ⨾ copair f g ≡ f
    copair-β₁ f g = cast-path (copair-factors₁ f g)

    copair-β₂
      : ∀ {X} (f : hom A X) (g : hom B X)
      → ι₂ ⨾ copair f g ≡ g
    copair-β₂ f g = cast-path (copair-factors₂ f g)

    copair-η
      : ∀ {X} (f : hom A X) (g : hom B X)
      → (m : hom S X)
      → ι₁ ⨾ m => f → ι₂ ⨾ m => g
      → copair f g ≡ m
    copair-η f g =
      copair-ind f g
        (λ m _ _ → copair f g ≡ m) refl
```

## Coproduct η-expansion

The copairing of the injections is the identity: `idn` factors
through each injection as itself, since `ι ⨾ idn => ι` is
`emb ι ≡ emb ι ▾ idn`, collapsed by `▾-idn`.

```agda
  module _
    {A B S : ob} {ι₁ : hom A S} {ι₂ : hom B S}
    (coprod : is-coproduct ι₁ ι₂)
    where
    open Coproduct coprod

    private
      idn-cofactors₁ : ι₁ ⨾ idn S => ι₁
      idn-cofactors₁ = sym (▾-idn (emb ι₁))

      idn-cofactors₂ : ι₂ ⨾ idn S => ι₂
      idn-cofactors₂ = sym (▾-idn (emb ι₂))

    copair-η-idn : copair ι₁ ι₂ ≡ idn S
    copair-η-idn =
      copair-η ι₁ ι₂ (idn S) idn-cofactors₁ idn-cofactors₂
```

## Coproduct uniqueness up to isomorphism

Two coproducts for the same diagram are isomorphic. The mediating
morphisms from each coproduct's universal property compose to the
identity by η-expansion.

```agda
  coproduct-unique
    : ∀ {A B S S' : ob}
      {ι₁ : hom A S} {ι₂ : hom B S}
      {ι₁' : hom A S'} {ι₂' : hom B S'}
    → (coprod : is-coproduct ι₁ ι₂)
    → (coprod' : is-coproduct ι₁' ι₂')
    → S ≅ S'
  coproduct-unique
    {ι₁ = ι₁} {ι₂} {ι₁'} {ι₂'} coprod coprod' =
    φ , ψ , φψ≡idn , ψφ≡idn
    where
      module Co  = Coproduct coprod
      module Co' = Coproduct coprod'
      φ : hom _ _
      φ = Co.copair ι₁' ι₂'
      ψ : hom _ _
      ψ = Co'.copair ι₁ ι₂

      ψφ≡idn : ψ ⨾ φ ≡ idn _
      ψφ≡idn =
        sym (Co'.copair-η ι₁' ι₂' (ψ ⨾ φ)
          (cast-path⁻¹ (assoc ι₁' ψ φ
            ∙ Co'.copair-β₁ ι₁ ι₂ ▹ φ
            ∙ Co.copair-β₁ ι₁' ι₂'))
          (cast-path⁻¹ (assoc ι₂' ψ φ
            ∙ Co'.copair-β₂ ι₁ ι₂ ▹ φ
            ∙ Co.copair-β₂ ι₁' ι₂')))
        ∙ copair-η-idn coprod'

      φψ≡idn : φ ⨾ ψ ≡ idn _
      φψ≡idn =
        sym (Co.copair-η ι₁ ι₂ (φ ⨾ ψ)
          (cast-path⁻¹ (assoc ι₁ φ ψ
            ∙ Co.copair-β₁ ι₁' ι₂' ▹ ψ
            ∙ Co'.copair-β₁ ι₁ ι₂))
          (cast-path⁻¹ (assoc ι₂ φ ψ
            ∙ Co.copair-β₂ ι₁' ι₂' ▹ ψ
            ∙ Co'.copair-β₂ ι₁ ι₂)))
        ∙ copair-η-idn coprod
```

## Duality

A coproduct in `C` is a product in `op C`. The op-side witness
`embᵒ f ≡ embᵒ m ▾ᵒ ι` unfolds to `⟲ (emb f) ≡ ⟲ (ι ▴ emb m)`, so
the cocone and the op-cone are fiberwise equivalent by
post-composition with `interchange` under `⟲`.

```agda
module dual {o h} (C : category o h) where
  open category C
  open theory C
  open op C using (⟲; ⟳)
  private module Cᵒ = category (op C)

  private
    ap-⟲-equiv : ∀ {x y} {α β : composite y x} → (α ≡ β) ≃ (⟲ α ≡ ⟲ β)
    ap-⟲-equiv = iso→equiv (ap ⟲) (ap ⟳) (λ _ → refl) (λ _ → refl)

    ×-cong : ∀ {u v w x} {A : Type u} {B : Type v} {Cc : Type w} {D : Type x}
           → A ≃ B → Cc ≃ D → (A × Cc) ≃ (B × D)
    ×-cong {A = A} {B} {Cc} {D} e d = iso→equiv fwd bwd sec retr where
      fwd : A × Cc → B × D
      fwd (a , c) = Equiv.fwd e a , Equiv.fwd d c

      bwd : B × D → A × Cc
      bwd (b , c') = Equiv.inv e b , Equiv.inv d c'

      sec : ∀ p → bwd (fwd p) ≡ p
      sec (a , c) i = Equiv.unit e a i , Equiv.unit d c i

      retr : ∀ p → fwd (bwd p) ≡ p
      retr (b , c') i = Equiv.counit e b i , Equiv.counit d c' i

    wit-equiv
      : ∀ {x y z} (ι : hom x y) (m : hom y z) (f : hom x z)
      → (emb f ≡ emb ι ▾ m) ≃ (Cᵒ.emb f ≡ Cᵒ.emb m Cᵒ.▾ ι)
    wit-equiv ι m f =
      (_ , comp-equiv
            (path-equiv-r (interchange ι m) .snd)
            (ap-⟲-equiv .snd))

  cone-dual
    : ∀ {A B S X : ob} (ι₁ : hom A S) (ι₂ : hom B S)
      (f : hom A X) (g : hom B X)
    → coproduct-cocone C ι₁ ι₂ X f g ≃ product-cone (op C) ι₁ ι₂ X f g
  cone-dual ι₁ ι₂ f g =
    Σ-equiv-snd λ m → ×-cong (wit-equiv ι₁ m f) (wit-equiv ι₂ m g)

  is-coproduct-dual
    : ∀ {A B S : ob} (ι₁ : hom A S) (ι₂ : hom B S)
    → is-coproduct C ι₁ ι₂ ≃ is-product (op C) ι₁ ι₂
  is-coproduct-dual ι₁ ι₂ =
    iso→equiv fwd bwd (λ _ → coprod-prop _ _) (λ _ → prod-prop _ _)
    where
      fwd : is-coproduct C ι₁ ι₂ → is-product (op C) ι₁ ι₂
      fwd cp {X} f g = is-contr-equiv (esym (cone-dual ι₁ ι₂ f g)) (cp f g)

      bwd : is-product (op C) ι₁ ι₂ → is-coproduct C ι₁ ι₂
      bwd pd {X} f g = is-contr-equiv (cone-dual ι₁ ι₂ f g) (pd f g)

      coprod-prop : is-prop (is-coproduct C ι₁ ι₂)
      coprod-prop p q i {X} f g =
        is-contr-is-prop _ (p {X} f g) (q {X} f g) i

      prod-prop : is-prop (is-product (op C) ι₁ ι₂)
      prod-prop p q i {X} f g =
        is-contr-is-prop _ (p {X} f g) (q {X} f g) i

module _ {o h} (C : category o h) where
  open category C

  is-product-dual
    : ∀ {A B P : ob} (π₁ : hom P A) (π₂ : hom P B)
    → is-product C π₁ π₂ ≃ is-coproduct (op C) π₁ π₂
  is-product-dual π₁ π₂ = esym (dual.is-coproduct-dual (op C) π₁ π₂)
```
