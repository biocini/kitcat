Lane Biocini
July 2026

Spike: the product of categories by representability.

The pointwise product of wild categories is obstructed (joint
context families do not decompose). The alternative presentation:
the joint functor-family `E ↦ (E → A) × (E → B)` exists freely,
and a product of `A` and `B` is a category representing it —
projections `π₁, π₂` such that postcomposition pairing is an
equivalence. The terminal category is the unit: functors into it
are contractible, and the unit law holds by postcomposition
identities.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.ProductSpike where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Equiv.Base using (is-equiv; iso→equiv; _≃_)
open import Core.Equiv.Properties using (is-equiv-is-prop)
open import Core.HLevel.Base using (⊤-is-contr; PathP-is-contr; Σ-is-prop; Πi-is-prop)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Functor
open import Cat.Depreciated.Terminal
open import Cat.Depreciated.Morphism
import Cat.Depreciated.Base
```

## The joint functor-family

```agda
module _ {o h o' h'} (A : category o h) (B : category o h) where

  Fam : category o' h' → Type (o ⊔ h ⊔ o' ⊔ h')
  Fam E = functor E A

  Joint : category o' h' → Type (o ⊔ h ⊔ o' ⊔ h')
  Joint E = functor E A × functor E B
```

## Terminal absorption

Functors into the terminal category are contractible: the maps are
determined by the unit type, and every field is a proposition there.

```agda
module _ {o h} (C : category o h) where
  private module T = category terminal-category

  const-functor : functor C terminal-category
  const-functor .functor.map _ = tt
  const-functor .functor.hmap _ = tt
  const-functor .functor.preserves-comp _ _ = refl
  const-functor .functor.preserves-neutral _ =
    (iso→equiv (λ _ → tt) (λ _ → tt) (λ _ → refl) (λ _ → refl) .snd)
    , (iso→equiv (λ _ → tt) (λ _ → tt) (λ _ → refl) (λ _ → refl) .snd)

  private
    ⊤-path-contr : ∀ {x y : ⊤} → is-contr (x ≡ y)
    ⊤-path-contr = PathP-is-contr ⊤-is-contr _ _

    ⊤-square-contr
      : ∀ {x y : ⊤} (p q : x ≡ y) → is-contr (p ≡ q)
    ⊤-square-contr p q = PathP-is-contr ⊤-path-contr p q

    neutral-prop : is-prop (morphism.is-neutral terminal-category tt)
    neutral-prop x y i =
      is-equiv-is-prop _ (x .fst) (y .fst) i
      , is-equiv-is-prop _ (x .snd) (y .snd) i

  terminal-fam-contr : is-contr (functor C terminal-category)
  terminal-fam-contr .center = const-functor
  terminal-fam-contr .paths F i .functor.map _ = tt
  terminal-fam-contr .paths F i .functor.hmap _ = tt
  terminal-fam-contr .paths F i .functor.preserves-comp f g =
    ⊤-square-contr refl (F .functor.preserves-comp f g) .center i
  terminal-fam-contr .paths F i .functor.preserves-neutral n =
    neutral-prop (const-functor .functor.preserves-neutral n)
      (F .functor.preserves-neutral n) i
```

## The product by representability

A product of `A` and `B` is a category `P` with projections such
that postcomposition pairing is an equivalence of functor types.
Naturality in `E` is automatic, since the pairing is postcomposition.

```agda
record is-product
  {o₁ h₁ o₂ h₂ o₃ h₃ o₄ h₄}
  (A : category o₁ h₁) (B : category o₂ h₂) (P : category o₃ h₃)
  : Type₊ (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂ ⊔ o₃ ⊔ h₃ ⊔ o₄ ⊔ h₄)
  where
  field
    π₁ : functor P A
    π₂ : functor P B

  pair : ∀ (E : category o₄ h₄) → functor E P → functor E A × functor E B
  pair E F = (π₁ ∘F F) , (π₂ ∘F F)

  field
    pairing-equiv : ∀ (E : category o₄ h₄) → is-equiv (pair E)
```

## The unit law

Postcomposition with the identity functor is the identity up to the
right unit of path composition, and functors into `𝟙` are unique, so
`A` itself represents the pair `(A , 𝟙)`.

```agda
module _ {o h} (A : category o h) where
  private
    ∘F-unitl : ∀ {C : category o h} (F : functor C A)
             → id-functor A ∘F F ≡ F
    ∘F-unitl F i .functor.map = F .functor.map
    ∘F-unitl F i .functor.hmap = F .functor.hmap
    ∘F-unitl F i .functor.preserves-comp f g =
      Path.unitr (F .functor.preserves-comp f g) i
    ∘F-unitl F i .functor.preserves-neutral =
      F .functor.preserves-neutral

  unit-law : is-product A terminal-category A
  unit-law .is-product.π₁ = id-functor A
  unit-law .is-product.π₂ = const-functor A
  unit-law .is-product.pairing-equiv E =
    iso→equiv fwd bwd sec retr .snd
    where
      fwd : functor E A → functor E A × functor E terminal-category
      fwd F = (id-functor A ∘F F) , (const-functor A ∘F F)

      bwd : functor E A × functor E terminal-category
          → functor E A
      bwd = fst

      sec : ∀ F → bwd (fwd F) ≡ F
      sec F = ∘F-unitl F

      retr : ∀ G → fwd (bwd G) ≡ G
      retr (G , c) i =
        ∘F-unitl G i
        , is-contr→is-prop (terminal-fam-contr E) (const-functor A ∘F G) c i
```
