Lane Biocini
March 2026

Rezk completion for virtual infinity-groupoids. Given a category
where every morphism is neutral (an infinity-groupoid), the Rezk
type is a HIT quotient that identifies objects connected by
morphisms. The four constructors are: `q` (points), `seg`
(paths from morphisms), `seg∙` (composition compatibility), and
`seg₁` (identity maps to refl).

The encode half of the path characterization is complete:
`encode ∘ decode ~ id` holds via `ua-β` and `unitl`. The
decode half (the retraction) requires a generalized decode
by Rezk-elimination, whose `seg∙` and `seg₁` cases involve
filling 3-cubes in the path type of Rezk.

This module uses `--cubical` (not `--erased-cubical`) because
it defines a higher inductive type.

```agda
{-# OPTIONS --cubical --safe --no-guardedness #-}

module Cat.Rezk where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base
open import Core.Transport.J
open import Core.Equiv.Properties
open import Core.Univalence
open import Cat.Type
open import Cat.Base using (module Cat)
```

## Setup

```agda
module _
  {o h} (C : category o h)
  where
  private module C = Virtual C
  open Cat C using (is-neutral)

  is-∞-groupoid : Type (o ⊔ h)
  is-∞-groupoid =
    ∀ {x y} (f : C.hom x y) → is-neutral f
```

## The HIT

```agda
  module _ (gpd : is-∞-groupoid) where

    data Rezk : Type (o ⊔ h) where
      q    : C.ob → Rezk
      seg  : ∀ {x y} → C.hom x y
           → q x ≡ q y
      seg∙ : ∀ {x y z}
           (f : C.hom x y) (g : C.hom y z)
           → seg (f C.⨾ g) ≡ seg f ∙ seg g
      seg₁ : ∀ {x} → seg (C.idn {x}) ≡ refl
```

## The code fibration

Fix a basepoint `x₀ : C.ob`. Post-composition with a
neutral morphism `g` is an equivalence
`hom x₀ y ≃ hom x₀ z`. The `Code` fibration sends `q y`
to `hom x₀ y` and `seg g` to the `ua` of this equivalence.

```agda
    module _ (x₀ : C.ob) where
      private
        post-equiv
          : ∀ {y z} → C.hom y z
          → C.hom x₀ y ≃ C.hom x₀ z
        post-equiv g = (C._⨾ g) , gpd g .snd
```

Post-composition is functorial: it respects composition
and sends the identity to the identity equivalence.

```agda
        post-equiv-comp
          : ∀ {x y z}
            (f : C.hom x y) (g : C.hom y z)
          → post-equiv (f C.⨾ g)
          ≡ post-equiv f ∙e post-equiv g
        post-equiv-comp f g = equiv-path _ _
          (funext λ a → sym (C.assoc a f g))

        post-equiv-idn
          : ∀ {x}
          → post-equiv (C.idn {x}) ≡ aut
        post-equiv-idn = equiv-path _ _
          (funext λ a → C.unitr a)
```

The 2-cell cases of `Code` reduce to paths between
paths in the universe, built from `ua-∙e` and `ua-id`.

```agda
        ua-comp-square
          : ∀ {x y z}
            (f : C.hom x y) (g : C.hom y z)
          → ua (post-equiv (f C.⨾ g))
          ≡ ua (post-equiv f)
            ∙ ua (post-equiv g)
        ua-comp-square f g =
          ap ua (post-equiv-comp f g)
          ∙ ua-∙e (post-equiv f) (post-equiv g)

        ua-idn-square
          : ∀ {x}
          → ua (post-equiv (C.idn {x})) ≡ refl
        ua-idn-square =
          ap ua post-equiv-idn ∙ ua-id
```

```agda
      Code : Rezk → Type h
      Code (q y) = C.hom x₀ y
      Code (seg g i) = ua (post-equiv g) i
      Code (seg∙ f g i j) =
        ua-comp-square f g i j
      Code (seg₁ {x} i j) = ua-idn-square {x} i j
```

## Encode and decode

```agda
      encode : ∀ {y}
        → q x₀ ≡ q y → C.hom x₀ y
      encode p = subst Code p C.idn

      decode : ∀ {y}
        → C.hom x₀ y → q x₀ ≡ q y
      decode f = seg f
```

## Section: encode ∘ decode ~ id

Transporting `idn` along `ua (post-equiv f)` yields
`idn ⨾ f`, which equals `f` by `unitl`.

```agda
      section : ∀ {y} (f : C.hom x₀ y)
        → encode (decode f) ≡ f
      section f =
        ua-β (post-equiv f) C.idn ∙ C.unitl f
```
