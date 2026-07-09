Lane Biocini
March 2026

Rezk completion for virtual infinity-groupoids. Given a category
where every morphism is neutral (an infinity-groupoid), the Rezk
type is a HIT quotient that identifies objects connected by
morphisms. The four constructors are: `q` (points), `seg`
(paths from morphisms), `seg∙` (composition compatibility), and
`seg₁` (identity maps to refl).

The encode half of the path characterization is complete:
`encode ∘ decode ~ id` holds via `ua-β` and `unitl`.

The decode half (the retraction) requires a generalized
`decode-gen : ∀ r → Code r → q x₀ ≡ r` by Rezk-elimination,
then `J` for the retraction. The `q` and `seg` cases are done;
the `seg` case uses `SinglP-contr` to build the transport
round-trip `c₀ ⨾ g ≡ c₁`, and `cat.fill` for the square base.
The `seg∙` and `seg₁` cases remain — they are 3-cubes in Rezk
guided by `ua-comp-square` and `ua-idn-square` respectively.

No `squash`/truncation constructor is added: the goal is to
derive the path characterization from the categorical structure
alone (no assumed truncation), since Kitcat's `category` is meant
to model higher categories in general.

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
open import Core.Transport.Properties using (SinglP-contr)
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

## Retraction: decode ∘ encode ~ id

The retraction goes via a generalized `decode-gen : ∀ r →
Code r → q x₀ ≡ r`, then `J`. The `q` case is `seg`; the `seg`
case is a 2-square built from `cat.fill` and a transport
round-trip; the `seg∙` and `seg₁` cases (3-cubes) remain open.

```agda
      decode-gen : (r : Rezk) → Code r → q x₀ ≡ r
      decode-gen (q y) f = seg f
      decode-gen (seg g i) c j =
        hcom (∂ i ∨ ∂ j) λ where
          k (i = i0) → seg c j
          k (i = i1) → α k j
          k (j = i0) → q x₀
          k (j = i1) → seg g i
          k (k = i0) → cat.fill (seg c₀) (seg g) j i
        where
          A : I → Type h
          A k = Code (seg g k)

          c₀ : C.hom x₀ _
          c₀ = coei0 A i c

          c₁ : C.hom x₀ _
          c₁ = coei1 A i c

          c₀⨾g≡c₁ : (c₀ C.⨾ g) ≡ c₁
          c₀⨾g≡c₁ =
            sym (ua-β (post-equiv g) c₀)
            ∙ ap fst (SinglP-contr {A = A} c₀ .paths (c₁ , c-line))
            where
              c-line : PathP A c₀ c₁
              c-line k = coe A i k c

          α : (seg c₀ ∙ seg g) ≡ seg c₁
          α = sym (seg∙ c₀ g) ∙ ap seg c₀⨾g≡c₁
      decode-gen (seg∙ f g i j) c k = {!!}
      decode-gen (seg₁ i j) c k = {!!}
```

The retraction is then `J` with motive `decode-gen r (subst Code
p idn) ≡ p`, whose base case reduces to `seg₁`.

```agda
      retraction : ∀ {y} (p : q x₀ ≡ q y)
        → decode-gen (q y) (encode p) ≡ p
      retraction {y} = J
        (λ r p → decode-gen r (subst Code p C.idn) ≡ p)
        (ap (decode-gen (q x₀)) (transport-refl C.idn) ∙ seg₁)
```
