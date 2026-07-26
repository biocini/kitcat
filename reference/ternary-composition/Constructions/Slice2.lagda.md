The slice category C/X using composite witnesses instead of
propositional equalities for slice morphisms.

In the original `Cat.Slice`, slice morphisms carry `k ⨾ fB ≡ fA`. The
dep-fill for contraction needs a square in hom, which requires
`hom-is-set`. Here we use composite witnesses `k ⨾ fB => fA` instead,
valued in the function space `∀ w → hom w A → hom w X`.

The `.center` part of the contraction works: composite witness fills
are handled by `is-contr→extend` on `composable-contr`. The `.paths`
part hits the same dep-fill wall: we need a PathP of composite
witnesses over a base path from `idn-contr .paths`, and this is a
square in hom (or equivalently a square in the function space, which
decomposes to pointwise squares in hom). The `is-contr→extend`
approach on `composable-contr` cannot produce `composite h fA fW`
directly because the total fiber `Σ s , composite h fA s` projects
to a witness at `s = .fst`, not at `fW`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Base

module Cat.Slice2 {o h} (C : category o h) where

open Cat C

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Sub using (outS; inS; _[_↦_])
open import Core.Transport
  using (is-prop→PathP; is-contr→PathP; subst)
```

## Slice data

```agda

module _ {X : ob} where

  ob/X : Type (o ⊔ h)
  ob/X = Σ A ∶ ob , hom A X

  hom/X : ob/X → ob/X → Type (o ⊔ h)
  hom/X (A , fA) (B , fB) =
    Σ k ∶ hom A B , k ⨾ fB => fA

```

## Yoneda map

```agda

  private
    yon-bridge
      : ∀ {A B W : ob} (k : hom A B) (m : hom W A)
        (w : ob) (n : hom w W)
      → yon k w (yon m w n) ≡ yon (yon k W m) w n
    yon-bridge k m w n =
      sym (happly (happly (yon-composite m k) w) n)
      ∙ happly (happly (ap yon (comp-eq m k)) w) n

  yon/X
    : ∀ {a b : ob/X} → hom/X a b
    → ∀ w → hom/X w a → hom/X w b
  yon/X {A , fA} {B , fB} (k , α) (W , fW) (m , β) =
    yon k W m , γ
    where
    γ : yon k W m ⨾ fB => fW
    γ j w n = pcom
      (sym (happly (happly β w) n))
      (λ j₁ → α j₁ w (yon m w n))
      (λ j₁ → yon fB w (yon-bridge k m w n j₁))
      j

  yon-op/X
    : ∀ {a b : ob/X} → hom/X a b
    → ∀ z → hom/X b z → hom/X a z
  yon-op/X {a} f z g = yon/X g a f

```

## Identity

```agda

  idn/X : ∀ {a : ob/X} → hom/X a a
  idn/X {_ , fA} = idn , α-idn
    where
    α-idn : idn ⨾ fA => fA
    α-idn j w m = yon fA w (yon-idn-pt w m (~ j))

```

## Covariant identity contraction

```agda

  idn/X-contr
    : ∀ {a : ob/X}
    → is-contr
        (fiber (yon/X {a} {a}) (λ _ → id))
  idn/X-contr {a@(A , fA)} .center = idn/X , wit
    where
    wit : yon/X idn/X ≡ (λ _ → id)
    wit i (W , fW) (m , β) =
      yon-idn-pt W m i
      , dep-wit i
      where
      dep-wit
        : ∀ (i : I) → (yon-idn-pt W m i) ⨾ fA => fW
      dep-wit i = {! !}

  idn/X-contr {a@(A , fA)} .paths y = {! !}

```
