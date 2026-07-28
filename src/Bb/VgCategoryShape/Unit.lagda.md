What the unit package pins.

Interchange makes each self-filled half of neutrality a statement about
a composition action, and associativity turns each into the square of
one — so a neutral edge is an isomorphism in the composition-action
sense, with no idempotence spent. Cancelling against the unit laws then
makes the idempotence component a based path, and the type of neutral
idempotents at an object contractible.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VgCategoryShape.Unit where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.Path.Base
open import Core.Equiv.Base
  using (_≃_; is-equiv; is-contr-equiv; module Equiv)
open import Core.Equiv.Properties
  using (esym; _∙e_; Σ-equiv-snd; bi-inv→equiv)
open import Core.Function.Embedding
  using (equiv→lc; is-embedding→ap-equiv; is-equiv→is-embedding)
open import Core.Transport.Base using (is-prop→PathP; transport)
open import Core.Transport.Properties using (transport-equiv)
open import Core.Transport.J using (subst)

open import Bb.VgCategoryShape.Type
open import Bb.VgCategoryShape.Base
```

```agda
module _ {o h} (M : hcategory o h) where
  open hcat M
```

## A neutral edge is a composition-action isomorphism

A map whose square is an equivalence is one.

```agda
  private
    square-equiv→equiv
      : ∀ {u} {A : Type u} {g : A → A}
      → is-equiv (λ a → g (g a)) → is-equiv g
    square-equiv→equiv {g = g} eq = bi-inv→equiv
      ( ((λ b → g (E.inv b)) , λ b → E.counit b)
      , ((λ b → E.inv (g b)) , λ a → E.unit a) )
      where module E = Equiv ((λ a → g (g a)) , eq)

  neutral→pre
    : ∀ {x} (e : hom x x) → is-neutral e
    → ∀ {z} → is-equiv (λ (k : hom x z) → e ⨾⁺ k)
  neutral→pre {x} e u {z} = square-equiv→equiv
    (subst is-equiv (funext step) (u .fst {z}))
    where
      step : (k : hom x z) → reflect e ((x , e) , (z , k)) ≡ e ⨾⁺ (e ⨾⁺ k)
      step k =
        sym (le-is-coact e k)
        ∙ ⨾⁺-is-coact (e ⨾⁻ e) k
        ∙ ap (_⨾⁺ k) (interchange e e)
        ∙ assoc⁺ e e k

  neutral→post
    : ∀ {x} (e : hom x x) → is-neutral e
    → ∀ {w} → is-equiv (λ (g : hom w x) → g ⨾⁻ e)
  neutral→post {x} e u {w} = square-equiv→equiv
    (subst is-equiv (funext step) (u .snd {w}))
    where
      step : (g : hom w x) → reflect e ((w , g) , (x , e)) ≡ (g ⨾⁻ e) ⨾⁻ e
      step g =
        sym (re-is-act e g)
        ∙ ⨾⁻-is-act (e ⨾⁺ e) g
        ∙ ap (g ⨾⁻_) (sym (interchange e e))
        ∙ assoc⁻ g e e
```

## Idempotence is a based path to the unit

```agda
  cancel : ∀ {x} (e : hom x x) → is-neutral e → e ⨾⁻ e ≡ e → e ≡ idn
  cancel e u p = equiv→lc (neutral→pre e u)
    (sym (interchange e e) ∙ p ∙ sym (unitr⁺ e))

  cancel-equiv : ∀ {x} (e : hom x x) (u : is-neutral e)
               → (e ⨾⁻ e ≡ e) ≃ (e ≡ idn)
  cancel-equiv {x} e u = esym (ap-pre ∙e shift)
    where
      ap-pre : (e ≡ idn) ≃ (e ⨾⁺ e ≡ e ⨾⁺ idn)
      ap-pre = ap (e ⨾⁺_)
             , is-embedding→ap-equiv
                 (is-equiv→is-embedding (neutral→pre e u))

      P : (e ⨾⁺ e ≡ e ⨾⁺ idn) ≡ (e ⨾⁻ e ≡ e)
      P i = interchange e e (~ i) ≡ unitr⁺ e i

      shift : (e ⨾⁺ e ≡ e ⨾⁺ idn) ≃ (e ⨾⁻ e ≡ e)
      shift = transport P , transport-equiv P
```

## The package is contractible

Being a neutral idempotent at an object is not merely propositional:
the type of such edges is contractible, with the unit as its centre. So
`unit` is a property field, and its inhabitant is determined.

```agda
  private
    pinned : (x : ob) → Type (o ⊔ h)
    pinned x = Σ e ∶ hom x x , is-neutral e × (e ≡ idn)

    pinned-contr : (x : ob) → is-contr (pinned x)
    pinned-contr x .center = idn , idn-neutral , refl
    pinned-contr x .paths (e , u , q) i =
        q (~ i)
      , is-prop→PathP (λ j → is-neutral-is-prop (q (~ j))) idn-neutral u i
      , λ j → q (~ i ∨ j)

  unit-contr : (x : ob) → is-contr (is-unital x)
  unit-contr x =
    is-contr-equiv
      (Σ-equiv-snd λ e → Σ-equiv-snd λ u → cancel-equiv e u)
      (pinned-contr x)

  is-unital-is-prop : (x : ob) → is-prop (is-unital x)
  is-unital-is-prop x = is-contr→is-prop (unit-contr x)
```
