Lane Biocini
July 2026

The unit layer over `codep-category` + `codep-coupling`. `codep-unit`
adds the two axioms that make the anchor a genuine unit: the identity's
acted and passenger actions are equivalences. From these the full unit
fragment derives — absorption (`absorb-l`, `absorb-r`), the codependent
identity law `·-idn` (`F · idn ≡ F`), the unit laws `unitl`/`unitr`
(fiber-projected), `emb-image-contr`, and identity uniqueness
`unit-is-prop` via the Kraus chain.

Together with `Cat.Codep.Coupling` this closes the noy-side four-axiom
wiring: `Cat.Type.category ≅ codep-category + codep-coupling +
codep-unit`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Unit where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (is-contr→is-prop; _∙_)
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding using (equiv→lc)

open import Cat.Codep.Base
open import Cat.Codep.Coupling
```

## The unit record

The identity's acted action `noy (idn x)` and passenger action
`yon (idn x)` are equivalences.

```agda
record codep-unit {o h} {ob : Type o}
  (R : codep-category {o} {h} ob) (Coup : codep-coupling R)
  : Type (o ⊔ h) where
  no-eta-equality
  open codep-category R
  open Helpers R
  field
    unit-l-equiv : ∀ {x} {v} → is-equiv (noy (idn x) {v})
    unit-r-equiv : ∀ {x} {w} → is-equiv (yon (idn x) {w})
```

## Absorption and the identity law

`absorb-l`/`absorb-r` cancel the identity's actions via the unit
equivalences; `·-idn` is the headline codependent identity law.

```agda
module UnitDerived {o h} {ob : Type o}
  (R : codep-category {o} {h} ob)
  (Coup : codep-coupling R) (U : codep-unit R Coup) where
  open codep-category R
  open Helpers R
  open codep-coupling Coup
  open codep-unit U
  open CouplingDerived R Coup

  absorb-l : ∀ {x v} (b : hom x v) → noy (idn x) b ≡ b
  absorb-l {x} b = equiv→lc unit-l-equiv noy-idn-idpt
    where
      noy-idn-idpt : noy (idn x) (noy (idn x) b) ≡ noy (idn x) b
      noy-idn-idpt =
        sym (subst (λ t → noy t b ≡ noy (idn x) (noy (idn x) b))
          idem (noy-composite (idn x) (idn x) b))

  absorb-r : ∀ {w x} (a : hom w x) → yon (idn x) a ≡ a
  absorb-r {w} {x} a = equiv→lc unit-r-equiv yon-idn-idpt
    where
      yon-idn-idpt : yon (idn x) (yon (idn x) a) ≡ yon (idn x) a
      yon-idn-idpt =
        sym (subst (λ t → yon t a ≡ yon (idn x) (yon (idn x) a))
          idem (yon-composite (idn x) (idn x) a))

  ·-idn : ∀ {x y} (F : loose x y) → F · idn y ≡ F
  ·-idn F = loose-ext λ γ →
    ap (λ β → F (γ .fst , β)) (absorb-l (γ .snd))
```

## Unit laws and the image fiber

The identity absorbs on the left of `emb`; `emb-image-contr` transports
`compose-contr (idn) f` along that absorption; `unitl`/`unitr` project
from the contractible image fiber.

```agda
  emb-idn-absorb : ∀ {x y} (f : hom x y) → emb (idn x) · f ≡ emb f
  emb-idn-absorb f = loose-ext λ γ →
    interchange (idn _) f (γ .fst .snd .snd) (γ .snd)
    ∙ ap (λ a' → emb f ((γ .fst .fst , (γ .fst .snd .fst , a')) , γ .snd))
        (absorb-r (γ .fst .snd .snd))

  emb-image-contr : ∀ {x y} (f : hom x y) → is-contr (fiber emb (emb f))
  emb-image-contr f =
    subst (λ T → is-contr (fiber emb T))
      (emb-idn-absorb f) (compose-contr (idn _) f)

  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn y ≡ f
  unitr f = ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = (f ⨾ idn _) , (emb-comp f (idn _) ∙ ·-idn (emb f))
      rhs : fiber emb (emb f)
      rhs = f , refl

  unitl : ∀ {x y} (f : hom x y) → idn x ⨾ f ≡ f
  unitl f = ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = (idn _ ⨾ f) , (emb-comp (idn _) f ∙ emb-idn-absorb f)
      rhs : fiber emb (emb f)
      rhs = f , refl
```

## Identity uniqueness

`emb-yon` rewrites `emb f` through `emb idn` at the yon-shifted binder.
`unit-is-prop`: any `e` whose passenger square is an equivalence and
whose binary yon-idempotency `yon e e ≡ e` holds is the identity, by
the Kraus chain (`yon e` squares to itself, is idempotent, so absorbs).

```agda
  emb-yon
    : ∀ {x y} (f : hom x y) {w} (a : hom w x) {v} (b : hom y v)
    → emb f ((v , (w , a)) , b) ≡ emb (idn y) ((v , (w , yon f a)) , b)
  emb-yon {x} {y} f {w} a {v} b =
    ap (λ b' → emb f ((v , (w , a)) , b')) (sym (absorb-l b))
    ∙ interchange f (idn y) a b

  unit-is-prop
    : ∀ {x} (e : hom x x)
    → (∀ {w} → is-equiv (λ (a : hom w x) → emb e ((x , (w , a)) , e)))
    → yon e e ≡ e
    → e ≡ idn x
  unit-is-prop {x} e re idpt = sym (yon-eval e) ∙ yon-e-absorb (idn x)
    where
      e-idem : e ⨾ e ≡ e
      e-idem = comp-eq e e ∙ idpt

      yon-e-idpt : ∀ {w} (g : hom w x) → yon e (yon e g) ≡ yon e g
      yon-e-idpt g =
        sym (sym (ap (λ t → yon t g) e-idem) ∙ yon-composite e e g)

      yon-e-squared
        : ∀ {w} (g : hom w x) → emb e ((x , (w , g)) , e) ≡ yon e (yon e g)
      yon-e-squared {w} g =
        emb-yon e g e
        ∙ sym (ap (λ b' → emb (idn x) ((x , (w , yon e g)) , b')) (yon-eval e))
        ∙ interchange (idn x) e (yon e g) (idn x)
        ∙ ap (λ t → yon e t) (absorb-r (yon e g))

      yon-e-absorb : ∀ {w} (g : hom w x) → yon e g ≡ g
      yon-e-absorb g = equiv→lc re
        (yon-e-squared (yon e g) ∙ yon-e-idpt (yon e g) ∙ sym (yon-e-squared g))
```
