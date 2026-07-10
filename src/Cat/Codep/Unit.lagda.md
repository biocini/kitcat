Lane Biocini
July 2026

The unit layer over `codep-category` + `codep-coupling`. `codep-unit`
adds the two axioms that make the anchor a genuine unit: the identity's
acted and passenger actions are equivalences. From these the full unit
fragment derives — absorption (`absorb-l`, `absorb-r`), the codependent
identity law `·-idn` (`F · idn ≡ F`), the unit laws `unitl`/`unitr`
(fiber-projected), `emb-image-contr`, and identity uniqueness
`unit-is-prop` via the Kraus chain.

Together with `Cat.Codep.Coupling` this closes the pre-side four-axiom
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
open import Core.Function.Embedding
  using (equiv→lc; image-fibers-contr→is-embedding)

open import Cat.Codep.Base
open import Cat.Codep.Coupling
```

## The unit record

The identity's acted action `pre (idn x)` and passenger action
`post (idn x)` are equivalences.

```agda
record codep-unit {o h} {ob : Type o}
  (R : codep-category {o} {h} ob) (Coup : codep-coupling R)
  : Type (o ⊔ h) where
  no-eta-equality
  open codep-category R
  open Helpers R
  field
    unit-l-equiv : ∀ {x} {v} → is-equiv (pre (idn x) {v})
    unit-r-equiv : ∀ {x} {w} → is-equiv (post (idn x) {w})
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

  absorb-l : ∀ {x v} (b : hom x v) → pre (idn x) b ≡ b
  absorb-l {x} b = equiv→lc unit-l-equiv pre-idn-idpt
    where
      pre-idn-idpt : pre (idn x) (pre (idn x) b) ≡ pre (idn x) b
      pre-idn-idpt =
        sym (subst (λ t → pre t b ≡ pre (idn x) (pre (idn x) b))
          idem (pre-comp (idn x) (idn x) b))

  absorb-r : ∀ {w x} (a : hom w x) → post (idn x) a ≡ a
  absorb-r {w} {x} a = equiv→lc unit-r-equiv post-idn-idpt
    where
      post-idn-idpt : post (idn x) (post (idn x) a) ≡ post (idn x) a
      post-idn-idpt =
        sym (subst (λ t → post t a ≡ post (idn x) (post (idn x) a))
          idem (post-comp (idn x) (idn x) a))

  ·-idn : ∀ {x y} (F : composite x y) → F · idn y ≡ F
  ·-idn F = composite-ext λ γ →
    ap (λ β → F (γ .fst , β)) (absorb-l (γ .snd))
```

## Unit laws and the image fiber

The identity absorbs on the left of `emb`; `emb-image-contr` transports
`compose-contr (idn) f` along that absorption; `unitl`/`unitr` project
from the contractible image fiber.

```agda
  emb-idn-absorb : ∀ {x y} (f : hom x y) → emb (idn x) · f ≡ emb f
  emb-idn-absorb f = composite-ext λ γ →
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

`emb-post` rewrites `emb f` through `emb idn` at the post-shifted
binder. `unit-is-prop`: any `e` whose passenger square is an
equivalence and whose binary post-idempotency `post e e ≡ e` holds is
the identity, by the Kraus chain (`post e` squares to itself, is
idempotent, so absorbs).

```agda
  emb-post
    : ∀ {x y} (f : hom x y) {w} (a : hom w x) {v} (b : hom y v)
    → emb f ((v , (w , a)) , b) ≡ emb (idn y) ((v , (w , post f a)) , b)
  emb-post {x} {y} f {w} a {v} b =
    ap (λ b' → emb f ((v , (w , a)) , b')) (sym (absorb-l b))
    ∙ interchange f (idn y) a b

  unit-is-prop
    : ∀ {x} (e : hom x x)
    → (∀ {w} → is-equiv (λ (a : hom w x) → emb e ((x , (w , a)) , e)))
    → post e e ≡ e
    → e ≡ idn x
  unit-is-prop {x} e re idpt = sym (post-eval e) ∙ post-e-absorb (idn x)
    where
      e-idem : e ⨾ e ≡ e
      e-idem = comp-eq e e ∙ idpt

      post-e-idpt : ∀ {w} (g : hom w x) → post e (post e g) ≡ post e g
      post-e-idpt g =
        sym (sym (ap (λ t → post t g) e-idem) ∙ post-comp e e g)

      post-e-squared
        : ∀ {w} (g : hom w x) → emb e ((x , (w , g)) , e) ≡ post e (post e g)
      post-e-squared {w} g =
        emb-post e g e
        ∙ sym (ap (λ b' → emb (idn x) ((x , (w , post e g)) , b')) (post-eval e))
        ∙ interchange (idn x) e (post e g) (idn x)
        ∙ ap (λ t → post e t) (absorb-r (post e g))

      post-e-absorb : ∀ {w} (g : hom w x) → post e g ≡ g
      post-e-absorb g = equiv→lc re
        (post-e-squared (post e g) ∙ post-e-idpt (post e g) ∙ sym (post-e-squared g))
```

## Names are tight

`emb` is an embedding — `is-representable F` is a proposition (from
`emb-image-contr`). This upgrades the unconditional total-space
equivalence `Cat.Codep.Base.hom≃representable` to a subtype inclusion:
`hom` embeds into the composites exactly as the representable ones.

```agda
  is-representable-prop
    : ∀ {x y} (F : composite x y) → is-prop (is-representable F)
  is-representable-prop = image-fibers-contr→is-embedding emb-image-contr
```
