Lane Biocini
July 2026

The coupling layer over `codep-category`: the profunctorial link
between the two representable actions. `pre` acts on the acted slot,
`post` on the passenger binder; both are `emb` at a re-anchored
identity context. `codep-coupling` records the two axioms relating
them — `interchange` (the two actions commute) and `post-eval` (the
passenger action at the identity is the identity).

`CouplingDerived` derives `post-comp`, `comp-eq`, and the identity
idempotency `idem : idn ⨾ idn ≡ idn` from the coupling ALONE. This
module has no access to `absorb-l` (which lives downstream in
`Cat.Codep.Unit`), so `idem`'s absorption-freeness is enforced by the
module boundary, not merely observed — the linchpin of the unit
fragment (idempotency precedes absorption; the two are not circular).

`pre-comp` is free: it is the base `act-comp` at the identity
binder, so it is not re-derived here.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Coupling where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)

open import Cat.Codep.Base
```

## The two representable actions

`pre g b` acts `g` on the acted slot at the identity binder; `post f a`
acts `f` on the passenger binder at the identity acted slot.

```agda
module Helpers {o h} {ob : Type o} (R : codep-category {o} {h} ob) where
  open codep-category R

  pre : ∀ {y z} (g : hom y z) {v} → hom z v → hom y v
  pre {y} g {v} b = emb g ((v , (y , idn y)) , b)

  post : ∀ {x y} (f : hom x y) {w} → hom w x → hom w y
  post {x} {y} f {w} a = emb f ((y , (w , a)) , idn y)
```

## The coupling record

```agda
record codep-coupling {o h} {ob : Type o}
  (R : codep-category {o} {h} ob) : Type (o ⊔ h) where
  no-eta-equality
  open codep-category R
  open Helpers R
  field
    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        {w} (a : hom w x) {v} (b : hom z v)
      → emb f ((v , (w , a)) , pre g b)
      ≡ emb g ((v , (w , post f a)) , b)
    post-eval
      : ∀ {x y} (f : hom x y) → post f (idn x) ≡ f
```

## Composition of actions, and identity idempotency

`post-comp` combines `emb-comp` with `interchange`; `comp-eq`
reads a composite as a `post`-action; `idem` follows with `post-eval`.

```agda
module CouplingDerived {o h} {ob : Type o}
  (R : codep-category {o} {h} ob) (Coup : codep-coupling R) where
  open codep-category R
  open Helpers R
  open codep-coupling Coup

  post-comp
    : ∀ {x y z} (f : hom x y) (g : hom y z) {w} (a : hom w x)
    → post (f ⨾ g) a ≡ post g (post f a)
  post-comp f g {w} a =
    happly (emb-comp f g) ((_ , (w , a)) , idn _)
    ∙ interchange f g a (idn _)

  comp-eq : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾ g ≡ post g f
  comp-eq f g =
    sym (post-eval (f ⨾ g))
    ∙ post-comp f g (idn _)
    ∙ ap (λ t → post g t) (post-eval f)

  post-idpt : ∀ {x} → post (idn x) (idn x) ≡ idn x
  post-idpt = post-eval (idn _)

  idem : ∀ {x} → idn x ⨾ idn x ≡ idn x
  idem = comp-eq (idn _) (idn _) ∙ post-idpt

  -- pre-comp is act-comp at the identity binder.
  pre-comp
    : ∀ {y z w} (g : hom y z) (h : hom z w) {v} (b : hom w v)
    → pre (g ⨾ h) b ≡ pre g (pre h b)
  pre-comp {y} g h b = act-comp (_ , unit y) g h b
```
