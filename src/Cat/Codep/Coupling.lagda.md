Lane Biocini
July 2026

The coupling layer over `codep-category`: the profunctorial link
between the two representable actions. `noy` acts on the acted slot,
`yon` on the passenger binder; both are `emb` at a re-anchored
identity context. `codep-coupling` records the two axioms relating
them — `interchange` (the two actions commute) and `yon-eval` (the
passenger action at the identity is the identity).

`CouplingDerived` derives `yon-composite`, `comp-eq`, and the identity
idempotency `idem : idn ⨾ idn ≡ idn` from the coupling ALONE. This
module has no access to `absorb-l` (which lives downstream in
`Cat.Codep.Unit`), so `idem`'s absorption-freeness is enforced by the
module boundary, not merely observed — the linchpin of the unit
fragment (idempotency precedes absorption; the two are not circular).

`noy-composite` is free: it is the base `act-comp` at the identity
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

`noy g b` acts `g` on the acted slot at the identity binder; `yon f a`
acts `f` on the passenger binder at the identity acted slot.

```agda
module Helpers {o h} {ob : Type o} (R : codep-category {o} {h} ob) where
  open codep-category R

  noy : ∀ {y z} (g : hom y z) {v} → hom z v → hom y v
  noy {y} g {v} b = emb g ((v , (y , idn y)) , b)

  yon : ∀ {x y} (f : hom x y) {w} → hom w x → hom w y
  yon {x} {y} f {w} a = emb f ((y , (w , a)) , idn y)
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
      → emb f ((v , (w , a)) , noy g b)
      ≡ emb g ((v , (w , yon f a)) , b)
    yon-eval
      : ∀ {x y} (f : hom x y) → yon f (idn x) ≡ f
```

## Composition of actions, and identity idempotency

`yon-composite` combines `emb-comp` with `interchange`; `comp-eq`
reads a composite as a `yon`-action; `idem` follows with `yon-eval`.

```agda
module CouplingDerived {o h} {ob : Type o}
  (R : codep-category {o} {h} ob) (Coup : codep-coupling R) where
  open codep-category R
  open Helpers R
  open codep-coupling Coup

  yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z) {w} (a : hom w x)
    → yon (f ⨾ g) a ≡ yon g (yon f a)
  yon-composite f g {w} a =
    happly (emb-comp f g) ((_ , (w , a)) , idn _)
    ∙ interchange f g a (idn _)

  comp-eq : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾ g ≡ yon g f
  comp-eq f g =
    sym (yon-eval (f ⨾ g))
    ∙ yon-composite f g (idn _)
    ∙ ap (λ t → yon g t) (yon-eval f)

  yon-idpt : ∀ {x} → yon (idn x) (idn x) ≡ idn x
  yon-idpt = yon-eval (idn _)

  idem : ∀ {x} → idn x ⨾ idn x ≡ idn x
  idem = comp-eq (idn _) (idn _) ∙ yon-idpt

  -- noy-composite is act-comp at the identity binder.
  noy-composite
    : ∀ {y z w} (g : hom y z) (h : hom z w) {v} (b : hom w v)
    → noy (g ⨾ h) b ≡ noy g (noy h b)
  noy-composite {y} g h b = act-comp (_ , idn-b y) g h b
```
