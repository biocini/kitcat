Lane Biocini
July 2026

Invertibility overlay for the faithful stratum: `codep-invariance`
upgrades the function-valued res-inv coercions of `codep-structure`
to equivalences, as an optional part of the module API — never a
field of `codep-structure` itself (Lane's ruling 2026-07-13; the
prep memo `notes/research/2026-07-13-faithful-stratum-spike-prep.md`
§2 note 5). A consumer opting in gains the backward coercions and
the section/retraction laws as derived members. At the tautological
filling both fields are discharged by `id-equiv` and the backward
coercions collapse to the identity definitionally — the killchecks
pin that collapse.

The is-equiv fields are prop-valued but carry the computational
content the derived members extract (the inverse is the center of
each fiber), so they take no `@0` — erasure would kill the backward
coercions under erased-cubical.

Scratch file — not in All. Imports the faithful-stratum spike
(Test importing Test is sanctioned in the scratch tier).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.CodepFaithfulInvariance-20260713-163756 where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Equiv.Base using (is-equiv; id-equiv; _≃_; module Equiv)

open import Cat.Type using (hcategory)

open import Test.CodepFaithful-20260713-140913
```

## The overlay record

Parameterized like the spike's Layer C. The two fields assert that
the fixed-endpoint coercions are equivalences; everything below
`field` is what opting in buys — the bundled equivalences, the
backward coercions via the fiber centers, and the roundtrip laws.

```agda
record codep-invariance {o h fℓ rℓ} {ob : Type o}
  {FS : fam-structure {o} {h} {fℓ} ob}
  (CS : codep-structure {o} {h} {fℓ} {rℓ} FS)
  : Type (o ⊔ h ⊔ fℓ ⊔ rℓ) where
  no-eta-equality
  open fam-structure FS
  open codep-structure CS
  field
    res-inv-r-equiv
      : ∀ {x y z} (g : hom y z) (c : cofam x) (φ : fam z)
      → is-equiv (res-inv-r g c φ)
    res-inv-l-equiv
      : ∀ {x y v} (f : hom x y) (c : cofam x) (φ : fam v)
      → is-equiv (res-inv-l f c φ)

  res-inv-r≃
    : ∀ {x y z} (g : hom y z) (c : cofam x) (φ : fam z)
    → res (c , g ◃ φ) ≃ res (c , φ)
  res-inv-r≃ g c φ = res-inv-r g c φ , res-inv-r-equiv g c φ

  res-inv-l≃
    : ∀ {x y v} (f : hom x y) (c : cofam x) (φ : fam v)
    → res (c ▹ f , φ) ≃ res (c , φ)
  res-inv-l≃ f c φ = res-inv-l f c φ , res-inv-l-equiv f c φ

  res-inv-r⁻¹
    : ∀ {x y z} (g : hom y z) (c : cofam x) (φ : fam z)
    → res (c , φ) → res (c , g ◃ φ)
  res-inv-r⁻¹ g c φ = Equiv.inv (res-inv-r≃ g c φ)

  res-inv-l⁻¹
    : ∀ {x y v} (f : hom x y) (c : cofam x) (φ : fam v)
    → res (c , φ) → res (c ▹ f , φ)
  res-inv-l⁻¹ f c φ = Equiv.inv (res-inv-l≃ f c φ)

  res-inv-r-sec
    : ∀ {x y z} (g : hom y z) (c : cofam x) (φ : fam z)
      (s : res (c , g ◃ φ))
    → res-inv-r⁻¹ g c φ (res-inv-r g c φ s) ≡ s
  res-inv-r-sec g c φ = Equiv.unit (res-inv-r≃ g c φ)

  res-inv-r-retr
    : ∀ {x y z} (g : hom y z) (c : cofam x) (φ : fam z)
      (t : res (c , φ))
    → res-inv-r g c φ (res-inv-r⁻¹ g c φ t) ≡ t
  res-inv-r-retr g c φ = Equiv.counit (res-inv-r≃ g c φ)

  res-inv-l-sec
    : ∀ {x y v} (f : hom x y) (c : cofam x) (φ : fam v)
      (s : res (c ▹ f , φ))
    → res-inv-l⁻¹ f c φ (res-inv-l f c φ s) ≡ s
  res-inv-l-sec f c φ = Equiv.unit (res-inv-l≃ f c φ)

  res-inv-l-retr
    : ∀ {x y v} (f : hom x y) (c : cofam x) (φ : fam v)
      (t : res (c , φ))
    → res-inv-l f c φ (res-inv-l⁻¹ f c φ t) ≡ t
  res-inv-l-retr f c φ = Equiv.counit (res-inv-l≃ f c φ)
```

## The filling instance

Over `module taut`'s `CS` both fields are `id-equiv`: the spike's
★-fields are `λ s → s` and the context types are convertible
(the spike's killcheck-res-inv-r/l pin that), so `idfun`'s
equivalence proof lands verbatim. The killchecks pin the reduction
the overlay's API value rests on at the filling: the derived
backward coercions collapse to the identity — the chain is
copattern projection (INV) → `id-equiv` → copattern projection
(`eqv-fibers … .center`) → builtin-Σ `.fst`.

```agda
module taut-inv {o h} (C : hcategory o h) where
  open taut C

  INV : codep-invariance CS
  INV .codep-invariance.res-inv-r-equiv g c φ = id-equiv
  INV .codep-invariance.res-inv-l-equiv f c φ = id-equiv

  module INV = codep-invariance INV

  killcheck-res-inv-r⁻¹
    : ∀ {x y z} (g : FS.hom y z) (c : FS.cofam x) (φ : FS.fam z)
    → INV.res-inv-r⁻¹ g c φ ≡ (λ s → s)
  killcheck-res-inv-r⁻¹ g c φ = refl

  killcheck-res-inv-l⁻¹
    : ∀ {x y v} (f : FS.hom x y) (c : FS.cofam x) (φ : FS.fam v)
    → INV.res-inv-l⁻¹ f c φ ≡ (λ s → s)
  killcheck-res-inv-l⁻¹ f c φ = refl
```

-- VERDICT: DERIVED. Route: the overlay record over the spike's
-- Layer C parameterization, backward coercions and roundtrip laws
-- projected through Core.Equiv.Base's `module Equiv` from the
-- bundled `res-inv-*≃` pairs; the filling instance discharged both
-- fields by `id-equiv` with no wrapping. The crux held by refl:
-- both killchecks (the derived backward coercions reduce to
-- `λ s → s` at the tautological filling) accepted `refl`. No walls.
