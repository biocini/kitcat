Lane Biocini
July 2026

Morphism-level algebra over a `Bb.CatsWithExplicitInterchange.Type`
category: whiskering, sections and retractions, monomorphisms and
epimorphisms, and neutrality — composition maps being equivalences.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Morphism where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv; aut)
open import Core.Function.Embedding using (equiv→lc)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Base

module morphism {o h} (C : category o h) where
  open category C
  open theory C
```

## Whiskering

Whiskering operators apply a morphism to one side of a path. Right
whiskering `p ▹ h'` precomposes the path's endpoints with `h'`; left
whiskering `f ◃ p` postcomposes `f`.

```agda
  _▹_
    : ∀ {x y z} {f g : hom x y}
    → f ≡ g → (h' : hom y z)
    → f ⨾ h' ≡ g ⨾ h'
  p ▹ h' = ap (_⨾ h') p
  infixr 25 _▹_

  _◃_
    : ∀ {x y z} (f : hom x y)
    → {g h' : hom y z} → g ≡ h'
    → f ⨾ g ≡ f ⨾ h'
  f ◃ p = ap (f ⨾_) p
  infixl 26 _◃_
```

## Sections and retractions

A morphism `f` has a section when there exists a right inverse `g`
with `f ⨾ g ≡ idn`. It has a retraction when there exists a left
inverse `g` with `g ⨾ f ≡ idn`.

```agda
  has-section : ∀ {x y} → hom x y → Type h
  has-section {y} f = Σ g ∶ hom y _ , f ⨾ g ≡ idn _

  has-retraction : ∀ {x y} → hom x y → Type h
  has-retraction {x} f = Σ g ∶ hom _ x , g ⨾ f ≡ idn _
```

## Mono and epi

A monomorphism is left-cancellable; an epimorphism is
right-cancellable.

```agda
  is-mono : ∀ {x y} → hom x y → Type (o ⊔ h)
  is-mono {x} f = ∀ {w} {g h' : hom w x} → g ⨾ f ≡ h' ⨾ f → g ≡ h'

  is-epi : ∀ {x y} → hom x y → Type (o ⊔ h)
  is-epi {y} f = ∀ {z} {g h' : hom y z} → f ⨾ g ≡ f ⨾ h' → g ≡ h'
```

A section (right inverse) gives a monomorphism; a retraction (left
inverse) gives an epimorphism. The proofs sandwich the hypothesis
between unit laws and associativity.

```agda
  section→mono
    : ∀ {x y} {f : hom x y}
    → has-section f → is-mono f
  section→mono {f = f} (g , s) {g = a} {h' = b} p =
    a             ≡˘⟨ unitr a ⟩
    a ⨾ idn _     ≡˘⟨ a ◃ s ⟩
    a ⨾ (f ⨾ g)   ≡⟨ assoc a f g ⟩
    (a ⨾ f) ⨾ g   ≡⟨ p ▹ g ⟩
    (b ⨾ f) ⨾ g   ≡⟨ sym (assoc b f g) ⟩
    b ⨾ (f ⨾ g)   ≡⟨ b ◃ s ⟩
    b ⨾ idn _     ≡⟨ unitr b ⟩
    b ∎

  retraction→epi
    : ∀ {x y} {f : hom x y}
    → has-retraction f → is-epi f
  retraction→epi {f = f} (g , r) {g = a} {h' = b} p =
    a             ≡˘⟨ unitl a ⟩
    idn _ ⨾ a     ≡˘⟨ r ▹ a ⟩
    (g ⨾ f) ⨾ a   ≡⟨ sym (assoc g f a) ⟩
    g ⨾ (f ⨾ a)   ≡⟨ g ◃ p ⟩
    g ⨾ (f ⨾ b)   ≡⟨ assoc g f b ⟩
    (g ⨾ f) ⨾ b   ≡⟨ r ▹ b ⟩
    idn _ ⨾ b     ≡⟨ unitl b ⟩
    b ∎
```

Monomorphisms compose: if both `f` and `g` are mono, then `f ⨾ g` is
mono. The proof reassociates to apply `g`'s cancellation, then `f`'s.

```agda
  mono-comp
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-mono f → is-mono g → is-mono (f ⨾ g)
  mono-comp {f = f} {g} mf mg p = mf (mg (sym (assoc _ f g) ∙ p ∙ assoc _ f g))

  epi-comp
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-epi f → is-epi g → is-epi (f ⨾ g)
  epi-comp {f = f} {g} ef eg p = eg (ef (assoc f g _ ∙ p ∙ sym (assoc f g _)))
```

If `f ⨾ g` is mono then `f` is mono; if `f ⨾ g` is epi then `g` is
epi. The proofs apply the composite cancellation after wrapping with
the opposite morphism.

```agda
  mono-cancel
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-mono (f ⨾ g) → is-mono f
  mono-cancel {f = f} {g} mfg p = mfg (assoc _ f g ∙ p ▹ g ∙ sym (assoc _ f g))

  epi-cancel
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-epi (f ⨾ g) → is-epi g
  epi-cancel {f = f} {g} efg p = efg (sym (assoc f g _) ∙ f ◃ p ∙ assoc f g _)
```

## Neutrality

A morphism is neutral when both composition maps are equivalences.
Left-neutrality: `(f ⨾_)` is an equivalence. Right-neutrality:
`(_⨾ f)` is an equivalence. An idempotent neutral morphism equals the
identity (cancel `_⨾ e` against `idn ⨾ e`).

```agda
  is-neutral : ∀ {x y} → hom x y → Type (o ⊔ h)
  is-neutral {x} {y} f =
    (∀ {z} → is-equiv (λ (h' : hom y z) → f ⨾ h'))
    × (∀ {w} → is-equiv (λ (g : hom w x) → g ⨾ f))

  idn-is-neutral : ∀ {x} → is-neutral (idn x)
  idn-is-neutral .fst = subst is-equiv (sym (funext unitl)) (aut .snd)
  idn-is-neutral .snd = subst is-equiv (sym (funext unitr)) (aut .snd)

  idempotent-neutral→idn
    : ∀ {x} {e : hom x x}
    → is-neutral e → e ⨾ e ≡ e → e ≡ idn _
  idempotent-neutral→idn {e = e} (_ , re) ee≡e =
    equiv→lc re
      (ee≡e ∙ sym (unitl e))
```
