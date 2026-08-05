What readback buys. Each composition is its own action read at the
axiom, each hand gains the unit law at its own twist, and the
negative composite at the twist is a reflection — so a contractible
negative cut yields the embedding condition. The hand modules consume
one cut and readback each, with no embedding-condition hypothesis and
no second cut; the residue module names what readback does not reach.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Readback where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Function.Embedding using (image-fibers-contr→is-embedding)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
```

## The positive hand

```agda
module hand⁺ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (R : framing.readback-of G rx corx) where

  open framing G rx corx

  _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁺ g = C⁺ f g .fst

  ⨾⁺-is-coact : ∀ {x y z} (f : hom x y) (k : hom y z)
              → coact-π f (z , k) ≡ f ⨾⁺ k
  ⨾⁺-is-coact {x} {y} {z} f k =
      (λ i → reflect f (var x , (z , R k (~ i))))
    ∙ (λ i → C⁺ f k .snd (~ i) (var x , covar z))
    ∙ R (f ⨾⁺ k)

  unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ corx y ≡ f
  unitr⁺ {x} {y} f =
      sym (R (f ⨾⁺ corx y))
    ∙ (λ i → C⁺ f (corx y) .snd i (var x , covar y))
    ∙ (λ i → reflect f (var x , (y , R (corx y) i)))
    ∙ R f
```

## The negative hand

```agda
module hand⁻ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (R : framing.readback-of G rx corx) where

  open framing G rx corx

  _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁻ g = C⁻ f g .fst

  ⨾⁻-is-act : ∀ {w x y} (s : hom w x) (h : hom x y)
            → act-π h (w , s) ≡ s ⨾⁻ h
  ⨾⁻-is-act {w} {x} {y} s h =
      (λ i → reflect h ((w , R s (~ i)) , covar y))
    ∙ (λ i → C⁻ s h .snd (~ i) (var w , covar y))
    ∙ R (s ⨾⁻ h)

  unitl⁻ : ∀ {x y} (g : hom x y) → rx x ⨾⁻ g ≡ g
  unitl⁻ {x} {y} g =
      sym (R (rx x ⨾⁻ g))
    ∙ (λ i → C⁻ (rx x) g .snd i (var x , covar y))
    ∙ (λ i → reflect g ((x , R (rx x) i) , covar y))
    ∙ R g

  composite⁻-twist : ∀ {x y} (g : hom x y)
                   → composite⁻ (rx x) g ≡ reflect g
  composite⁻-twist {x} g =
    sym (C⁻ (rx x) g .snd) ∙ ap reflect (unitl⁻ g)
```

## The embedding condition from the contractible negative cut

The negative composite at the twist is a reflection, so a
contractible cut fiber transports to every image fiber.

```agda
module contr-cut⁻ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (R : framing.readback-of G rx corx)
  (cc : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (is-representable G (framing⁺.composite⁻ G corx f g))) where

  open hand⁻ G rx corx (λ f g → cc f g .center) R

  embedding-from-contr-cut⁻ : reflect-is-embedding G
  embedding-from-contr-cut⁻ {x} {y} =
    image-fibers-contr→is-embedding
      (λ g → subst (λ β → is-contr (is-representable G β))
                   (composite⁻-twist g) (cc (rx x) g))
```

## The residues

The four absorption hypotheses do not follow from readback: it
constrains reflection at the axiom environment of the reflected edge
only. Modulo the action identities each hypothesis is exactly a
missing far unit law or a crossed pairing.

```agda
module residues {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (R : framing.readback-of G rx corx) where

  open framing G rx corx
  open hand⁺ G rx corx C⁺ R
  open hand⁻ G rx corx C⁻ R

  K⁻-from-unitr⁻ : (∀ {x v} (k : hom x v) → k ⨾⁻ rx v ≡ k)
                 → ∀ x → cell⁻ x ≡ snd
  K⁻-from-unitr⁻ u x i γ =
    (⨾⁻-is-act (γ .snd) (rx (γ .fst)) ∙ u (γ .snd)) i

  K⁺-from-unitl⁺ : (∀ {w x} (s : hom w x) → corx w ⨾⁺ s ≡ s)
                 → ∀ x → cell⁺ x ≡ snd
  K⁺-from-unitl⁺ u x i t =
    (⨾⁺-is-coact (corx (t .fst)) (t .snd) ∙ u (t .snd)) i

  pin⁻-from-crossing : (∀ {x v} (k : hom x v)
                        → corx x ⨾⁺ k ≡ k ⨾⁻ rx v)
                     → ∀ x → coact-π (corx x) ≡ cell⁻ x
  pin⁻-from-crossing u x i γ =
    ( ⨾⁺-is-coact (corx x) (γ .snd)
    ∙ u (γ .snd)
    ∙ sym (⨾⁻-is-act (γ .snd) (rx (γ .fst))) ) i

  pin⁺-from-crossing : (∀ {w x} (s : hom w x)
                        → s ⨾⁻ rx x ≡ corx w ⨾⁺ s)
                     → ∀ x → act-π (rx x) ≡ cell⁺ x
  pin⁺-from-crossing u x i t =
    ( ⨾⁻-is-act (t .snd) (rx x)
    ∙ u (t .snd)
    ∙ sym (⨾⁺-is-coact (corx (t .fst)) (t .snd)) ) i
```

## Over the tower

The hand laws land on the tower's compositions — the cuts bind the
same first projection — and the crossed pairings follow. The §4-style
collapse laws are `collapse⁺ pair⁺` and `collapse⁻ pair⁻` at the
re-exported tower.

```agda
module readback-tower {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (R : framing.readback-of G rx corx) where

  open tower G rx corx S C⁺ C⁻ public

  ⨾⁺-is-coact = hand⁺.⨾⁺-is-coact G rx corx C⁺ R
  unitr⁺      = hand⁺.unitr⁺ G rx corx C⁺ R
  ⨾⁻-is-act   = hand⁻.⨾⁻-is-act G rx corx C⁻ R
  unitl⁻      = hand⁻.unitl⁻ G rx corx C⁻ R

  composite⁻-twist = hand⁻.composite⁻-twist G rx corx C⁻ R

  pair⁻ : ∀ x → rx x ⨾⁻ corx x ≡ corx x
  pair⁻ x = unitl⁻ (corx x)

  pair⁺ : ∀ x → rx x ⨾⁺ corx x ≡ rx x
  pair⁺ x = unitr⁺ (rx x)
```
