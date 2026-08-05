Readback over the circle model — reifying the reflection of an edge at
the axiom returns the edge — holds in two provably distinct ways: the
unit witness and its `rot`-shift differ by one winding. The readback
family is therefore not a proposition, and no family over it with
points over both witnesses has a contractible total space: any
candidate filler separates its two witnesses by one winding.

This module uses `--cubical`: it consumes `loop-nontrivial` in an
unerased position, which rides the winding equivalence `ua` builds.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.VirtualGraphs.Circle.Torsor where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Data.Empty using (⊥)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Circle.Model

open import HData.Circle
open Circle

open virtual-graph circle.model using (reflect)
open framing circle.model (λ _ → base) (λ _ → base) using (eval; readback-of)
```

Readback holds: reifying the reflection of an edge at the axiom
returns the edge, by one right unit law.

```agda
rb₀ : readback-of
rb₀ f = mult-unit-r f

rb₁ : readback-of
rb₁ f = rb₀ f ∙ rot f
```

The two readbacks separate at the axiom by one winding, so the
readback family is not a proposition.

```agda
readback-not-prop : is-prop readback-of → ⊥
readback-not-prop W =
  loop-nontrivial
    (sym (Path.unitl loop) ∙ sym (λ i → W rb₀ rb₁ i base))
```

No family over the readbacks with points over both witnesses has a
contractible total space. A filler candidate dies by exhibiting its
two witnesses.

```agda
torsor : ∀ {ℓ} (F : readback-of → Type ℓ)
       → F rb₀ → F rb₁
       → is-contr (Sigma readback-of F)
       → ⊥
torsor F x y c =
  loop-nontrivial
    (sym (Path.unitl loop)
     ∙ sym (λ i → is-contr→is-prop c (rb₀ , x) (rb₁ , y) i .fst base))
```
