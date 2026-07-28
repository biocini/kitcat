Spike: the propositional form of balance is buried.

Readback over the circle model — reifying the reflection of an
edge at the axiom returns the edge — holds in provably distinct
ways: the unit witness and its `rot`-shift differ by one winding.
So the readback family is not a proposition, and no family over
it with points over both witnesses has a contractible total
space. A filler candidate dies by exhibiting its two witnesses.

This module uses `--cubical` because it consumes
`loop-nontrivial` in an unerased position, which rides the
winding equivalence that `ua` builds.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Test.SpikeReadbackTorsor where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Data.Empty using (⊥)

open import Cat.Logic.Type
open import Cat.Logic.Gist.ThunkableSquare

open import HData.Circle
open Circle
open circle

open virtual-graph model using (reflect)
open sequents model using (eval)
```

Readback holds: reifying the reflection of an edge at the axiom
returns the edge, by one right unit law.

```agda
rb₀ : (f : Circle) → eval (reflect f) ≡ f
rb₀ f = mult-unit-r f

rb₁ : (f : Circle) → eval (reflect f) ≡ f
rb₁ f = rb₀ f ∙ rot f
```

The two readbacks separate at the axiom by one winding, so the
readback family is not a proposition.

```agda
readback-not-prop : is-prop ((f : Circle) → eval (reflect f) ≡ f) → ⊥
readback-not-prop W =
  loop-nontrivial
    (sym (Path.unitl loop) ∙ sym (λ i → W rb₀ rb₁ i base))
```

No family over the readbacks with points over both witnesses has
a contractible total space. A filler candidate dies by exhibiting
its two witnesses.

```agda
torsor : ∀ {ℓ} (F : ((f : Circle) → eval (reflect f) ≡ f) → Type ℓ)
       → F rb₀ → F rb₁
       → is-contr (Sigma ((f : Circle) → eval (reflect f) ≡ f) F)
       → ⊥
torsor F x y c =
  loop-nontrivial
    (sym (Path.unitl loop)
     ∙ sym (λ i → is-contr→is-prop c (rb₀ , x) (rb₁ , y) i .fst base))
```
