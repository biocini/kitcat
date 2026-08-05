Thunkability at the circle model is data. Both hands compute to the
multiplication, so `associates base g h` is the loop space at
`mult g h`: the constant family and its pointwise `rot`-shift are
both witnesses, and evaluation at the axiom separates them by one
winding. The length-4 coherence square does not cut the freedom —
the constant witness satisfies it through the degenerate associator,
the shift preserves it by naturality of `rot`, and the refined
closure is again not a proposition. The freedom is a loop-space
action, and the square is blind to a uniform shift.

This module uses `--cubical`: it consumes `loop-nontrivial` and
`Circle-is-groupoid` in unerased positions, which ride the winding
equivalence `ua` builds.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.VirtualGraphs.Circle.Thunkable where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Empty using (⊥)
open import Core.Kan using (_∙_; module Path)
open import Core.Path.Base using (ap-comp)
open import Core.Transport.J using (J)
open import Core.Transport.Properties using (is-prop→is-set)

open import HData.Circle
open Circle

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Circle.Model
```

## Two witnesses

```agda
open tower circle.model (λ _ → base) (λ _ → base)
  circle.stable circle.C⁺ circle.C⁻

T₀ : thunkable base
T₀ g h = refl

shift : (f : Circle) → thunkable f → thunkable f
shift f T g h = T g h ∙ rot (mult f (mult g h))

T₁ : thunkable base
T₁ = shift base T₀

thunkable-not-prop : is-prop (thunkable base) → ⊥
thunkable-not-prop W =
  loop-nontrivial
    (sym (Path.unitl loop) ∙ sym (λ i → W T₀ T₁ i base base))

associates-not-prop : is-prop (associates base base base) → ⊥
associates-not-prop W = loop-nontrivial (W loop refl)
```

## The square does not separate them

At the base edge the tower associator degenerates: the fiber over
the common judgment is a proposition, so the path the embedding
condition supplies agrees with the pair path whose first component is
constant, and the trace on edges is `refl`.

```agda
assoc⁺-base : (g k : Circle) → assoc⁺ base g k ≡ refl
assoc⁺-base g k =
  ap (ap fst)
    (is-prop→is-set (circle.stable (tri⁺.E base g k))
      (tri⁺.a₁ base g k) (tri⁺.a₂ base g k)
      (tri⁺.σ base g k)
      (λ i → mult g k , edge i))
  where
  edge : tri⁺.a₁ base g k .snd ≡ tri⁺.a₂ base g k .snd
  edge = Path.unitr (circle.C⁺ g k .snd) ∙ sym (Path.unitl (circle.C⁺ g k .snd))

T₀-coherent : coherent base T₀
T₀-coherent g h k =
    Path.unitl (assoc⁺ base (g ⨾⁻ h) k ∙ mixed-assoc g h k)
  ∙ (ap (_∙ mixed-assoc g h k) (assoc⁺-base (mult g h) k)
  ∙ (Path.unitl (mixed-assoc g h k)
  ∙ sym (Path.unitr (mixed-assoc g h k))))
```

The shift preserves the square: `rot-mult` moves the shift across
the trailing whisker, and `rot` is natural, so the shift commutes
with the canonical edges and lands on the shift of the other
instance.

```agda
rot-natural : {x y : Circle} (p : x ≡ y) → rot x ∙ p ≡ p ∙ rot y
rot-natural {x} p =
  J (λ y q → rot x ∙ q ≡ q ∙ rot y)
    (Path.unitr (rot x) ∙ sym (Path.unitl (rot x))) p

shift-coherent : (f : Circle) (T : thunkable f)
               → coherent f T → coherent f (shift f T)
shift-coherent f T cT g h k =
    ap (_∙ canon)
       ( ap-comp (_⨾⁺ k) (T g h) (rot X)
       ∙ ap (ap (_⨾⁺ k) (T g h) ∙_) (rot-mult X k))
  ∙ (sym (Path.assoc (ap (_⨾⁺ k) (T g h)) (rot (mult X k)) canon)
  ∙ (ap (ap (_⨾⁺ k) (T g h) ∙_) (rot-natural canon)
  ∙ (Path.assoc (ap (_⨾⁺ k) (T g h)) canon (rot Y)
  ∙ (ap (_∙ rot Y) (cT g h k)
  ∙ sym (Path.assoc (mixed-assoc (f ⨾⁺ g) h k)
          (T g (h ⨾⁺ k)) (rot Y))))))
  where
  X = mult f (mult g h)
  Y = mult f (mult g (mult h k))
  canon = assoc⁺ f (g ⨾⁻ h) k ∙ ap (f ⨾⁺_) (mixed-assoc g h k)

T₁-coherent : coherent base T₁
T₁-coherent = shift-coherent base T₀ T₀-coherent

coherent-not-prop : is-prop (Sigma (thunkable base) (coherent base)) → ⊥
coherent-not-prop W =
  loop-nontrivial
    (sym (Path.unitl loop)
     ∙ sym (λ i → W (T₀ , T₀-coherent) (T₁ , T₁-coherent) i .fst base base))
```
