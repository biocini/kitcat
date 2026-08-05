Polarity at the circle model. Both cuts compute to the
multiplication, so `associates f g h` is
`mult (mult f g) h ≡ mult f (mult g h)` on the nose and
`mult-assoc` inhabits it at every triple: every edge is thunkable
and linear, and the one object is positive and negative at once.
The witness freedom persists one quantifier up — the pointwise
`rot`-shift of a polarity witness is again a witness, and
evaluation at the axiom triple separates the two by one winding —
so neither polarity is a proposition and neither witness space is
contractible. The two positivity witnesses fill one `associates`
cell in distinct ways: a subcategory of positive objects reads its
mixed associator off the witness, and over this model that
associator is a choice, not a law.

This module uses `--cubical`: it consumes `loop-nontrivial` in an
unerased position, which rides the winding equivalence `ua` builds.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.VirtualGraphs.Circle.Polarity where

open import Core.Type
open import Core.Base
open import Core.Data.Empty using (¬_)
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)

open import HData.Circle
open Circle

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Polarity
open import Bb.VirtualGraphs.Circle.Model
```

```agda
open polarity circle.model (λ _ → base) (λ _ → base)
  circle.stable circle.C⁺ circle.C⁻

thunkable-all : (f : Circle) → thunkable f
thunkable-all f g h = mult-assoc f g h

linear-all : (f : Circle) → linear f
linear-all f g k = mult-assoc g k f

positive-all : positive tt
positive-all y f = linear-all f

negative-all : negative tt
negative-all y f = thunkable-all f
```

```agda
shift⁺ : positive tt → positive tt
shift⁺ P y f g k = P y f g k ∙ rot (mult g (mult k f))

shift⁻ : negative tt → negative tt
shift⁻ N y f g h = N y f g h ∙ rot (mult f (mult g h))

P₀ P₁ : positive tt
P₀ = positive-all
P₁ = shift⁺ P₀

N₀ N₁ : negative tt
N₀ = negative-all
N₁ = shift⁻ N₀

positive-distinct : ¬ (P₀ ≡ P₁)
positive-distinct p =
  loop-nontrivial (sym (Path.unitl loop) ∙ sym (λ i → p i tt base base base))

negative-distinct : ¬ (N₀ ≡ N₁)
negative-distinct p =
  loop-nontrivial (sym (Path.unitl loop) ∙ sym (λ i → p i tt base base base))

positive-not-prop : ¬ is-prop (positive tt)
positive-not-prop W = positive-distinct (W P₀ P₁)

negative-not-prop : ¬ is-prop (negative tt)
negative-not-prop W = negative-distinct (W N₀ N₁)

positive-not-contr : ¬ is-contr (positive tt)
positive-not-contr c = positive-not-prop (is-contr→is-prop c)

negative-not-contr : ¬ is-contr (negative tt)
negative-not-contr c = negative-not-prop (is-contr→is-prop c)

filler-distinct
  : ¬ (positive-assoc P₀ base base base ≡ positive-assoc P₁ base base base)
filler-distinct p = loop-nontrivial (sym (Path.unitl loop) ∙ sym p)
```
