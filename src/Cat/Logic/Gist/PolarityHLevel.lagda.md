Spike: the h-level of polarity, computed at the circle model and
at the balanced word model.

`positive` and `negative` transcribe a polarity definition over the
tower. The source is Clairambault and Munch-Maccagnoni, *Duploid
situations in concurrent games* (GaLoP XII, 2017), the Polarity
definition at `resources/mmmm-classical-notions/article.tex:1694-1700`.
An object is positive when every edge out of it is linear. It is
negative when every edge into it is thunkable. The transcription
truncates nothing. At the circle model both polarities hold at the
one object, in provably distinct ways. So polarity is structure at
full deductive-system strength. At the word model both polarities
are propositions, and both are empty.

This module uses `--cubical`. It consumes the circle model of
`Cat.Logic.Gist.ThunkableSquare` and the multiplication coherences
of `HData.Circle` in unerased positions. Both live in `--cubical`
modules, and an `--erased-cubical` module can use them only
erased.

```agda
{-# OPTIONS --cubical --safe --no-guardedness #-}

module Cat.Logic.Gist.PolarityHLevel where

open import Core.Type
open import Core.Base
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Data.Empty using (¬_)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop)

open import Cat.Logic.Type
open import Cat.Logic.Base

open import Cat.Logic.Gist.ThunkableSquare using (module circle)
open import Cat.Logic.Gist.BalancedWord
  using (BW; BW-stable; BW-comp⁺; BW-comp⁻; ε̂; τ̂; W-set;
         thunkable-refuted; linear-refuted)

open import HData.Circle
open Circle
```

## Polarity over the tower

An object is positive when every edge out of it is linear. It is
negative when every edge into it is thunkable. The object
quantifier is explicit, as in the cited definition. Neither
type is a proposition here, so the names carry no `is-` prefix,
matching `thunkable` and `linear`.

```agda
module polarity {o h} (G : virtual-graph o h)
  (S : is-stable G) (C⁺ : is-composable⁺ G) (C⁻ : is-composable⁻ G) where
  open virtual-graph G
  open tower G S C⁺ C⁻ public

  positive : ob → Type (o ⊔ h)
  positive x = (y : ob) (f : hom x y) → linear f

  negative : ob → Type (o ⊔ h)
  negative x = (y : ob) (f : hom y x) → thunkable f
```

A polarity witness fills the failing mixed word. A positivity
witness on the source of the trailing edge fills `associates` at
the whole triple. A negativity witness on the target of the
leading edge does the same. Each filler reads its witness at one
slot, so distinct witnesses can read to distinct fillers.

```agda
  positive-assoc : ∀ {w x y z} (P : positive y)
                   (f : hom w x) (g : hom x y) (h : hom y z)
                 → associates f g h
  positive-assoc {z = z} P f g h = P z h f g

  negative-assoc : ∀ {w x y z} (N : negative x)
                   (f : hom w x) (g : hom x y) (h : hom y z)
                 → associates f g h
  negative-assoc {w = w} N f g h = N w f g h
```

Over hom sets every `associates` cell lives in a set. Both
polarities are then propositions, by the argument that truncates
`thunkable` there.

```agda
  positive-is-prop : (∀ {x y} → is-set (hom x y))
                   → ∀ x → is-prop (positive x)
  positive-is-prop hs x =
    Π-is-prop λ _ → Π-is-prop λ _ →
    Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → hs _ _

  negative-is-prop : (∀ {x y} → is-set (hom x y))
                   → ∀ x → is-prop (negative x)
  negative-is-prop hs x =
    Π-is-prop λ _ → Π-is-prop λ _ →
    Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → hs _ _
```

## The circle model

Both cuts compute to the multiplication, so `associates f g h` is
`mult (mult f g) h ≡ mult f (mult g h)` on the nose. `mult-assoc`
inhabits it at every triple. So every edge is thunkable and
linear, not only `base`. The one object is positive and negative
at once.

```agda
module circle-model where
  open circle using (model; stable; C⁺; C⁻)
  open polarity model stable C⁺ C⁻

  thunkable-all : (f : Circle) → thunkable f
  thunkable-all f g h = mult-assoc f g h

  linear-all : (f : Circle) → linear f
  linear-all f g k = mult-assoc g k f

  positive-all : positive tt
  positive-all y f = linear-all f

  negative-all : negative tt
  negative-all y f = thunkable-all f
```

The witness freedom of `ThunkableSquare` persists one quantifier
up. The pointwise `rot`-shift of a polarity witness is again a
witness. Evaluation at the axiom triple separates the two
witnesses by one winding. So neither polarity is a proposition,
and neither witness space is contractible.

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
```

The two positivity witnesses fill one `associates` cell in two
ways, and the fillers differ. A subcategory of positive objects
reads its mixed associator off the positivity witness. Over this
model that associator is a choice, not a law.

```agda
  filler-distinct
    : ¬ (positive-assoc P₀ base base base ≡ positive-assoc P₁ base base base)
  filler-distinct p = loop-nontrivial (sym (Path.unitl loop) ∙ sym p)
```

## The word model

Homs form a set, so both polarities are propositions there. Both
propositions are empty. A positivity witness at the point yields
linearity of the identity `ε̂`. A negativity witness yields
thunkability of the negative twist `τ̂`. The model refutes both.

```agda
module word-model where
  open polarity BW BW-stable BW-comp⁺ BW-comp⁻

  positive-prop : is-prop (positive tt)
  positive-prop = positive-is-prop (λ {x} {y} → W-set) tt

  negative-prop : is-prop (negative tt)
  negative-prop = negative-is-prop (λ {x} {y} → W-set) tt

  positive-empty : ¬ positive tt
  positive-empty P = linear-refuted (P tt ε̂)

  negative-empty : ¬ negative tt
  negative-empty N = thunkable-refuted (N tt τ̂)
```

## What the spike settles

At full deductive-system strength, polarity is structure. The
circle model inhabits both polarities and refutes their
propositionality and their contractibility. The definitions do
not self-improve to a property. The freedom is the loop-space
action of `thunkable-not-prop`, now uniform across all edges and
both polarities.

Over hom sets polarity is a property, as in the source theory. At
the free balanced point that property is empty: the word model
has no positive object and no negative object. That emptiness
measures the free point, not the theory. The circle model is a
full deductive system in which both polarities hold.

verified: `just check Cat.Logic.Gist.PolarityHLevel`, 2026-07-29, zero
warnings, no holes, no postulates.
