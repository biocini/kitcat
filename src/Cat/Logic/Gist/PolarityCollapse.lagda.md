Spike: the two twist conditions agree at every object of a deductive
system.

`Cat.Logic.Gist.PolarityTwist` reduced polarity to a two-edge check. A
linear positive twist makes its object positive. A thunkable negative
twist makes its object negative. This spike asks whether the two
conditions come apart. A split needs one object positive and not
negative, and a second one negative and not positive. They do not come
apart.

Each twist condition implies the other, at every object. So the two
polarities are logically equivalent. The argument reads the framing
off the two cuts. The positive cut is associative, and both of its
unit laws hold at the positive twist. So the edges form a unital
magmoid whose identity is that twist.

The mixed law and the left positive unit law rewrite each negative
cut: `f ⨾⁻ g` is `(f ⨾⁻ twist⁺) ⨾⁺ g`. So the negative cut adds
nothing to the unital magmoid and the operator `_⨾⁻ twist⁺`. Each
polarity statement is then a statement about that operator.

A linear positive twist at `x` makes the operator one positive cut
against a fixed edge. That reading holds on every edge into `x`. The
fixed edge is a right inverse of the negative twist. The operator then
passes through any positive cut whose junction sits at `x`. That is a
thunkable negative twist. The dual argument runs through `twist⁻ x
⨾⁺_` and reads the same way.

So a distinguishing model is inconsistent at each candidate object. A
positive-not-negative object `p` needs a linear positive twist and no
thunkable negative twist. `no-positive-split` closes that pair. A
negative-not-positive object `n` closes the dual way, by
`no-negative-split`.

The obstruction sits at the tier level, not at the carrier level.
The collapse consumes the mixed law, the four unit laws, and both
associativities. A full deductive system carries all of them, and so
carries the collapse.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.PolarityCollapse where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Data.Empty

open import Cat.Logic.Type
open import Cat.Logic.Base

open import Cat.Logic.Gist.BalancedWord
  using ( BW; BW-stable; BW-comp⁺; BW-comp⁻; BW-invertible
        ; ε̂; τ̂; linear-refuted; thunkable-refuted )

open import Cat.Logic.Gist.PolarityTwist using (module polarity)
```

## The two crossed pairings

Each hand cuts against the other hand's twist. Neither pairing is a
unit law. Either one at every edge identifies the two twists.

```agda
module collapse {o h} (G : virtual-graph o h)
  (S : is-stable G) (C⁺ : is-composable⁺ G) (C⁻ : is-composable⁻ G)
  (T⁻ : is-invertible⁻ G) (T⁺ : is-invertible⁺ G) where
  open virtual-graph G
  open polarity G S C⁺ C⁻
  open balanced T⁻ T⁺
  open full T⁻ T⁺

  cross⁻ : ∀ {x y} → hom x y → hom x y
  cross⁻ {y = y} f = f ⨾⁻ twist⁺ y

  cross⁺ : ∀ {x y} → hom x y → hom x y
  cross⁺ {x} g = twist⁻ x ⨾⁺ g
```

Each cut is the other cut after its own pairing. The mixed law moves
the pairing's twist across the junction. The hand's own unit law then
absorbs it.

```agda
  cut⁻-cross : ∀ {x y z} (f : hom x y) (g : hom y z)
             → cross⁻ f ⨾⁺ g ≡ f ⨾⁻ g
  cut⁻-cross {y = y} f g =
    mixed-assoc f (twist⁺ y) g ∙ ap (f ⨾⁻_) (unitl⁺ g)

  cut⁺-cross : ∀ {x y z} (f : hom x y) (g : hom y z)
             → f ⨾⁻ cross⁺ g ≡ f ⨾⁺ g
  cut⁺-cross {y = y} f g =
    sym (mixed-assoc f (twist⁻ y) g) ∙ ap (_⨾⁺ g) (unitr⁻ f)
```

Each pairing distributes over the cut it produces. The proof rewrites
both cuts into the other hand. That hand's associativity closes it.

```agda
  cross⁻-cut⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → cross⁻ (cross⁻ f ⨾⁺ g) ≡ cross⁻ f ⨾⁺ cross⁻ g
  cross⁻-cut⁺ {z = z} f g =
      ap cross⁻ (cut⁻-cross f g)
    ∙ assoc⁻ f g (twist⁺ z)
    ∙ sym (cut⁻-cross f (cross⁻ g))

  cross⁺-cut⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → cross⁺ (f ⨾⁻ cross⁺ g) ≡ cross⁺ f ⨾⁻ cross⁺ g
  cross⁺-cut⁻ {x} f g =
      ap cross⁺ (cut⁺-cross f g)
    ∙ sym (assoc⁺ (twist⁻ x) f g)
    ∙ sym (cut⁺-cross (cross⁺ f) g)
```

## A linear positive twist

The hypothesis reads at its own twist. The pairing at an edge into `x`
is a positive cut against a fixed edge. The fixed edge is the pairing
at the positive twist. So one edge fixes the pairing on the whole of
`hom w x`. The negative twist cuts onto that edge as a right inverse.

```agda
  module from-linear {x} (L : linear (twist⁺ x)) where
    centre : hom x x
    centre = cross⁻ (twist⁺ x)

    cross⁻-into : ∀ {w} (f : hom w x) → cross⁻ f ≡ f ⨾⁺ centre
    cross⁻-into f = ap cross⁻ (sym (unitr⁺ f)) ∙ L f (twist⁺ x)

    twist⁻-centre : twist⁻ x ⨾⁺ centre ≡ twist⁺ x
    twist⁻-centre = sym (cross⁻-into (twist⁻ x)) ∙ pair⁻ x
```

The right inverse makes the pairing retract the negative twist's
positive cut. So every edge into `x` is a pairing. The distribution
law then reads at any edge into `x`. The negative twist is one of
them.

```agda
    retract : ∀ {w} (u : hom w x) → cross⁻ (u ⨾⁺ twist⁻ x) ≡ u
    retract u =
        cross⁻-into (u ⨾⁺ twist⁻ x)
      ∙ assoc⁺ u (twist⁻ x) centre
      ∙ ap (u ⨾⁺_) twist⁻-centre
      ∙ unitr⁺ u

    cross⁻-left : ∀ {w y} (u : hom w x) (f : hom x y)
                → cross⁻ (u ⨾⁺ f) ≡ u ⨾⁺ cross⁻ f
    cross⁻-left u f =
        ap (λ e → cross⁻ (e ⨾⁺ f)) (sym (retract u))
      ∙ cross⁻-cut⁺ (u ⨾⁺ twist⁻ x) f
      ∙ ap (_⨾⁺ cross⁻ f) (retract u)

    thunkable-twist⁻ : thunkable (twist⁻ x)
    thunkable-twist⁻ g h =
        sym (cut⁻-cross (twist⁻ x ⨾⁺ g) h)
      ∙ ap (_⨾⁺ h) (cross⁻-left (twist⁻ x) g)
      ∙ assoc⁺ (twist⁻ x) (cross⁻ g) h
      ∙ ap (twist⁻ x ⨾⁺_) (cut⁻-cross g h)
```

## A thunkable negative twist

The dual reading takes the pairing at an edge out of `x`. It uses the
negative cut in place of the positive one.

```agda
  module from-thunkable {x} (T : thunkable (twist⁻ x)) where
    centre : hom x x
    centre = cross⁺ (twist⁻ x)

    cross⁺-out : ∀ {v} (k : hom x v) → cross⁺ k ≡ centre ⨾⁻ k
    cross⁺-out k = ap cross⁺ (sym (unitl⁻ k)) ∙ sym (T (twist⁻ x) k)

    centre-twist⁺ : centre ⨾⁻ twist⁺ x ≡ twist⁻ x
    centre-twist⁺ = sym (cross⁺-out (twist⁺ x)) ∙ pair⁺ x

    retract : ∀ {v} (u : hom x v) → cross⁺ (twist⁺ x ⨾⁻ u) ≡ u
    retract u =
        cross⁺-out (twist⁺ x ⨾⁻ u)
      ∙ sym (assoc⁻ centre (twist⁺ x) u)
      ∙ ap (_⨾⁻ u) centre-twist⁺
      ∙ unitl⁻ u

    cross⁺-right : ∀ {w v} (f : hom w x) (u : hom x v)
                 → cross⁺ (f ⨾⁻ u) ≡ cross⁺ f ⨾⁻ u
    cross⁺-right f u =
        ap (λ e → cross⁺ (f ⨾⁻ e)) (sym (retract u))
      ∙ cross⁺-cut⁻ f (twist⁺ x ⨾⁻ u)
      ∙ ap (cross⁺ f ⨾⁻_) (retract u)

    linear-twist⁺ : linear (twist⁺ x)
    linear-twist⁺ f g =
        ap (_⨾⁻ twist⁺ x) (sym (cut⁺-cross f g))
      ∙ assoc⁻ f (cross⁺ g) (twist⁺ x)
      ∙ ap (f ⨾⁻_) (sym (cross⁺-right g (twist⁺ x)))
      ∙ cut⁺-cross f (g ⨾⁻ twist⁺ x)
```

## The collapse

Each twist condition implies the other. So the one-edge theorem sends
each polarity to the other one.

```agda
  linear→thunkable : ∀ x → linear (twist⁺ x) → thunkable (twist⁻ x)
  linear→thunkable _ L = from-linear.thunkable-twist⁻ L

  thunkable→linear : ∀ x → thunkable (twist⁻ x) → linear (twist⁺ x)
  thunkable→linear _ T = from-thunkable.linear-twist⁺ T

  positive→negative : ∀ x → positive x → negative x
  positive→negative x P =
    negative-of-twist⁻ x (linear→thunkable x (P x (twist⁺ x)))

  negative→positive : ∀ x → negative x → positive x
  negative→positive x N =
    positive-of-twist⁺ x (thunkable→linear x (N x (twist⁻ x)))
```

A distinguishing model needs one object positive and not negative, or
one object negative and not positive. `no-positive-split` refutes the
first case, and `no-negative-split` refutes the second, dually.

```agda
  no-positive-split : ∀ {p} → linear (twist⁺ p) → ¬ thunkable (twist⁻ p) → ⊥
  no-positive-split L R = R (linear→thunkable _ L)

  no-negative-split : ∀ {n} → thunkable (twist⁻ n) → ¬ linear (twist⁺ n) → ⊥
  no-negative-split T R = R (thunkable→linear _ T)
```

## The word model, read through the collapse

The free balanced point refutes both twist conditions at its one
object. The collapse ties the two refutations together. Either one
gives the other.

```agda
module word-check where
  open polarity BW BW-stable BW-comp⁺ BW-comp⁻ using (thunkable; linear)
  open collapse BW BW-stable BW-comp⁺ BW-comp⁻
    (is-invertible.fiber⁻ BW-invertible) (is-invertible.fiber⁺ BW-invertible)
    using (linear→thunkable; thunkable→linear)

  τ̂-not-thunkable : ¬ thunkable τ̂
  τ̂-not-thunkable T = linear-refuted (thunkable→linear tt T)

  ε̂-not-linear : ¬ linear ε̂
  ε̂-not-linear L = thunkable-refuted (linear→thunkable tt L)
```

## The bundled deductive system

The two theorems above take the raw tiers `(G, S, C⁺, C⁻, T⁻, T⁺)`
directly, not the bundled record `is-deductive-system`. `is-deductive-system`
reaches those same tiers through its own accessors, so
`from-deductive-system` opens `polarity` and `collapse` at them and
restates both directions for any `D : is-deductive-system G`.

```agda
module from-deductive-system {o h} (G : virtual-graph o h)
  (D : is-deductive-system G) where
  open polarity G (axioms→stable G D)
    (λ f g → is-composable.contr⁺ (is-deductive-system.composable D) f g .center)
    (λ f g → is-composable.contr⁻ (is-deductive-system.composable D) f g .center)
  open collapse G (axioms→stable G D)
    (λ f g → is-composable.contr⁺ (is-deductive-system.composable D) f g .center)
    (λ f g → is-composable.contr⁻ (is-deductive-system.composable D) f g .center)
    (is-invertible.fiber⁻ (is-deductive-system.invertible D))
    (is-invertible.fiber⁺ (is-deductive-system.invertible D))

  ds-positive→negative : ∀ x → positive x → negative x
  ds-positive→negative = positive→negative

  ds-negative→positive : ∀ x → negative x → positive x
  ds-negative→positive = negative→positive
```

## What the spike settles

No deductive system has an object that is positive and not negative.
The two twist conditions at an object are equivalent. So the two
polarities are logically equivalent, and no carrier separates them.
The search for a distinguishing model closes with the tiers, not
with a carrier count. `from-deductive-system` restates both
directions at the bundled record `is-deductive-system`, not only at
the raw tiers.

The collapse consumes `mixed-assoc`, `assoc⁺`, `assoc⁻`, `unitr⁺`,
`unitl⁻`, `pair⁺`, `pair⁻`, `unitl⁺`, and `unitr⁻`. The first seven
hold over a stable and composable carrier. The balanced tier proves
the last two from the two invertibility fibers. So a stratum
where the polarities differ could drop the mixed law. It could
instead drop one hand's associativity, or leave the framing without
an inverse.

verified: `just check Cat.Logic.Gist.PolarityCollapse`, 2026-07-29, zero
warnings, no holes, no postulates.
