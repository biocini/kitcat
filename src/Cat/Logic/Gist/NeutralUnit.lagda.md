Spike: a neutral unit for both cuts

The two cuts have one unit law each, on opposite sides, and the edge
each names is the other's twist. This spike asks what it takes for a
single edge — the composite of the two twists — to be a two-sided unit
for both.

The answer is one hypothesis, and it is the one the fragment is defined
by dropping: that the two cuts agree. Under it the two compositions
coincide, all four unit laws hold, the two twists are *derived* to be
equal, and their composite is the shared neutral unit.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.NeutralUnit where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)

open import Cat.Logic.Type
open import Cat.Logic.Base
```

## The hypothesis

Cutting through a pending read and cutting through a pending write
deliver the same judgment. Nothing below this decides it: the two
composite judgments carry opposite windings at the junction, and
equating them is a coherence rather than a consequence.

```agda
module _ {o h} {G : virtual-graph o h} where
  open virtual-graph G

  is-interchanging : Type (o ⊔ h)
  is-interchanging = ∀ {x y z} (f : hom x y) (g : hom y z)
                   → composite⁺ G f g ≡ composite⁻ G f g
```

## What it buys

```agda
module _ {o h} {G : virtual-graph o h}
  (S : is-stable G) (C⁺ : is-composable⁺ G) (C⁻ : is-composable⁻ G)
  (pin⁻ : ∀ x → virtual-graph.coact-π G (virtual-graph.twist⁺ G x) ≡ cell⁻ G x)
  (pin⁺ : ∀ x → virtual-graph.act-π   G (virtual-graph.twist⁻ G x) ≡ cell⁺ G x)
  (K⁻ : ∀ x → cell⁻ G x ≡ snd) (K⁺ : ∀ x → cell⁺ G x ≡ snd)
  (X : is-interchanging {G = G})
  where
  open virtual-graph G
  open sequents G
  open tower S C⁺ C⁻
  open unital pin⁻ pin⁺ K⁻ K⁺
```

Representation being unique, agreeing judgments have equal
representatives: the two compositions are one.

```agda
  ⨾-agree : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁺ g ≡ f ⨾⁻ g
  ⨾-agree f g = lc (reflect-⨾⁺ f g ∙ X f g ∙ sym (reflect-⨾⁻ f g))
```

Each hand's own unit law transports to the other hand, so each
composition acquires the law it was missing.

```agda
  unitl⁺ : ∀ {x y} (g : hom x y) → twist⁻ x ⨾⁺ g ≡ g
  unitl⁺ g = ⨾-agree (twist⁻ _) g ∙ unitl⁻ g

  unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ twist⁺ y ≡ f
  unitr⁻ f = sym (⨾-agree f (twist⁺ _)) ∙ unitr⁺ f
```

A left unit and a right unit for one composition meet at their own
composite, so the two twists are not independent after all.

```agda
  twists-agree : ∀ x → twist⁻ x ≡ twist⁺ x
  twists-agree x = sym (unitr⁺ (twist⁻ x)) ∙ unitl⁺ (twist⁺ x)
```

## The neutral unit

The composite of the two twists — either juxtaposition, since the two
compositions are one — is that common edge, and it is a two-sided unit
for both cuts.

```agda
  ι : (x : ob) → hom x x
  ι x = twist⁻ x ⨾⁺ twist⁺ x

  ι-twist⁻ : ∀ x → ι x ≡ twist⁻ x
  ι-twist⁻ = pair⁺

  ι-twist⁺ : ∀ x → ι x ≡ twist⁺ x
  ι-twist⁺ x = pair⁺ x ∙ twists-agree x

  ι-either : ∀ x → twist⁻ x ⨾⁻ twist⁺ x ≡ ι x
  ι-either x = sym (⨾-agree (twist⁻ x) (twist⁺ x))

  ι-unitl⁺ : ∀ {x y} (g : hom x y) → ι x ⨾⁺ g ≡ g
  ι-unitl⁺ {x} g = ap (_⨾⁺ g) (ι-twist⁻ x) ∙ unitl⁺ g

  ι-unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ ι y ≡ f
  ι-unitr⁺ {y = y} f = ap (f ⨾⁺_) (ι-twist⁺ y) ∙ unitr⁺ f

  ι-unitl⁻ : ∀ {x y} (g : hom x y) → ι x ⨾⁻ g ≡ g
  ι-unitl⁻ {x} g = sym (⨾-agree (ι x) g) ∙ ι-unitl⁺ g

  ι-unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ ι y ≡ f
  ι-unitr⁻ {y = y} f = sym (⨾-agree f (ι y)) ∙ ι-unitr⁺ f
```

## What the spike settles

`ι` is the composite of the two twists, taken in either composition by
`ι-either`, and it satisfies the ordinary two-sided unit laws for both —
`ι-unitl⁺`, `ι-unitr⁺`, `ι-unitl⁻`, `ι-unitr⁻`. Nothing here is a new
axiom about units: the four laws are the two the framing already gives,
transported across `⨾-agree`.

The cost is exactly one hypothesis, and it is `is-interchanging`. That
is not an accident of the derivation. The two composite judgments carry
opposite windings at their junction, so a single edge can be neutral for
both only if the junctions are identified — and identifying them is the
coherence the deductive-system fragment is defined by forgetting.

`twists-agree` is the sharp consequence and it is derived, not assumed:
once the two cuts agree, the positive and negative twists are the same
edge. So a framing with two genuinely distinct twists and a shared
neutral unit is not a shape that exists. Either the twists differ and
each cut keeps its own one-sided unit, or they are identified and the
two cuts collapse to one with a two-sided unit — the framed theory and
its degeneration, and no third option between them.
