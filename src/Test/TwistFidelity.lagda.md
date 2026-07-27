Audit: are `twist⁺`/`twist⁻` the balanced/tortile twist?

Two questions, both statable without a tensor. Is the framing invertible in
the sense a tortile twist is — the two composing to the unit? And is either
twist natural?

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.TwistFidelity where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)

open import Cat.Logic.Type
open import Cat.Logic.Base
```

## Terms and coterms exchange definitionally

The coterm family of a virtual graph is the term family of its opposite. So
no condition may be imposed on one family alone.

```agda
coterm-is-op-term : ∀ {o h} (G : virtual-graph o h) (y : virtual-graph.ob G)
                  → virtual-graph.coterm G y ≡ virtual-graph.term (opⱽ G) y
coterm-is-op-term _ _ = refl

term-is-op-coterm : ∀ {o h} (G : virtual-graph o h) (x : virtual-graph.ob G)
                  → virtual-graph.term G x ≡ virtual-graph.coterm (opⱽ G) x
term-is-op-coterm _ _ = refl
```

## The tortile obligations

```agda
module _ {o h} {G : virtual-graph o h}
  (S : is-stable G) (C⁺ : is-composable⁺ G) (C⁻ : is-composable⁻ G)
  (pin⁻ : ∀ x → virtual-graph.coact-π G (virtual-graph.twist⁺ G x) ≡ cell⁻ G x)
  (pin⁺ : ∀ x → virtual-graph.act-π   G (virtual-graph.twist⁻ G x) ≡ cell⁺ G x)
  (K⁻ : ∀ x → cell⁻ G x ≡ snd) (K⁺ : ∀ x → cell⁺ G x ≡ snd)
  where
  open virtual-graph G
  open tower S C⁺ C⁻
  open unital pin⁻ pin⁺ K⁻ K⁺
```

A tortile twist is invertible: `θ⁻¹ ∘ θ` is the identity. Each hand has a
unit — the twist the *other* half carries — so the demand is that the
composite of the two twists be that unit. Read in either hand it forces the
two twists to be one edge.

```agda
  inverse⁻ : Type (o ⊔ h)
  inverse⁻ = ∀ x → twist⁻ x ⨾⁺ twist⁺ x ≡ twist⁺ x

  inverse⁺ : Type (o ⊔ h)
  inverse⁺ = ∀ x → twist⁻ x ⨾⁻ twist⁺ x ≡ twist⁻ x

  inverse⁻-collapses : inverse⁻ → ∀ x → twist⁻ x ≡ twist⁺ x
  inverse⁻-collapses H x = sym (pair⁺ x) ∙ H x

  inverse⁺-collapses : inverse⁺ → ∀ x → twist⁻ x ≡ twist⁺ x
  inverse⁺-collapses H x = sym (H x) ∙ pair⁻ x
```

A tortile twist is natural. In the hand where a twist is the unit, its
naturality *is* two-sided unitality — the tortile law carries no twist
content there, because the edge it speaks about occupies the unit's place.

```agda
  natural⁻ : Type (o ⊔ h)
  natural⁻ = ∀ {x y} (f : hom x y) → f ⨾⁺ twist⁺ y ≡ twist⁺ x ⨾⁺ f

  natural⁺ : Type (o ⊔ h)
  natural⁺ = ∀ {x y} (f : hom x y) → f ⨾⁻ twist⁻ y ≡ twist⁻ x ⨾⁻ f

  natural⁻-is-unitl : natural⁻ → ∀ {x y} (f : hom x y) → twist⁺ x ⨾⁺ f ≡ f
  natural⁻-is-unitl N f = sym (N f) ∙ unitr⁺ f

  natural⁺-is-unitr : natural⁺ → ∀ {x y} (f : hom x y) → f ⨾⁻ twist⁻ y ≡ f
  natural⁺-is-unitr N f = N f ∙ unitl⁻ f
```

## Interchange at the twists alone

The two hands are asked to agree on the composite of the framing — the whole
of the tier, with no other pair quantified over. The crossed pairings make
each side one of the two twists, so the tier *is* their identification.

```agda
  twist-interchange : Type (o ⊔ h)
  twist-interchange = ∀ x → twist⁻ x ⨾⁺ twist⁺ x ≡ twist⁻ x ⨾⁻ twist⁺ x

  twist-interchange-collapses : twist-interchange → ∀ x → twist⁻ x ≡ twist⁺ x
  twist-interchange-collapses H x = sym (pair⁺ x) ∙ H x ∙ pair⁻ x
```
