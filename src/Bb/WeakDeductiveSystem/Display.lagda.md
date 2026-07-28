The two argument families as lenses, and each cut as a fibration. A
family transports along base edges and returns its own vertex at the
base's reflexive edge, which is one cancellation — so each family is a
lens over the graph of the twist it does not carry, with that
cancellation as its unitor.
Composability then reads as a lifting condition, with the composition
the lift's target and the head-rewriting witness the lift.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.WeakDeductiveSystem.Display where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Path.Base
open import Core.Transport.Properties using (prop-inhabited→is-contr)

open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base
open import Cat.Graph.Refl.Properties
open import Cat.Graph.Refl.Lens
open import Cat.Graph.Refl.Fibration

open import Bb.WeakDeductiveSystem.Type
open import Bb.WeakDeductiveSystem.Base
open import Bb.WeakDeductiveSystem.Graph
```

## The two families

```agda
module framed {o h} (G : virtual-graph o h)
  (pin⁻ : ∀ x → virtual-graph.coact-π G (virtual-graph.twist⁺ G x) ≡ cell⁻ G x)
  (pin⁺ : ∀ x → virtual-graph.act-π   G (virtual-graph.twist⁻ G x) ≡ cell⁺ G x)
  (K⁻ : ∀ x → cell⁻ G x ≡ snd) (K⁺ : ∀ x → cell⁺ G x ≡ snd)
  where
  open virtual-graph G
  open sequents G
  open two-sided G
  open absorption G pin⁻ pin⁺ K⁻ K⁺
```

The term action pushes forward and its cancellation points back at the
vertex, which is an oplax covariant lens; the coterm action pulls back
and its cancellation points forward, which is a lax contravariant one.

```agda
  term-lens : oplax-cov-lens (graph⁻ G) (term-fam G)
  term-lens .oplax-cov-lens.has-push _ _ p = act p
  term-lens .oplax-cov-lens.has-unitor t   = absorb⁺ t

  coterm-lens : lax-ctrv-lens (graph⁺ G) (coterm-fam G)
  coterm-lens .lax-ctrv-lens.has-pull _ _ p = coact p
  coterm-lens .lax-ctrv-lens.has-unitor k   = sym (absorb⁻ k)
```

Both families are discrete, hence path objects, so both displays are
univalent with no condition on the base — which a deductive system does
not in general satisfy.

```agda
  term-disp-univalent : is-displayed-univalent (oplax-cov-lens.display term-lens)
  term-disp-univalent = cov-disp-path-object term-lens (λ x → disc-path-object (term x))

  coterm-disp-univalent : is-displayed-univalent (lax-ctrv-lens.display coterm-lens)
  coterm-disp-univalent = ctrv-disp-path-object coterm-lens (λ y → disc-path-object (coterm y))
```

## The coslice, and the cut as a lift

The edges out of a fixed object, displayed over the positive graph, with
a displayed edge over `p` recording that its target represents the
positive composite. Displayed reflexivity is the cancellation and
nothing more.

```agda
  coslice : ob → rx.disp (graph⁺ G) h (o ⊔ h)
  coslice a .reflexive-graphᴰ.vtx z          = hom a z
  coslice a .reflexive-graphᴰ.edge _ _ p u w = reflect w ≡ composite⁺ G u p
  coslice a .reflexive-graphᴰ.rx u i γ       = reflect u (γ .fst , sym (absorb⁻ (γ .snd)) i)
```

A displayed edge out of `u` over `p` is a representation of the
composite, so the lifting condition is that representation's
contractibility: existence is the cut's, uniqueness is stability's, and
the two together are exactly a covariant fibration.

```agda
  module cuts (S : is-stable G) (C⁺ : is-composable⁺ G) (C⁻ : is-composable⁻ G) where
    open tower S C⁺ C⁻

    coslice-fibration : ∀ a → rx.is-cov-fibration (graph⁺ G) (coslice a)
    coslice-fibration _ _ _ p u = prop-inhabited→is-contr (S _) (C⁺ u p)

    module F (a : ob) = rx.cov-fibration (graph⁺ G) (coslice a) (coslice-fibration a)

    push-is-cut : ∀ a y z (p : hom y z) (u : hom a y) → F.push a y z p u ≡ u ⨾⁺ p
    push-is-cut _ _ _ _ _ = refl

    lift-is-witness : ∀ a y z (p : hom y z) (u : hom a y)
                    → F.lift a y z p u ≡ reflect-⨾⁺ u p
    lift-is-witness _ _ _ _ _ = refl
```

Being a fibration, the coslice is univalent as a display, with the base
unconstrained.

```agda
    coslice-univalent : ∀ a → is-displayed-univalent (coslice a)
    coslice-univalent a = cov-fibration-path-object (coslice a) (coslice-fibration a)
```

## The two-sided display

Over the base carrying both variances the judgment family transports in
one move, and its unitor is the two cancellations together.

```agda
  bipush-axiom : ∀ {x y} (α : judgment x y) → bipush (twist⁻ x) (twist⁺ y) α ≡ α
  bipush-axiom α = funext λ γ i → α (absorb⁺ (γ .fst) i , absorb⁻ (γ .snd) i)

  judgment-lens : oplax-cov-lens base judgment-fam
  judgment-lens .oplax-cov-lens.has-push _ _ p = bipush (p .fst) (p .snd)
  judgment-lens .oplax-cov-lens.has-unitor     = bipush-axiom

  judgment-disp-univalent
    : is-displayed-univalent (oplax-cov-lens.display judgment-lens)
  judgment-disp-univalent = cov-disp-path-object judgment-lens (λ _ → disc-path-object _)
```

Each composite judgment is the two-sided transport with one leg held at
its twist, applied to one factor's reflection. The two land in the fiber
at the outer pair from *different* vertices, so their configuration is a
cospan and their agreement is neither a unitor nor an edge of the
display.

```agda
  push-is-composite⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
                     → bipush (twist⁻ x) g (reflect f) ≡ composite⁺ G f g
  push-is-composite⁺ f g i γ = reflect f (absorb⁺ (γ .fst) i , coact g (γ .snd))

  push-is-composite⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
                     → bipush f (twist⁺ z) (reflect g) ≡ composite⁻ G f g
  push-is-composite⁻ f g i γ = reflect g (act f (γ .fst) , absorb⁻ (γ .snd) i)

  cospan-from-cuts
    : (∀ {x y z} (f : hom x y) (g : hom y z) → composite⁺ G f g ≡ composite⁻ G f g)
    → ∀ {x y z} (f : hom x y) (g : hom y z)
    → bipush (twist⁻ x) g (reflect f) ≡ bipush f (twist⁺ z) (reflect g)
  cospan-from-cuts X f g =
    push-is-composite⁺ f g ∙ X f g ∙ sym (push-is-composite⁻ f g)

  cuts-from-cospan
    : (∀ {x y z} (f : hom x y) (g : hom y z)
       → bipush (twist⁻ x) g (reflect f) ≡ bipush f (twist⁺ z) (reflect g))
    → ∀ {x y z} (f : hom x y) (g : hom y z) → composite⁺ G f g ≡ composite⁻ G f g
  cuts-from-cospan C f g =
    sym (push-is-composite⁺ f g) ∙ C f g ∙ push-is-composite⁻ f g
```

## What the lens is not

The two-sided transport composes, but the base edge it lands on takes
one hand's composition on the backward coordinate and the other's on the
forward one. No single composition makes the lens functorial.

```agda
  module _ (S : is-stable G) (C⁺ : is-composable⁺ G) (C⁻ : is-composable⁻ G) where
    open tower S C⁺ C⁻

    bipush-comp
      : ∀ {x y x' y' x'' y''}
        (a : hom x' x) (a' : hom x'' x') (b : hom y y') (b' : hom y' y'')
        (α : judgment x y)
      → bipush a' b' (bipush a b α) ≡ bipush (a' ⨾⁻ a) (b ⨾⁺ b') α
    bipush-comp a a' b b' α i γ =
      α (act-⨾⁻ a' a (γ .fst) (~ i) , coact-⨾⁺ b b' (γ .snd) (~ i))
```
