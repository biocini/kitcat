Spike: readback as a structure field of the carrier. A virtual
graph carries it beside the framing, and this measures what the
base gains from it.

The opposite is a strict involution on the nose, the readback leg
crossing unchanged. With one cut per hand, readback buys that
hand's unit law at its twist, and each composition is its own
action read at the axiom. The four absorption hypotheses do not
follow: readback constrains reflection at the axiom environment
of the reflected edge only, and modulo the conversions each
hypothesis is exactly a missing unit law or a crossed pairing.
The stability demotion reduces to one price: the negative
composite at the twist is a reflection through `unitl⁻`, so
stability follows once the cut's fiber arrives contractible —
the one datum an existence-only cut does not supply.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.BalancedBase where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Function.Embedding using (image-fibers-contr→is-embedding)

open import Cat.Logic.Type
open import Cat.Logic.Base

record bgraph o h : Type₊ (o ⊔ h) where
  field
    graph    : virtual-graph o h
    readback : ∀ {x y} (f : virtual-graph.hom graph x y)
             → sequents.eval graph (virtual-graph.reflect graph f)
             ≡ f
```

The opposite swaps the argument halves and the twists; evaluation
at the axiom is unmoved, so the readback leg crosses unchanged and
the involution stays on the nose.

```agda
opᴮ : ∀ {o h} → bgraph o h → bgraph o h
opᴮ B .bgraph.graph    = opⱽ (bgraph.graph B)
opᴮ B .bgraph.readback = bgraph.readback B

opᴮ-invol : ∀ {o h} (B : bgraph o h) → opᴮ (opᴮ B) ≡ B
opᴮ-invol B = refl
```

```agda
module rehearsal {o h} (B : bgraph o h) where
  open bgraph B
  open virtual-graph graph hiding (readback)
  open sequents graph

  -- pin⁻, pin⁺, K⁻, K⁺ from readback alone: BLOCKED. Each is a
  -- family over every coterm or term with a twist reflected at a
  -- non-axiom environment; readback constrains reflect at the
  -- axiom environment of the reflected edge only, so no instance
  -- of it has the right head.

  module cuts (C⁺ : is-composable⁺ graph) (C⁻ : is-composable⁻ graph) where

    _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾⁺ g = C⁺ f g .fst

    _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾⁻ g = C⁻ f g .fst
```

Each composition is its own action read at the axiom: the cut's
representation witness evaluates there, and readback straightens
both flanks.

```agda
    ⨾⁻-is-act : ∀ {w x y} (s : hom w x) (h : hom x y)
              → act-π h (w , s) ≡ s ⨾⁻ h
    ⨾⁻-is-act {w} {x} {y} s h =
        (λ i → reflect h ((w , readback s (~ i)) , covar y))
      ∙ (λ i → C⁻ s h .snd (~ i) (var w , covar y))
      ∙ readback (s ⨾⁻ h)

    ⨾⁺-is-coact : ∀ {x y z} (f : hom x y) (k : hom y z)
                → coact-π f (z , k) ≡ f ⨾⁺ k
    ⨾⁺-is-coact {x} {y} {z} f k =
        (λ i → reflect f (var x , (z , readback k (~ i))))
      ∙ (λ i → C⁺ f k .snd (~ i) (var x , covar z))
      ∙ readback (f ⨾⁺ k)
```

With a cut aboard the four absorption hypotheses stay unproved,
and the conversions name each residue exactly: the K's are the
missing unit law per hand at its own twist, and the pins are the
two crossed pairings.

```agda
    -- K⁻, K⁺, pin⁻, pin⁺ with the cuts: BLOCKED, residues below.

    K⁻-from-unitr⁻ : (∀ {x v} (k : hom x v) → k ⨾⁻ twist⁻ v ≡ k)
                   → ∀ x → cell⁻ graph x ≡ snd
    K⁻-from-unitr⁻ u x i γ =
      (⨾⁻-is-act (γ .snd) (twist⁻ (γ .fst)) ∙ u (γ .snd)) i

    K⁺-from-unitl⁺ : (∀ {w x} (s : hom w x) → twist⁺ w ⨾⁺ s ≡ s)
                   → ∀ x → cell⁺ graph x ≡ snd
    K⁺-from-unitl⁺ u x i t =
      (⨾⁺-is-coact (twist⁺ (t .fst)) (t .snd) ∙ u (t .snd)) i

    pin⁻-from-crossing : (∀ {x v} (k : hom x v)
                          → twist⁺ x ⨾⁺ k ≡ k ⨾⁻ twist⁻ v)
                       → ∀ x → coact-π (twist⁺ x) ≡ cell⁻ graph x
    pin⁻-from-crossing u x i γ =
      ( ⨾⁺-is-coact (twist⁺ x) (γ .snd)
      ∙ u (γ .snd)
      ∙ sym (⨾⁻-is-act (γ .snd) (twist⁻ (γ .fst))) ) i

    pin⁺-from-crossing : (∀ {w x} (s : hom w x)
                          → s ⨾⁻ twist⁻ x ≡ twist⁺ w ⨾⁺ s)
                       → ∀ x → act-π (twist⁻ x) ≡ cell⁺ graph x
    pin⁺-from-crossing u x i t =
      ( ⨾⁻-is-act (t .snd) (twist⁻ x)
      ∙ u (t .snd)
      ∙ sym (⨾⁺-is-coact (twist⁺ (t .fst)) (t .snd)) ) i
```

The two unit laws the unital module gains land here without the
absorption hypotheses and without stability: readback at the
composite, the cut's witness at the axiom, readback at the twist,
readback at the edge. The composite is the tower's — `tower`
binds the same first projection — so these are the tower's
`unitr⁺` and `unitl⁻` verbatim.

```agda
    unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ twist⁺ y ≡ f
    unitr⁺ {x} {y} f =
        sym (readback (f ⨾⁺ twist⁺ y))
      ∙ (λ i → C⁺ f (twist⁺ y) .snd i (var x , covar y))
      ∙ (λ i → reflect f (var x , (y , readback (twist⁺ y) i)))
      ∙ readback f

    unitl⁻ : ∀ {x y} (g : hom x y) → twist⁻ x ⨾⁻ g ≡ g
    unitl⁻ {x} {y} g =
        sym (readback (twist⁻ x ⨾⁻ g))
      ∙ (λ i → C⁻ (twist⁻ x) g .snd i (var x , covar y))
      ∙ (λ i → reflect g ((x , readback (twist⁻ x) i) , covar y))
      ∙ readback g

```

The negative composite at the twist is a reflection: the cut's
witness against `unitl⁻`, no absorption spent. So a contractible
cut fiber transports to every image fiber, and
`image-fibers-contr→is-embedding` closes stability. This
fragment's `is-composable⁻` carries a point of representability
only, so the demotion's exact price is that contractibility.

```agda
    composite⁻-twist : ∀ {x y} (g : hom x y)
                     → composite⁻ graph (twist⁻ x) g ≡ reflect g
    composite⁻-twist {x} g =
      sym (C⁻ (twist⁻ x) g .snd) ∙ ap reflect (unitl⁻ g)

    stable-from-contr-cut⁻
      : (∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable (composite⁻ graph f g)))
      → is-stable graph
    stable-from-contr-cut⁻ cc {x} {y} =
      image-fibers-contr→is-embedding
        (λ g → subst (λ β → is-contr (is-representable β))
                     (composite⁻-twist g) (cc (twist⁻ x) g))
```
