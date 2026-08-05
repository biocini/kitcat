Polarity over the tower. An object is positive when every edge out
of it is linear, negative when every edge into it is thunkable —
after Clairambault and Munch-Maccagnoni, *Duploid situations in
concurrent games* (GaLoP XII, 2017), the Polarity definition at
`resources/mmmm-classical-notions/article.tex:1694-1700`. The
transcription truncates nothing: neither type is a proposition in
general, so the names carry no `is-` prefix, matching `thunkable`
and `linear`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Polarity where

open import Core.Type
open import Core.Base
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
```

```agda
module polarity {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx) where

  open tower G rx corx S C⁺ C⁻ public

  positive : ob → Type (o ⊔ h)
  positive x = (y : ob) (f : hom x y) → linear f

  negative : ob → Type (o ⊔ h)
  negative x = (y : ob) (f : hom y x) → thunkable f
```

A polarity witness fills the failing mixed word: a positivity
witness on the source of the trailing edge fills `associates` at the
whole triple, and a negativity witness on the target of the leading
edge does the same. Each filler reads its witness at one slot, so
distinct witnesses can read to distinct fillers.

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

Over hom sets every `associates` cell lives in a set, so both
polarities are propositions.

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

## The forward direction

Both twists at `x` inhabit `hom x x`, so each polarity witness
evaluates at them: four instantiations, with no content beyond the
quantifier.

```agda
  positive→linear-corx : ∀ x → positive x → linear (corx x)
  positive→linear-corx x P = P x (corx x)

  positive→linear-rx : ∀ x → positive x → linear (rx x)
  positive→linear-rx x P = P x (rx x)

  negative→thunkable-corx : ∀ x → negative x → thunkable (corx x)
  negative→thunkable-corx x N = N x (corx x)

  negative→thunkable-rx : ∀ x → negative x → thunkable (rx x)
  negative→thunkable-rx x N = N x (rx x)
```

## Generation

`gen` says an edge is a cut word in the twists. Its indices force
every generated edge onto a loop: `gen-diag` reads the endpoint
identification off a derivation, so the generated-carrier hypothesis
is vacuous on any carrier with a non-loop edge. Over a generated
carrier, induction over `gen` returns each polarity from its
two-twist instances, `gen-diag` transporting the hypotheses to the
junctions a derivation visits.

```agda
  data gen : ∀ {x y} → hom x y → Type (o ⊔ h) where
    gen-corx : ∀ {x} → gen (corx x)
    gen-rx : ∀ {x} → gen (rx x)
    gen-⨾⁺ : ∀ {x y z} {f : hom x y} {g : hom y z}
           → gen f → gen g → gen (f ⨾⁺ g)
    gen-⨾⁻ : ∀ {x y z} {f : hom x y} {g : hom y z}
           → gen f → gen g → gen (f ⨾⁻ g)

  gen-diag : ∀ {x y} {f : hom x y} → gen f → x ≡ y
  gen-diag gen-corx   = refl
  gen-diag gen-rx   = refl
  gen-diag (gen-⨾⁺ d e) = gen-diag d ∙ gen-diag e
  gen-diag (gen-⨾⁻ d e) = gen-diag d ∙ gen-diag e

  gen-linear : ∀ {x y} {f : hom x y}
             → linear (corx x) → linear (rx x)
             → gen f → linear f
  gen-linear L⁺ L⁻ gen-corx = L⁺
  gen-linear L⁺ L⁻ gen-rx = L⁻
  gen-linear L⁺ L⁻ (gen-⨾⁺ {f = f} {g = g} d _) =
    linear-⨾⁺ f g (gen-linear L⁺ L⁻ d)
  gen-linear L⁺ L⁻ (gen-⨾⁻ {f = f} {g = g} d e) =
    linear-⨾⁻ f g (gen-linear L⁺ L⁻ d)
      (gen-linear
        (subst (λ z → linear (corx z)) (gen-diag d) L⁺)
        (subst (λ z → linear (rx z)) (gen-diag d) L⁻) e)

  gen-thunkable : ∀ {x y} {f : hom x y}
                → thunkable (corx y) → thunkable (rx y)
                → gen f → thunkable f
  gen-thunkable T⁺ T⁻ gen-corx = T⁺
  gen-thunkable T⁺ T⁻ gen-rx = T⁻
  gen-thunkable T⁺ T⁻ (gen-⨾⁺ {f = f} {g = g} d e) =
    thunkable-⨾⁺ f g
      (gen-thunkable
        (subst (λ z → thunkable (corx z)) (sym (gen-diag e)) T⁺)
        (subst (λ z → thunkable (rx z)) (sym (gen-diag e)) T⁻) d)
      (gen-thunkable T⁺ T⁻ e)
  gen-thunkable T⁺ T⁻ (gen-⨾⁻ {f = f} {g = g} _ e) =
    thunkable-⨾⁻ f g (gen-thunkable T⁺ T⁻ e)

  positive-generated
    : (∀ {a b} (f : hom a b) → gen f)
    → ∀ x → linear (corx x) → linear (rx x) → positive x
  positive-generated gA x L⁺ L⁻ y f = gen-linear L⁺ L⁻ (gA f)

  negative-generated
    : (∀ {a b} (f : hom a b) → gen f)
    → ∀ x → thunkable (corx x) → thunkable (rx x) → negative x
  negative-generated gA x T⁺ T⁻ y f = gen-thunkable T⁺ T⁻ (gA f)
```

## The unit-law converse

Each hand's far unit law, fixed at one object, is the exact
consumable. With the far left law at `x`, every edge out of `x` is
the positive twist cut before that edge, and `linear-⨾⁺` finishes
from the twist alone; dually with the far right law and
`thunkable-⨾⁻`. So one edge decides its object's polarity wherever
those laws hold, with no generation hypothesis. `Cancellation`
instantiates these at the tiers.

```agda
  positive-from-unit
    : ∀ x → (∀ {v} (s : hom x v) → corx x ⨾⁺ s ≡ s)
    → linear (corx x) → positive x
  positive-from-unit x ul L y f =
    subst (λ e → linear e) (ul f) (linear-⨾⁺ (corx x) f L)

  negative-from-unit
    : ∀ x → (∀ {w} (k : hom w x) → k ⨾⁻ rx x ≡ k)
    → thunkable (rx x) → negative x
  negative-from-unit x ur T y f =
    subst (λ e → thunkable e) (ur f) (thunkable-⨾⁻ f (rx x) T)
```
