Spike: polarity as a twist condition, measured at three strengths.

Both twists at an object are edges at that object, so both fall
under both polarity quantifiers. Instantiation gives the forward
direction: a positive object has two linear twists, and a negative
object has two thunkable twists. This spike measures the converse,
whether the two-edge check returns the full quantifier.

Three strengths, three answers. Over the bare tower, `thunkable`
and `linear` close under both cuts. No closure consumes a unit
law, a hom set, or invertibility. Two closures are one-sided.
`linear` under the positive cut reads only its leading factor.
`thunkable` under the negative cut reads only its trailing factor.

When the twists generate the carrier under the two cuts, induction
over the generation proves the converse from both twists. At full
deductive-system strength the framing is invertible and the
balanced unit laws hold. There one edge suffices. A linear
positive twist makes its object positive. A thunkable negative
twist makes its object negative. Between the two strengths, on a
stable and composable carrier that is neither invertible nor
generated, the question stays open.

The twists generate the word model: `gen-sem` writes every
canonical descriptor as a cut word in the two twists. The
recursion tracks weak monotonicity alone. So the two-edge check
holds at the free balanced point, vacuously. Each hypothesis pair
fails on exactly one twist there. The negative twist is linear and
the identity is not (`linear-refuted`). The identity is thunkable
and the negative twist is not (`thunkable-refuted`).

`positive` and `negative` restate `Cat.Logic.Gist.PolarityHLevel`
verbatim. That module is `--cubical` for its circle-model
measurements. An `--erased-cubical` module can use its exports
only erased, so this module restates the two definitions.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.PolarityTwist where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat
open import Core.Data.List
open import Core.Data.Bool

open import Cat.Logic.Type
open import Cat.Logic.Base

open import Cat.Logic.Gist.BalancedWord
  using ( BW; BW-stable; BW-comp⁺; BW-comp⁻; W; ev; evW; incr?
        ; ε̂; τ̂; ev-comp; ev-inj; w-inc; ev-mono-le; ev-past
        ; linear-refuted; thunkable-refuted )
open import Cat.Logic.Gist.AssociatesDefect
  using (le-pos; ev-τ; ev-cutε; run→linear; rise→thunkable)

open Nat using (_+_; _≤_; _≤ᵇ_; ≤ᵇ-sound; ≤ᵇ-complete)
open List using (length)
open Bool using (So; so-and; so-fst; so-snd)
```

## Polarity over the tower

An object is positive when every edge out of it is linear. It is
negative when every edge into it is thunkable. The object
quantifier is explicit, as in the source definitions.

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

## The forward direction

Both twists at `x` inhabit `hom x x`, so each polarity witness
evaluates at them. Four instantiations, with no content beyond the
quantifier.

```agda
  positive→linear-twist⁺ : ∀ x → positive x → linear (twist⁺ x)
  positive→linear-twist⁺ x P = P x (twist⁺ x)

  positive→linear-twist⁻ : ∀ x → positive x → linear (twist⁻ x)
  positive→linear-twist⁻ x P = P x (twist⁻ x)

  negative→thunkable-twist⁺ : ∀ x → negative x → thunkable (twist⁺ x)
  negative→thunkable-twist⁺ x N = N x (twist⁺ x)

  negative→thunkable-twist⁻ : ∀ x → negative x → thunkable (twist⁻ x)
  negative→thunkable-twist⁻ x N = N x (twist⁻ x)
```

## Closure under the cuts

All four combinations hold over the bare tower. Each proof
consumes the three unconditional associativity theorems and the
given witnesses, nothing else. Two closures are one-sided:
`linear-⨾⁺` reads only its leading factor, and `thunkable-⨾⁻`
only its trailing factor. The other two read both.

```agda
  thunkable-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → thunkable f → thunkable g → thunkable (f ⨾⁺ g)
  thunkable-⨾⁺ f g tf tg k h =
    ap (_⨾⁻ h) (assoc⁺ f g k)
    ∙ tf (g ⨾⁺ k) h
    ∙ ap (f ⨾⁺_) (tg k h)
    ∙ sym (assoc⁺ f g (k ⨾⁻ h))

  thunkable-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → thunkable g → thunkable (f ⨾⁻ g)
  thunkable-⨾⁻ f g tg k h =
    ap (_⨾⁻ h) (mixed-assoc f g k)
    ∙ assoc⁻ f (g ⨾⁺ k) h
    ∙ ap (f ⨾⁻_) (tg k h)
    ∙ sym (mixed-assoc f g (k ⨾⁻ h))

  linear-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → linear f → linear (f ⨾⁺ g)
  linear-⨾⁺ f g lf k m =
    sym (mixed-assoc (k ⨾⁺ m) f g)
    ∙ ap (_⨾⁺ g) (lf k m)
    ∙ assoc⁺ k (m ⨾⁻ f) g
    ∙ ap (k ⨾⁺_) (mixed-assoc m f g)

  linear-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → linear f → linear g → linear (f ⨾⁻ g)
  linear-⨾⁻ f g lf lg k m =
    sym (assoc⁻ (k ⨾⁺ m) f g)
    ∙ ap (_⨾⁻ g) (lf k m)
    ∙ lg k (m ⨾⁻ f)
    ∙ ap (k ⨾⁺_) (assoc⁻ m f g)
```

## Generation

`gen` says an edge is a cut word in the twists. Its indices force
every generated edge onto a loop: `gen-diag` reads the endpoint
identification off a derivation. So the generated-carrier tier is
vacuous on any carrier with a non-loop edge, because `gen-diag`
forces every generated edge onto an endpoint-identity loop. The
converse over a generated carrier is induction over `gen`. The
hypotheses sit at one object, and `gen-diag` transports them to the
junctions a derivation visits.

```agda
  data gen : ∀ {x y} → hom x y → Type (o ⊔ h) where
    gen-twist⁺ : ∀ {x} → gen (twist⁺ x)
    gen-twist⁻ : ∀ {x} → gen (twist⁻ x)
    gen-⨾⁺ : ∀ {x y z} {f : hom x y} {g : hom y z}
           → gen f → gen g → gen (f ⨾⁺ g)
    gen-⨾⁻ : ∀ {x y z} {f : hom x y} {g : hom y z}
           → gen f → gen g → gen (f ⨾⁻ g)

  gen-diag : ∀ {x y} {f : hom x y} → gen f → x ≡ y
  gen-diag gen-twist⁺   = refl
  gen-diag gen-twist⁻   = refl
  gen-diag (gen-⨾⁺ d e) = gen-diag d ∙ gen-diag e
  gen-diag (gen-⨾⁻ d e) = gen-diag d ∙ gen-diag e

  gen-linear : ∀ {x y} {f : hom x y}
             → linear (twist⁺ x) → linear (twist⁻ x)
             → gen f → linear f
  gen-linear L⁺ L⁻ gen-twist⁺ = L⁺
  gen-linear L⁺ L⁻ gen-twist⁻ = L⁻
  gen-linear L⁺ L⁻ (gen-⨾⁺ {f = f} {g = g} d _) =
    linear-⨾⁺ f g (gen-linear L⁺ L⁻ d)
  gen-linear L⁺ L⁻ (gen-⨾⁻ {f = f} {g = g} d e) =
    linear-⨾⁻ f g (gen-linear L⁺ L⁻ d)
      (gen-linear
        (subst (λ z → linear (twist⁺ z)) (gen-diag d) L⁺)
        (subst (λ z → linear (twist⁻ z)) (gen-diag d) L⁻) e)

  gen-thunkable : ∀ {x y} {f : hom x y}
                → thunkable (twist⁺ y) → thunkable (twist⁻ y)
                → gen f → thunkable f
  gen-thunkable T⁺ T⁻ gen-twist⁺ = T⁺
  gen-thunkable T⁺ T⁻ gen-twist⁻ = T⁻
  gen-thunkable T⁺ T⁻ (gen-⨾⁺ {f = f} {g = g} d e) =
    thunkable-⨾⁺ f g
      (gen-thunkable
        (subst (λ z → thunkable (twist⁺ z)) (sym (gen-diag e)) T⁺)
        (subst (λ z → thunkable (twist⁻ z)) (sym (gen-diag e)) T⁻) d)
      (gen-thunkable T⁺ T⁻ e)
  gen-thunkable T⁺ T⁻ (gen-⨾⁻ {f = f} {g = g} _ e) =
    thunkable-⨾⁻ f g (gen-thunkable T⁺ T⁻ e)

  positive-generated
    : (∀ {a b} (f : hom a b) → gen f)
    → ∀ x → linear (twist⁺ x) → linear (twist⁻ x) → positive x
  positive-generated gA x L⁺ L⁻ y f = gen-linear L⁺ L⁻ (gA f)

  negative-generated
    : (∀ {a b} (f : hom a b) → gen f)
    → ∀ x → thunkable (twist⁺ x) → thunkable (twist⁻ x) → negative x
  negative-generated gA x T⁺ T⁻ y f = gen-thunkable T⁺ T⁻ (gA f)
```

## The unit-law converse

Each hand's balanced unit law, fixed at one object, is the exact
consumable. With `unitl⁺` at `x`, every edge out of `x` is the
positive twist cut before that edge. `linear-⨾⁺` then finishes from
the twist alone. Dually with `unitr⁻` at `x` and `thunkable-⨾⁻`. The
balanced tier proves both laws from invertibility, and a deductive
system carries both tiers. So at full strength one edge decides its
object's polarity, with no generation hypothesis.

```agda
  positive-from-unit
    : ∀ x → (∀ {v} (s : hom x v) → twist⁺ x ⨾⁺ s ≡ s)
    → linear (twist⁺ x) → positive x
  positive-from-unit x ul L y f =
    subst (λ e → linear e) (ul f) (linear-⨾⁺ (twist⁺ x) f L)

  negative-from-unit
    : ∀ x → (∀ {w} (k : hom w x) → k ⨾⁻ twist⁻ x ≡ k)
    → thunkable (twist⁻ x) → negative x
  negative-from-unit x ur T y f =
    subst (λ e → thunkable e) (ur f) (thunkable-⨾⁻ f (twist⁻ x) T)

  module full (T⁻ : is-invertible⁻ G) (T⁺ : is-invertible⁺ G) where
    open balanced T⁻ T⁺

    positive-of-twist⁺ : ∀ x → linear (twist⁺ x) → positive x
    positive-of-twist⁺ x = positive-from-unit x unitl⁺

    negative-of-twist⁻ : ∀ x → thunkable (twist⁻ x) → negative x
    negative-of-twist⁻ x = negative-from-unit x unitr⁻
```

## The twists generate the word model

Every canonical descriptor is a cut word in the two twists.
`gen-sem` recurses on the descriptor. A pure translation peels one
negative twist per step. A zero head is one guard, the negative
cut against the identity. A positive head keeps every value
positive, by weak monotonicity. The word is then the negative
twist cut onto the pointwise predecessor, whose tail value drops
by one. The recursion consumes weak monotonicity alone, and the
minimality constraint rides along inside `W`.

```agda
module word-model where
  open polarity BW BW-stable BW-comp⁺ BW-comp⁻

  linear-τ̂ : linear τ̂
  linear-τ̂ = run→linear τ̂ refl

  thunkable-ε̂ : thunkable ε̂
  thunkable-ε̂ = rise→thunkable ε̂ refl

  mapPred : List Nat → List Nat
  mapPred []      = []
  mapPred (x ∷ p) = Nat.pred x ∷ mapPred p

  ev-mapPred : ∀ p u n → ev (mapPred p) u n ≡ Nat.pred (ev p (S u) n)
  ev-mapPred []      u n     = sym (ap Nat.pred (Nat.add.+suc n u))
  ev-mapPred (x ∷ p) u Z     = refl
  ev-mapPred (x ∷ p) u (S n) = ev-mapPred p u n

  incr-mapPred : ∀ p u → So (incr? p (S u)) → So (incr? (mapPred p) u)
  incr-mapPred []      u s = tt
  incr-mapPred (x ∷ p) u s =
    so-and (Nat.pred x ≤ᵇ ev (mapPred p) u Z) (incr? (mapPred p) u)
      (≤ᵇ-complete (Nat.pred x) (ev (mapPred p) u Z)
        (subst (Nat.pred x ≤_) (sym (ev-mapPred p u Z))
          (Nat.le.pred-mono
            (≤ᵇ-sound x (ev p (S u) Z)
              (so-fst (x ≤ᵇ ev p (S u) Z) (incr? p (S u)) s)))))
      (incr-mapPred p u (so-snd (x ≤ᵇ ev p (S u) Z) (incr? p (S u)) s))

  head-le : ∀ x p t → So (incr? (x ∷ p) t) → x ≤ t
  head-le x p t s =
    Nat.le.cat
      (≤ᵇ-sound x (ev p t Z) (so-fst (x ≤ᵇ ev p t Z) (incr? p t) s))
      (subst (ev p t Z ≤_) tail-val
        (ev-mono-le p t (so-snd (x ≤ᵇ ev p t Z) (incr? p t) s)
          Z (length p) Nat.lt.z<s))
    where
    tail-val : ev p t (length p) ≡ t
    tail-val =
      subst (λ m → ev p t m ≡ t) (Nat.add.unitr (length p)) (ev-past p t Z)

  spred : ∀ v → (Σ j ∶ Nat , v ≡ S j) → S (Nat.pred v) ≡ v
  spred v (j , e) = ap (λ m → S (Nat.pred m)) e ∙ sym e

  gen-sem : ∀ p t → So (incr? p t)
          → Σ A ∶ W , gen A × (∀ n → evW A n ≡ ev p t n)
  gen-sem [] Z s = ε̂ , gen-twist⁺ , λ n → refl
  gen-sem [] (S u) s = τ̂ ⨾⁺ A' , gen-⨾⁺ gen-twist⁻ dA' , path
    where
    ih : Σ A ∶ W , gen A × (∀ n → evW A n ≡ ev [] u n)
    ih = gen-sem [] u tt

    A' : W
    A' = ih .fst

    dA' : gen A'
    dA' = ih .snd .fst

    path : ∀ n → evW (τ̂ ⨾⁺ A') n ≡ ev [] (S u) n
    path n =
      ev-comp τ̂ A' n
      ∙ ap (evW τ̂) (ih .snd .snd n)
      ∙ ev-τ (n + u)
      ∙ sym (Nat.add.+suc n u)
  gen-sem (Z ∷ p) t s = A' ⨾⁻ ε̂ , gen-⨾⁻ dA' gen-twist⁺ , path
    where
    ih : Σ A ∶ W , gen A × (∀ n → evW A n ≡ ev p t n)
    ih = gen-sem p t (so-snd (Z ≤ᵇ ev p t Z) (incr? p t) s)

    A' : W
    A' = ih .fst

    dA' : gen A'
    dA' = ih .snd .fst

    path : ∀ n → evW (A' ⨾⁻ ε̂) n ≡ ev (Z ∷ p) t n
    path Z     = ev-cutε A' Z
    path (S m) = ev-cutε A' (S m) ∙ ih .snd .snd m
  gen-sem (S y ∷ p) Z s =
    ex-falso (Nat.lt.¬n<z (Nat.lt.peel Z (head-le (S y) p Z s)))
  gen-sem (S y ∷ p) (S u) s = τ̂ ⨾⁺ A' , gen-⨾⁺ gen-twist⁻ dA' , path
    where
    ih : Σ A ∶ W , gen A × (∀ n → evW A n ≡ ev (y ∷ mapPred p) u n)
    ih = gen-sem (y ∷ mapPred p) u (incr-mapPred (S y ∷ p) u s)

    A' : W
    A' = ih .fst

    dA' : gen A'
    dA' = ih .snd .fst

    pos-at : ∀ n → Σ j ∶ Nat , ev (S y ∷ p) (S u) n ≡ S j
    pos-at Z     = y , refl
    pos-at (S m) =
      le-pos y (ev p (S u) m)
        (Nat.le.cat
          (≤ᵇ-sound (S y) (ev p (S u) Z)
            (so-fst (S y ≤ᵇ ev p (S u) Z) (incr? p (S u)) s))
          (ev-mono-le p (S u)
            (so-snd (S y ≤ᵇ ev p (S u) Z) (incr? p (S u)) s)
            Z m Nat.lt.z<s))

    path : ∀ n → evW (τ̂ ⨾⁺ A') n ≡ ev (S y ∷ p) (S u) n
    path n =
      ev-comp τ̂ A' n
      ∙ ap (evW τ̂) (ih .snd .snd n ∙ ev-mapPred (S y ∷ p) u n)
      ∙ ev-τ (Nat.pred (ev (S y ∷ p) (S u) n))
      ∙ spred (ev (S y ∷ p) (S u) n) (pos-at n)

  gen-all : (A : W) → gen A
  gen-all A =
    subst (λ B → gen B) (ev-inj (g .fst) A (g .snd .snd)) (g .snd .fst)
    where
    g : Σ B ∶ W , gen B × (∀ n → evW B n ≡ evW A n)
    g = gen-sem (A .fst) (A .snd .fst) (w-inc A)

  positive-two-edge : linear ε̂ → linear τ̂ → positive tt
  positive-two-edge = positive-generated (λ f → gen-all f) tt

  negative-two-edge : thunkable ε̂ → thunkable τ̂ → negative tt
  negative-two-edge = negative-generated (λ f → gen-all f) tt

  positive-empty : ¬ positive tt
  positive-empty P = linear-refuted (P tt ε̂)

  negative-empty : ¬ negative tt
  negative-empty N = thunkable-refuted (N tt τ̂)
```

## What the spike settles

The two-edge check is the polarity. On a generated carrier both
twists decide it, over the bare tower. At full deductive-system
strength one edge decides it, with no generation hypothesis. So no
deductive system separates the twist condition from the polarity.
`full.positive-of-twist⁺` and `full.negative-of-twist⁻` close that
search space outright.

The closures hold unconditionally over the tower. The one open
case is a stable and composable carrier that is neither invertible
nor generated. Nothing here decides whether the two-edge check
suffices there. The generated-carrier tier itself is narrow: it
applies only where every edge is a `gen-diag` loop, so it says
nothing about a carrier with a non-loop edge.

`gen-all` writes every edge of the word model as a cut word in
the twists. Its polarities stay empty because each hypothesis
pair already fails on one twist, not because generation fails.

This module restates `positive` and `negative` rather than
importing `Cat.Logic.Gist.PolarityHLevel`'s copy. Their natural
future home is one shared definition beside `thunkable` and
`linear` in `Cat.Logic.Base`, which erasure does not restrict.

verified: `just check Cat.Logic.Gist.PolarityTwist`, 2026-07-29, zero
warnings, no holes, no postulates.
