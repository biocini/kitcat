Spike: the framed cut at an arbitrary framing

The path groupoid on a type, framed by two arbitrary families of loops.
Representability is total there, so every tier of a deductive system
holds without any condition on the framing — the framing is free and the
package is inhabited untruncated.

What the framing then decides is where the units are. The two twists are
the tiers' centres unconditionally; whether either is a unit for its
hand's composition is one equation, and a unit exists whether or not
that equation holds. So a neutral unit and a nontrivial framing are not
in competition: the neutral unit is simply not a twist.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeFramedCut where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom; is-contr→is-prop)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (_≃_; is-equiv; eqv-fibers; iso→equiv)
open import Core.Equiv.Properties using (_∙e_; Π-contr-dom)
open import Core.Groupoid.Virtual using (module yon-unbiased)

open import Cat.Logic.Type
open import Cat.Logic.Base
```

## The carrier

```agda
module path {u} {A : Type u} (t⁺ t⁻ : (x : A) → x ≡ x) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  emb-equiv : {x y : A} → is-equiv (emb {x} {y})
  emb-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob          = A
  PG .virtual-graph.hom x y     = x ≡ y
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)
  PG .virtual-graph.twist⁺      = t⁺
  PG .virtual-graph.twist⁻      = t⁻

  open virtual-graph PG
  open sequents PG

  term-contr : ∀ x → is-contr (term x)
  term-contr x .center = x , refl
  term-contr x .paths (w , p) i = p (~ i) , λ j → p (~ i ∨ j)

  coterm-contr : ∀ y → is-contr (coterm y)
  coterm-contr y .center = y , refl
  coterm-contr y .paths (v , p) i = p i , λ j → p (i ∧ j)

  recentre : ∀ {ℓ} {T : Type ℓ} → is-contr T → T → is-contr T
  recentre c t .center = t
  recentre c t .paths s = sym (c .paths t) ∙ c .paths s

  curry≃ : ∀ {x y} → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z) ≃ judgment x y
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  reflect-equiv : ∀ {x y} → is-equiv (reflect {x} {y})
  reflect-equiv = ((emb , emb-equiv) ∙e curry≃) .snd

  slot≃ : ∀ {x y}
        → judgment x y ≃ ((t : term x) (γ : coterm y) → hom (t .fst) (γ .fst))
  slot≃ = iso→equiv (λ α t γ → α (t , γ)) (λ Φ δ → Φ (δ .fst) (δ .snd))
                    (λ _ → refl) (λ _ → refl)

  slot-swap≃ : ∀ {x y}
             → judgment x y ≃ ((γ : coterm y) (t : term x) → hom (t .fst) (γ .fst))
  slot-swap≃ = iso→equiv (λ α γ t → α (t , γ)) (λ Φ δ → Φ (δ .snd) (δ .fst))
                         (λ _ → refl) (λ _ → refl)

  coact-π-equiv : ∀ x → is-equiv (coact-π {x} {x})
  coact-π-equiv x =
    ( (reflect , reflect-equiv)
    ∙e slot≃
    ∙e Π-contr-dom (recentre (term-contr x) (var x)) ) .snd

  act-π-equiv : ∀ x → is-equiv (act-π {x} {x})
  act-π-equiv x =
    ( (reflect , reflect-equiv)
    ∙e slot-swap≃
    ∙e Π-contr-dom (recentre (coterm-contr x) (covar x)) ) .snd
```

## The package, at any framing

```agda
  PG-stable : is-stable PG
  PG-stable α = is-contr→is-prop (eqv-fibers reflect-equiv α)

  PG-composable⁻ : is-composable⁻ PG
  PG-composable⁻ f g = eqv-fibers reflect-equiv (composite⁻ PG f g) .center

  PG-composable⁺ : is-composable⁺ PG
  PG-composable⁺ f g = eqv-fibers reflect-equiv (composite⁺ PG f g) .center

  PG-unital⁻ : is-unital⁻ PG
  PG-unital⁻ x = eqv-fibers (coact-π-equiv x) (cell⁻ PG x)

  PG-unital⁺ : is-unital⁺ PG
  PG-unital⁺ x = eqv-fibers (act-π-equiv x) (cell⁺ PG x)

  PG-composable : is-composable PG PG-stable
  PG-composable .is-composable.contr⁻ = PG-composable⁻
  PG-composable .is-composable.contr⁺ = PG-composable⁺

  PG-unital : is-unital PG
  PG-unital .is-unital.fiber⁻ = PG-unital⁻
  PG-unital .is-unital.fiber⁺ = PG-unital⁺

  PG-deductive : is-deductive-system PG
  PG-deductive .is-deductive-system.stable     = PG-stable
  PG-deductive .is-deductive-system.composable = PG-composable
  PG-deductive .is-deductive-system.unital     = PG-unital

  PG-system : deductive-system u u
  PG-system .deductive-system.graph  = PG
  PG-system .deductive-system.axioms = PG-deductive

  open tower PG-stable PG-composable⁻ PG-composable⁺
```

## The twists are the centres

Each tier's condition read at the axiom half of its argument is the
flank exchange, so `pcom.lr` places each twist in the other hand's
fiber, and the argument half being contractible carries it everywhere.
The framing is not consulted.

```agda
  pin⁻-axiom : ∀ x → coact-π (t⁺ x) (x , refl) ≡ cell⁻ PG x (x , refl)
  pin⁻-axiom x = sym (pcom.lr (t⁻ x) (t⁺ x))

  pin⁺-axiom : ∀ x → act-π (t⁻ x) (x , refl) ≡ cell⁺ PG x (x , refl)
  pin⁺-axiom x = pcom.lr (t⁻ x) (t⁺ x)

  pin⁻ : ∀ x → coact-π (t⁺ x) ≡ cell⁻ PG x
  pin⁻ x = funext λ γ →
    subst (λ c → coact-π (t⁺ x) c ≡ cell⁻ PG x c)
          (coterm-contr x .paths γ) (pin⁻-axiom x)

  pin⁺ : ∀ x → act-π (t⁻ x) ≡ cell⁺ PG x
  pin⁺ x = funext λ t →
    subst (λ s → act-π (t⁻ x) s ≡ cell⁺ PG x s)
          (term-contr x .paths t) (pin⁺-axiom x)

  twist⁺-centre : ∀ x → PG-unital⁻ x .center .fst ≡ t⁺ x
  twist⁺-centre x = ap fst (PG-unital⁻ x .paths (t⁺ x , pin⁻ x))

  twist⁻-centre : ∀ x → PG-unital⁺ x .center .fst ≡ t⁻ x
  twist⁻-centre x = ap fst (PG-unital⁺ x .paths (t⁻ x , pin⁺ x))

  twist⁺-unique : ∀ x (e : x ≡ x) → coact-π e ≡ cell⁻ PG x → t⁺ x ≡ e
  twist⁺-unique x e w =
    sym (twist⁺-centre x) ∙ ap fst (PG-unital⁻ x .paths (e , w))

  twist⁻-unique : ∀ x (e : x ≡ x) → act-π e ≡ cell⁺ PG x → t⁻ x ≡ e
  twist⁻-unique x e w =
    sym (twist⁻-centre x) ∙ ap fst (PG-unital⁺ x .paths (e , w))
```

## One equation

The two cancellation hypotheses are the same equation read on the two
hands: the composite of the twists at an object is trivial. That is the
framing's own content and nothing above it decides it — the tiers hold
either way.

```agda
  cancels : Type u
  cancels = ∀ x → pcom.composite refl (t⁻ x) (t⁺ x) ≡ refl

  trivial⁻ : cancels → ∀ x → cell⁻ PG x ≡ snd
  trivial⁻ K x = funext λ γ →
    subst (λ c → cell⁻ PG x c ≡ c .snd) (coterm-contr x .paths γ) (K x)

  trivial⁺ : cancels → ∀ x → cell⁺ PG x ≡ snd
  trivial⁺ K x = funext λ t →
    subst (λ s → cell⁺ PG x s ≡ s .snd) (term-contr x .paths t)
          (sym (pcom.lr (t⁻ x) (t⁺ x)) ∙ K x)

  module cancelled (K : cancels) where
    open unital pin⁻ pin⁺ (trivial⁻ K) (trivial⁺ K) public
```

Under it each hand gains its one unit law and the twists compose to
twists: `unitr⁻`, `unitl⁺`, `pair⁺` and `pair⁻` come from the module,
crossed as the tiers predict.

## A unit exists regardless

A right unit for the coterm hand is an edge whose action is the second
projection — an inhabitant of the fiber of the same map over `snd`
rather than over `cell⁻`. Representability being total, that fiber is
inhabited at every framing, so the composition has a unit whether or not
the twists cancel. What the equation decides is only whether that unit
*is* the twist.

```agda
  neutral⁻ : ∀ x → fiber (coact-π {x} {x}) snd
  neutral⁻ x = eqv-fibers (coact-π-equiv x) snd .center

  neutral⁻-absorb : ∀ {y} (k : coterm y) → coact (neutral⁻ y .fst) k ≡ k
  neutral⁻-absorb {y} k i = k .fst , neutral⁻ y .snd i k

  neutral⁻-unitr : ∀ {x y} (f : hom x y) → f ⨾⁻ neutral⁻ y .fst ≡ f
  neutral⁻-unitr f = lc
    ( reflect-⨾⁻ f (neutral⁻ _ .fst)
    ∙ (λ i γ → reflect f (γ .fst , neutral⁻-absorb (γ .snd) i)) )

  neutral⁺ : ∀ x → fiber (act-π {x} {x}) snd
  neutral⁺ x = eqv-fibers (act-π-equiv x) snd .center

  neutral⁺-absorb : ∀ {x} (t : term x) → act (neutral⁺ x .fst) t ≡ t
  neutral⁺-absorb {x} t i = t .fst , neutral⁺ x .snd i t

  neutral⁺-unitl : ∀ {x y} (g : hom x y) → neutral⁺ x .fst ⨾⁺ g ≡ g
  neutral⁺-unitl g = lc
    ( reflect-⨾⁺ (neutral⁺ _ .fst) g
    ∙ (λ i γ → reflect g (neutral⁺-absorb (γ .fst) i , γ .snd)) )
```

And the two agree exactly when the equation holds: the twist inhabits
the `snd`-fiber precisely then, and contractibility identifies it with
the neutral.

```agda
  module _ (K : cancels) where
    twist-is-neutral⁻ : ∀ x → neutral⁻ x .fst ≡ t⁺ x
    twist-is-neutral⁻ x =
      ap fst (eqv-fibers (coact-π-equiv x) snd .paths
               (t⁺ x , pin⁻ x ∙ trivial⁻ K x))

    twist-is-neutral⁺ : ∀ x → neutral⁺ x .fst ≡ t⁻ x
    twist-is-neutral⁺ x =
      ap fst (eqv-fibers (act-π-equiv x) snd .paths
               (t⁻ x , pin⁺ x ∙ trivial⁺ K x))
```

## What the spike settles

`PG-deductive` is the whole package at an arbitrary framing over an
arbitrary type, with no h-level hypothesis: stability, both cuts, both
unit tiers. Nothing in it constrains the twists, and `twist⁺-centre`,
`twist⁻-centre` show why — the tiers place each twist in the other
hand's fiber by the flank exchange alone, so the framing is free and the
centres track it.

`cancels` is one equation, and both hands' triviality follows from it by
the same exchange. It is the framing's own content: mutual inverseness
of the twists, with the twists themselves still arbitrary.

The neutral unit was never in competition with the framing.
`neutral⁻-unitr` and `neutral⁺-unitl` give each composition a unit at
*every* framing — representability being total is enough — and
`twist-is-neutral⁻`, `twist-is-neutral⁺` say the unit is the twist
exactly when the equation holds. So a framed system has a unit that is
not a twist, and the crossed pairing the tiers deliver is the framing
showing through rather than a substitute for a missing unit.
