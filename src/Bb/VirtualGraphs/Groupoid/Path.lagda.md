The path groupoid on a type, framed by two arbitrary families of
loops. Representability is total, so every hypothesis group holds
with no condition on the framing and no h-level on the type: the
framing is free and the package is inhabited untruncated. What the
framing then decides is where the twists sit. Each hand's unit is
that hand's tier's own centre and exists at every framing; the
twists are the centres of the cell fibers instead, and whether the
two centres coincide is one equation — the composite of the twists
at an object is trivial. A neutral unit and a nontrivial framing are
not in competition: the neutral unit is simply not a twist. The
one-twist instance closes the file: at an arbitrary one-sided
framing the extraction telescope is inhabited entire.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Groupoid.Path where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom; is-contr→is-prop)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (_≃_; is-equiv; eqv-fibers; iso→equiv)
open import Core.Equiv.Properties using (_∙e_; Π-contr-dom)
open import Core.Groupoid.Virtual using (module yon-unbiased)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Extraction
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

  open virtual-graph PG using (term; coterm; judgment)
  open framing PG t⁻ t⁺

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

  reflect-equiv : ∀ {x y} → is-equiv (virtual-graph.reflect PG {x} {y})
  reflect-equiv = ((emb , emb-equiv) ∙e curry≃) .snd

  slot≃ : ∀ {x y}
        → judgment x y ≃ ((t : term x) (γ : coterm y) → t .fst ≡ γ .fst)
  slot≃ = iso→equiv (λ α t γ → α (t , γ)) (λ Φ δ → Φ (δ .fst) (δ .snd))
                    (λ _ → refl) (λ _ → refl)

  slot-swap≃ : ∀ {x y}
             → judgment x y ≃ ((γ : coterm y) (t : term x) → t .fst ≡ γ .fst)
  slot-swap≃ = iso→equiv (λ α γ t → α (t , γ)) (λ Φ δ → Φ (δ .snd) (δ .fst))
                         (λ _ → refl) (λ _ → refl)

  coact-π-equiv : ∀ x → is-equiv (coact-π {x} {x})
  coact-π-equiv x =
    ( (virtual-graph.reflect PG , reflect-equiv)
    ∙e slot≃
    ∙e Π-contr-dom (recentre (term-contr x) (var x)) ) .snd

  act-π-equiv : ∀ x → is-equiv (act-π {x} {x})
  act-π-equiv x =
    ( (virtual-graph.reflect PG , reflect-equiv)
    ∙e slot-swap≃
    ∙e Π-contr-dom (recentre (coterm-contr x) (covar x)) ) .snd
```

## The package, at any framing

```agda
  PG-embedding : reflect-is-embedding PG
  PG-embedding α = is-contr→is-prop (eqv-fibers reflect-equiv α)

  PG-composable⁺ : is-composable⁺
  PG-composable⁺ f g = eqv-fibers reflect-equiv (composite⁺ f g) .center

  PG-composable⁻ : is-composable⁻
  PG-composable⁻ f g = eqv-fibers reflect-equiv (composite⁻ f g) .center

  PG-unital⁻ : is-absorbing⁻
  PG-unital⁻ x = eqv-fibers (coact-π-equiv x) snd

  PG-unital⁺ : is-absorbing⁺
  PG-unital⁺ x = eqv-fibers (act-π-equiv x) snd

  open tower PG t⁻ t⁺ PG-embedding PG-composable⁺ PG-composable⁻
    using (_⨾⁺_; _⨾⁻_; reflect-⨾⁺; reflect-⨾⁻; lc)
```

## The twists are the cells' centres

Each action map being an equivalence makes its fiber over the cell
contractible as well. Read at the axiom half of the argument,
membership of that fiber is the flank exchange, so `pcom.lr` places
each twist in the other hand's cell fiber, and the argument half
being contractible carries it everywhere. The framing is not
consulted.

```agda
  cell-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) (cell⁻ x))
  cell-fiber⁻ x = eqv-fibers (coact-π-equiv x) (cell⁻ x)

  cell-fiber⁺ : ∀ x → is-contr (fiber (act-π {x} {x}) (cell⁺ x))
  cell-fiber⁺ x = eqv-fibers (act-π-equiv x) (cell⁺ x)

  pin⁻-axiom : ∀ x → coact-π (t⁺ x) (x , refl) ≡ cell⁻ x (x , refl)
  pin⁻-axiom x = sym (pcom.lr (t⁻ x) (t⁺ x))

  pin⁺-axiom : ∀ x → act-π (t⁻ x) (x , refl) ≡ cell⁺ x (x , refl)
  pin⁺-axiom x = pcom.lr (t⁻ x) (t⁺ x)

  pin⁻ : ∀ x → coact-π (t⁺ x) ≡ cell⁻ x
  pin⁻ x = funext λ γ →
    subst (λ c → coact-π (t⁺ x) c ≡ cell⁻ x c)
          (coterm-contr x .paths γ) (pin⁻-axiom x)

  pin⁺ : ∀ x → act-π (t⁻ x) ≡ cell⁺ x
  pin⁺ x = funext λ t →
    subst (λ s → act-π (t⁻ x) s ≡ cell⁺ x s)
          (term-contr x .paths t) (pin⁺-axiom x)

  corx-centre : ∀ x → cell-fiber⁻ x .center .fst ≡ t⁺ x
  corx-centre x = ap fst (cell-fiber⁻ x .paths (t⁺ x , pin⁻ x))

  rx-centre : ∀ x → cell-fiber⁺ x .center .fst ≡ t⁻ x
  rx-centre x = ap fst (cell-fiber⁺ x .paths (t⁻ x , pin⁺ x))

  corx-unique : ∀ x (e : x ≡ x) → coact-π e ≡ cell⁻ x → t⁺ x ≡ e
  corx-unique x e w =
    sym (corx-centre x) ∙ ap fst (cell-fiber⁻ x .paths (e , w))

  rx-unique : ∀ x (e : x ≡ x) → act-π e ≡ cell⁺ x → t⁻ x ≡ e
  rx-unique x e w =
    sym (rx-centre x) ∙ ap fst (cell-fiber⁺ x .paths (e , w))
```

## One equation

The two cancellation hypotheses are the same equation read on the
two hands: the composite of the twists at an object is trivial.
That is the framing's own content, and nothing above it decides it —
the tiers hold either way.

```agda
  cancels : Type u
  cancels = ∀ x → pcom.composite refl (t⁻ x) (t⁺ x) ≡ refl

  trivial⁻ : cancels → ∀ x → cell⁻ x ≡ snd
  trivial⁻ K x = funext λ γ →
    subst (λ c → cell⁻ x c ≡ c .snd) (coterm-contr x .paths γ) (K x)

  trivial⁺ : cancels → ∀ x → cell⁺ x ≡ snd
  trivial⁺ K x = funext λ t →
    subst (λ s → cell⁺ x s ≡ s .snd) (term-contr x .paths t)
          (sym (pcom.lr (t⁻ x) (t⁺ x)) ∙ K x)

  module cancelled (K : cancels) where
    open unital PG t⁻ t⁺ PG-embedding PG-composable⁺ PG-composable⁻
      pin⁻ pin⁺ (trivial⁻ K) (trivial⁺ K) public
```

Under it each hand gains its one unit law and the twists compose to
twists: `unitr⁺`, `unitl⁻`, `pair⁻` and `pair⁺` come from the
module, crossed as the tiers predict.

## A unit exists regardless

A right unit for the coterm hand is an edge whose action is the
second projection, which is what that hand's tier already asks for,
and representability being total makes the tier hold at every
framing. What the equation decides is only whether that unit is the
twist: the twist inhabits the `snd`-fiber precisely under `cancels`,
and contractibility identifies it with the neutral.

```agda
  neutral⁻ : ∀ x → fiber (coact-π {x} {x}) snd
  neutral⁻ x = PG-unital⁻ x .center

  neutral⁻-absorb : ∀ {y} (k : coterm y) → coact (neutral⁻ y .fst) k ≡ k
  neutral⁻-absorb {y} k i = k .fst , neutral⁻ y .snd i k

  neutral⁻-unitr : ∀ {x y} (f : x ≡ y) → f ⨾⁺ neutral⁻ y .fst ≡ f
  neutral⁻-unitr f = lc
    ( reflect-⨾⁺ f (neutral⁻ _ .fst)
    ∙ (λ i γ → virtual-graph.reflect PG f (γ .fst , neutral⁻-absorb (γ .snd) i)) )

  neutral⁺ : ∀ x → fiber (act-π {x} {x}) snd
  neutral⁺ x = PG-unital⁺ x .center

  neutral⁺-absorb : ∀ {x} (t : term x) → act (neutral⁺ x .fst) t ≡ t
  neutral⁺-absorb {x} t i = t .fst , neutral⁺ x .snd i t

  neutral⁺-unitl : ∀ {x y} (g : x ≡ y) → neutral⁺ x .fst ⨾⁻ g ≡ g
  neutral⁺-unitl g = lc
    ( reflect-⨾⁻ (neutral⁺ _ .fst) g
    ∙ (λ i γ → virtual-graph.reflect PG g (neutral⁺-absorb (γ .fst) i , γ .snd)) )

  module _ (K : cancels) where
    twist-is-neutral⁻ : ∀ x → neutral⁻ x .fst ≡ t⁺ x
    twist-is-neutral⁻ x =
      ap fst (PG-unital⁻ x .paths (t⁺ x , pin⁻ x ∙ trivial⁻ K x))

    twist-is-neutral⁺ : ∀ x → neutral⁺ x .fst ≡ t⁻ x
    twist-is-neutral⁺ x =
      ap fst (PG-unital⁺ x .paths (t⁻ x , pin⁺ x ∙ trivial⁺ K x))
```

## The one-twist instance

At an arbitrary one-sided framing over an arbitrary type, the
extraction telescope is inhabited entire, with no h-level
hypothesis: the carrier imposes no truncation.

```agda
module one-twist {u} {A : Type u} (t⁻ : (x : A) → x ≡ x) where

  open path t⁻ t⁻ using
    (PG; coact-π-equiv; reflect-equiv; slot-swap≃; coterm-contr; recentre)

  U⁻ : framing⁻.is-absorbing⁻ PG t⁻
  U⁻ x = eqv-fibers (coact-π-equiv x) snd

  open extraction PG t⁻ U⁻

  S : reflect-is-embedding PG
  S α = is-contr→is-prop (eqv-fibers reflect-equiv α)

  C⁺ : is-composable⁺
  C⁺ f g = eqv-fibers reflect-equiv (composite⁺ f g) .center

  C⁻ : is-composable⁻
  C⁻ f g = eqv-fibers reflect-equiv (composite⁻ f g) .center

  act-π-equiv : ∀ x → is-equiv (act-π {x} {x})
  act-π-equiv x =
    ( (virtual-graph.reflect PG , reflect-equiv)
    ∙e slot-swap≃
    ∙e Π-contr-dom (recentre (coterm-contr x) (x , corx x)) ) .snd

  U⁺ : is-absorbing⁺
  U⁺ x = eqv-fibers (act-π-equiv x) snd

  open extraction.system⁻ PG t⁻ U⁻ S C⁺ C⁻ U⁺
    using (unitl⁻; cancel⁺; agree)
```
