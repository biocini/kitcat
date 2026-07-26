Spike: the unit laws as carrier structure, so that the predicate is a
proposition.

Pinning an independently chosen `idn` to the unit is a path in a hom
type — `Test.SpikeStabilityShape` computes it — so no predicate over a
graph carrying `idn` freely can assert it propositionally. The way out
is not another packaging but a different division: the chosen edge
comes *with* its two absorptions, as structure, and the predicate over
that structure is three contractibility statements and nothing else.

`reflect`'s type needs only objects and edges, so the chosen edge and
its laws can be declared after it, in order.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeReflexiveVG where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom)
open import Core.Path.Base
open import Core.Equiv.Base using (_≃_; is-equiv; iso→equiv; eqv-fibers)
open import Core.Equiv.Properties using (_∙e_; is-equiv-is-prop; Π-contr-dom)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; ×-is-hlevel)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Groupoid.Virtual using (module yon-unbiased)

import Test.AnchorPin as AP
```

## The carrier

```agda
record reflexive-virtual-graph o h : Type₊ (o ⊔ h) where
  field
    ob  : Type o
    hom : ob → ob → Type h

  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v

  argument : ob → ob → Type (o ⊔ h)
  argument x y = term x × coterm y

  conclusion : ∀ {x y} → argument x y → Type h
  conclusion γ = hom (γ .fst .fst) (γ .snd .fst)

  judgment : ob → ob → Type (o ⊔ h)
  judgment x y = (γ : argument x y) → conclusion γ

  field
    reflect : ∀ {x y} → hom x y → judgment x y
    idn     : (x : ob) → hom x x

  var : (x : ob) → term x
  var x = x , idn x

  covar : (y : ob) → coterm y
  covar y = y , idn y

  eval : ∀ {x y} → judgment x y → hom x y
  eval {x} {y} α = α (var x , covar y)

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f ((var x) , γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (t , covar y)

  field
    absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
    absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
```

## Opposition on the carrier

Terms and coterms exchange, each axiom half becomes the other, and so
the two actions and the two absorptions exchange **definitionally**.
Opposition is an involution on the nose.

```agda
opᴿ : ∀ {o h} → reflexive-virtual-graph o h → reflexive-virtual-graph o h
opᴿ G .reflexive-virtual-graph.ob          = reflexive-virtual-graph.ob G
opᴿ G .reflexive-virtual-graph.hom x y     = reflexive-virtual-graph.hom G y x
opᴿ G .reflexive-virtual-graph.reflect f γ = reflexive-virtual-graph.reflect G f (γ .snd , γ .fst)
opᴿ G .reflexive-virtual-graph.idn         = reflexive-virtual-graph.idn G
opᴿ G .reflexive-virtual-graph.absorb⁻     = reflexive-virtual-graph.absorb⁺ G
opᴿ G .reflexive-virtual-graph.absorb⁺     = reflexive-virtual-graph.absorb⁻ G

opᴿ-invol : ∀ {o h} (G : reflexive-virtual-graph o h) → opᴿ (opᴿ G) ≡ G
opᴿ-invol _ = refl
```

## The predicate

Three contractibility statements. Composability's two fibers, the
two unit fibers, and stability as an equivalence.

```agda
module _ {o h} (G : reflexive-virtual-graph o h) where
  open reflexive-virtual-graph G

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact {x} f e = e .fst , coact-π f e

  act : ∀ {x y} → hom x y → term x → term y
  act {y = y} f t = t .fst , act-π f t

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (γ .fst , coact g (γ .snd))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect g (act f (γ .fst) , γ .snd)

  is-representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  is-representable = fiber reflect

  readback : Type (o ⊔ h)
  readback = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f

  flank : Type (o ⊔ h)
  flank = ∀ x → eval (reflect (idn x)) ≡ idn x

  restrict : readback → flank
  restrict u x = u (idn x)

  is-composable : Type (o ⊔ h)
  is-composable =
      (∀ {x y z} (f : hom x y) (g : hom y z) → is-contr (is-representable (composite⁻ f g)))
    × (∀ {x y z} (f : hom x y) (g : hom y z) → is-contr (is-representable (composite⁺ f g)))

  is-unital : Type (o ⊔ h)
  is-unital = (∀ x → is-contr (fiber (coact-π {x} {x}) snd))
            × (∀ x → is-contr (fiber (act-π   {x} {x}) snd))

  is-stable : Type (o ⊔ h)
  is-stable = is-equiv restrict

  record is-deductive-system : Type (o ⊔ h) where
    field
      composable : is-composable
      unital     : is-unital
      stable     : is-stable
```

The chosen edge inhabits the unit fiber by the carrier's own laws, so
contractibility makes it *the* unit — canonical and unique together.

```agda
  module _ (U : is-unital) where
    unit⁻ unit⁺ : ∀ x → hom x x
    unit⁻ x = U .fst x .center .fst
    unit⁺ x = U .snd x .center .fst

    idn-is-unit⁻ : ∀ x → unit⁻ x ≡ idn x
    idn-is-unit⁻ x = ap fst (U .fst x .paths (idn x , funext (absorb⁻ x)))

    idn-is-unit⁺ : ∀ x → unit⁺ x ≡ idn x
    idn-is-unit⁺ x = ap fst (U .snd x .paths (idn x , funext (absorb⁺ x)))

    units-agree : ∀ x → unit⁻ x ≡ unit⁺ x
    units-agree x = idn-is-unit⁻ x ∙ sym (idn-is-unit⁺ x)

    unit⁻-unique : ∀ x (e : hom x x) → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ idn x
    unit⁻-unique x e p =
      sym (ap fst (U .fst x .paths (e , funext p))) ∙ idn-is-unit⁻ x

    unit⁺-unique : ∀ x (e : hom x x) → (∀ t → act-π e t ≡ t .snd) → e ≡ idn x
    unit⁺-unique x e p =
      sym (ap fst (U .snd x .paths (e , funext p))) ∙ idn-is-unit⁺ x
```

## The predicate is a proposition

Every field is a contractibility or an `is-equiv`, so this is immediate
— and it is what the carrier change buys.

```agda
  is-composable-is-prop : is-prop is-composable
  is-composable-is-prop =
    ×-is-hlevel 1
      (Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
       Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _)
      (Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
       Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _)

  is-unital-is-prop : is-prop is-unital
  is-unital-is-prop =
    ×-is-hlevel 1 (Π-is-prop λ _ → is-contr-is-prop _)
                  (Π-is-prop λ _ → is-contr-is-prop _)

  is-stable-is-prop : is-prop is-stable
  is-stable-is-prop = is-equiv-is-prop _

  is-deductive-system-is-prop : is-prop is-deductive-system
  is-deductive-system-is-prop D D' i .is-deductive-system.composable =
    is-composable-is-prop (is-deductive-system.composable D)
                          (is-deductive-system.composable D') i
  is-deductive-system-is-prop D D' i .is-deductive-system.unital =
    is-unital-is-prop (is-deductive-system.unital D)
                      (is-deductive-system.unital D') i
  is-deductive-system-is-prop D D' i .is-deductive-system.stable =
    is-stable-is-prop (is-deductive-system.stable D)
                      (is-deductive-system.stable D') i
```

## The path groupoid, untruncated

The carrier's two absorptions are `pcom`'s idempotence laws, so the
path graph of *any* type is a reflexive virtual graph outright.

```agda
module path {u} (A : Type u) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  PG : reflexive-virtual-graph u u
  PG .reflexive-virtual-graph.ob      = A
  PG .reflexive-virtual-graph.hom x y = x ≡ y
  PG .reflexive-virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)
  PG .reflexive-virtual-graph.idn x   = refl
  PG .reflexive-virtual-graph.absorb⁻ x γ = pcom.ideml (γ .snd)
  PG .reflexive-virtual-graph.absorb⁺ x t = pcom.idemr (t .snd)

  open reflexive-virtual-graph PG
```

Representability is total, so composability is handed over; each
action at reflexivity is an equivalence, so each unit fiber is
contractible; and restriction is `AnchorPin`'s singleton contraction.

```agda
  curry≃ : ∀ {x y} → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z) ≃ judgment x y
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  reflect-equiv : ∀ {x y} → is-equiv (reflect {x} {y})
  reflect-equiv = ((emb , yon-unbiased.emb-equiv {A = λ _ → A}) ∙e curry≃) .snd

  PG-composable : is-composable PG
  PG-composable = (λ f g → eqv-fibers reflect-equiv (composite⁻ PG f g))
                , (λ f g → eqv-fibers reflect-equiv (composite⁺ PG f g))

  term-contr : ∀ x → is-contr (term x)
  term-contr x .center = var x
  term-contr x .paths (w , p) i = p (~ i) , λ j → p (~ i ∨ j)

  coterm-contr : ∀ y → is-contr (coterm y)
  coterm-contr y .center = covar y
  coterm-contr y .paths (v , p) i = p i , λ j → p (i ∧ j)

  coact-π-equiv : ∀ x → is-equiv (coact-π {x} {x})
  coact-π-equiv x =
    ((reflect , reflect-equiv)
      ∙e iso→equiv (λ α t γ → α (t , γ)) (λ Φ δ → Φ (δ .fst) (δ .snd))
                   (λ _ → refl) (λ _ → refl)
      ∙e Π-contr-dom {B = λ t → (γ : coterm x) → hom (t .fst) (γ .fst)}
                     (term-contr x)) .snd

  act-π-equiv : ∀ x → is-equiv (act-π {x} {x})
  act-π-equiv x =
    ((reflect , reflect-equiv)
      ∙e iso→equiv (λ α γ t → α (t , γ)) (λ Φ δ → Φ (δ .snd) (δ .fst))
                   (λ _ → refl) (λ _ → refl)
      ∙e Π-contr-dom {B = λ γ → (t : term x) → hom (t .fst) (γ .fst)}
                     (coterm-contr x)) .snd

  PG-unital : is-unital PG
  PG-unital = (λ x → eqv-fibers (coact-π-equiv x) snd)
            , (λ x → eqv-fibers (act-π-equiv x) snd)

  T : ∀ {x y : A} → x ≡ y → x ≡ y
  T {x} {y} p = emb p x refl y refl

  t₀ : ∀ (x : A) → T (refl {x = x}) ≡ refl
  t₀ x = pcom.unit refl

  rb≃ : readback PG ≃ (∀ (x y : A) (p : x ≡ y) → T p ≡ p)
  rb≃ = iso→equiv (λ v _ _ p → v p) (λ rd p → rd _ _ p) (λ _ → refl) (λ _ → refl)

  PG-stable : is-stable PG
  PG-stable =
    (rb≃ ∙e (AP.at-refl T t₀
            , iso→equiv (AP.at-refl T t₀) (AP.extend T t₀)
                        (AP.extend-retract T t₀)
                        (λ v → funext (AP.extend-refl T t₀ v)) .snd)) .snd

  PG-deductive : is-deductive-system PG
  PG-deductive .is-deductive-system.composable = PG-composable
  PG-deductive .is-deductive-system.unital     = PG-unital
  PG-deductive .is-deductive-system.stable     = PG-stable
```

## How much of the unit tier the carrier already implies

The carrier's own absorption at the axiom half *is* a flank element,
so stability's equivalence hands back a readback family with no unit
tier in sight. Uniqueness of an absorbing edge follows from that.

```agda
module redundancy {o h} (G : reflexive-virtual-graph o h) (S : is-stable G) where
  open reflexive-virtual-graph G

  flank-pt : flank G
  flank-pt x = absorb⁻ x (covar x)

  rb : readback G
  rb = S .eqv-fibers flank-pt .center .fst

  absorber-is-idn⁻ : ∀ x (e : hom x x) → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ idn x
  absorber-is-idn⁻ x e p = sym (rb e) ∙ p (covar x)

  absorber-is-idn⁺ : ∀ x (e : hom x x) → (∀ t → act-π e t ≡ t .snd) → e ≡ idn x
  absorber-is-idn⁺ x e p = sym (rb e) ∙ p (var x)
```
