Spike: the two compositions and where they meet.

There is no single composition. Terms and coterms are two displayed
reflexive graphs over the base, and each display's fibration condition
projects its own composite — push from the term display, pull from the
coterm display. The unit tier is stated in terms of both, which is why
it cannot be stated before the composability tier has projected them.

What the tier says is that the two agree at the unit: each composition
is idempotent there, and both land on the reflexive edge. The spike
checks three things. Each hand's absorption and its `emb-image-contr`
— the engine every coherence tower runs on — follow from that hand's
own data, readback-free. Readback is one statement rather than two,
since evaluating at the identity context fills both slots. And the two
absorptions at the unit inhabit the *same* type, so their agreement is
a well-formed statement that neither hand supplies: it is the one
cross-hand fact, and it is left uninhabited here.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikePerHandUnit where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv; eqv-fibers; iso→equiv)
open import Core.Function.Embedding using (equiv→lc)
open import Core.Groupoid.Virtual using (module yon-unbiased)

record reflexive-graph v e : Type₊ (v ⊔ e) where
  field
    vtx  : Type v
    edge : vtx → vtx → Type e
    rx   : (x : vtx) → edge x x
```

A virtual graph. Each hand is the ternary action read at the reflexive
edge in one slot: `yon` transports an incoming edge forward along `f`,
`noy` an outgoing edge backward.

```agda

module vgraph {v e} (G : reflexive-graph v e)
  (emb : ∀ {x y} → reflexive-graph.edge G x y
       → ∀ w → reflexive-graph.edge G w x
       → ∀ z → reflexive-graph.edge G y z
       → reflexive-graph.edge G w z)
  where
  open reflexive-graph G

  yon : ∀ {x y} → edge x y → ∀ w → edge w x → edge w y
  yon {y = y} f w a = emb f w a y (rx y)

  noy : ∀ {x y} → edge x y → ∀ z → edge y z → edge x z
  noy {x} f z b = emb f x (rx x) z b

  ev : ∀ {x y} → edge x y → edge x y
  ev {x} {y} f = emb f x (rx x) y (rx y)
```

The two strings a pair `f , g` spans, one per hand: `g` acting on the
outgoing slot, or `f` acting on the incoming one.

```agda

  E▿ : ∀ {x y z} → edge x y → edge y z
     → ∀ w → edge w x → ∀ t → edge z t → edge w t
  E▿ f g w a t b = emb f w a t (noy g t b)

  E▵ : ∀ {x y z} → edge x y → edge y z
     → ∀ w → edge w x → ∀ t → edge z t → edge w t
  E▵ f g w a t b = emb g w (yon f w a) t b
```

## Composability: two conditions, two compositions

```agda

  module hands
    (pull-contr : ∀ {x y z} (f : edge x y) (g : edge y z)
                → is-contr (fiber (emb {x} {z}) (E▿ f g)))
    (push-contr : ∀ {x y z} (f : edge x y) (g : edge y z)
                → is-contr (fiber (emb {x} {z}) (E▵ f g)))
    where

    _⨾▿_ : ∀ {x y z} → edge x y → edge y z → edge x z
    f ⨾▿ g = pull-contr f g .center .fst
    infixr 40 _⨾▿_

    _⨾▵_ : ∀ {x y z} → edge x y → edge y z → edge x z
    f ⨾▵ g = push-contr f g .center .fst
    infixr 40 _⨾▵_
```

Each hand's action distributes over its own composite, freely: the
fiber center's witness, read at the reflexive edge in the other slot.

```agda

    noy-composite
      : ∀ {x y z} (f : edge x y) (g : edge y z) {t} (b : edge z t)
      → noy (f ⨾▿ g) t b ≡ noy f t (noy g t b)
    noy-composite {x} f g b i = pull-contr f g .center .snd i x (rx x) _ b

    yon-composite
      : ∀ {x y z} (f : edge x y) (g : edge y z) {w} (a : edge w x)
      → yon (f ⨾▵ g) w a ≡ yon g w (yon f w a)
    yon-composite {z = z} f g a i = push-contr f g .center .snd i _ a z (rx z)
```

## The unit tier: both compositions, idempotent at the reflexive edge

```agda

    module unital
      (pull-eqv : ∀ {x t} → is-equiv (noy (rx x) t))
      (push-eqv : ∀ {x w} → is-equiv (yon (rx x) w))
      (idem▿ : ∀ {x} → rx x ⨾▿ rx x ≡ rx x)
      (idem▵ : ∀ {x} → rx x ⨾▵ rx x ≡ rx x)
      where
```

Both idempotences land on the reflexive edge, so the two compositions
agree there — and this is the only place the tier relates them.

```agda

      coincide : ∀ {x} → rx x ⨾▿ rx x ≡ rx x ⨾▵ rx x
      coincide = idem▿ ∙ sym idem▵
```

Each absorption is its own hand's cancellation: the unit action against
its own idempotence, over its own distributivity. Readback is not in
scope, and neither hand's data appears in the other's derivation.

```agda

      absorb▿ : ∀ {x t} (b : edge x t) → noy (rx x) t b ≡ b
      absorb▿ {x} {t} b = equiv→lc pull-eqv step
        where
        step : noy (rx x) t (noy (rx x) t b) ≡ noy (rx x) t b
        step = sym (noy-composite (rx x) (rx x) b)
             ∙ ap (λ s → noy s t b) idem▿

      absorb▵ : ∀ {x w} (a : edge w x) → yon (rx x) w a ≡ a
      absorb▵ {x} {w} a = equiv→lc push-eqv step
        where
        step : yon (rx x) w (yon (rx x) w a) ≡ yon (rx x) w a
        step = sym (yon-composite (rx x) (rx x) a)
             ∙ ap (λ s → yon s w a) idem▵
```

The engine, twice over. Each hand collapses its own string at the unit
and inherits the contractibility from its own composability field, so
the tower is available from either hand alone.

```agda

      shrink▿ : ∀ {x y} (f : edge x y) → E▿ f (rx y) ≡ emb f
      shrink▿ f i w a t b = emb f w a t (absorb▿ b i)

      emb-image-contr▿
        : ∀ {x y} (f : edge x y) → is-contr (fiber (emb {x} {y}) (emb f))
      emb-image-contr▿ {x} {y} f =
        subst (λ α → is-contr (fiber (emb {x} {y}) α))
              (shrink▿ f) (pull-contr f (rx y))

      shrink▵ : ∀ {x y} (f : edge x y) → E▵ (rx x) f ≡ emb f
      shrink▵ f i w a t b = emb f w (absorb▵ a i) t b

      emb-image-contr▵
        : ∀ {x y} (f : edge x y) → is-contr (fiber (emb {x} {y}) (emb f))
      emb-image-contr▵ {x} {y} f =
        subst (λ α → is-contr (fiber (emb {x} {y}) α))
              (shrink▵ f) (push-contr (rx x) f)
```

## The flanks

At the reflexive edge the two actions are the same expression — both
slots carry `rx` — so the two absorptions are paths in one type. Their
agreement is therefore stateable, and it is not a consequence of either
hand: `flank-pin` is a type here, uninhabited by design. This is the
cell the stability tier pins.

```agda

      flank▿ : ∀ {x} → emb (rx x) x (rx x) x (rx x) ≡ rx x
      flank▿ {x} = absorb▿ (rx x)

      flank▵ : ∀ {x} → emb (rx x) x (rx x) x (rx x) ≡ rx x
      flank▵ {x} = absorb▵ (rx x)

      flank-pin : ∀ {x} → Type e
      flank-pin {x} = flank▿ {x} ≡ flank▵ {x}
```

## Stability is one statement, not two

Readback evaluates at the identity context, which fills both slots at
once, so the two hands' readbacks are the same equation. It buys each
hand's unit laws.

```agda

    module stable (readback : ∀ {x y} (f : edge x y) → ev f ≡ f) where

      comp-eq▿ : ∀ {x y z} (f : edge x y) (g : edge y z) → f ⨾▿ g ≡ noy f z g
      comp-eq▿ {z = z} f g =
          sym (readback (f ⨾▿ g))
        ∙ noy-composite f g (rx z)
        ∙ ap (noy f z) (readback g)

      comp-eq▵ : ∀ {x y z} (f : edge x y) (g : edge y z) → f ⨾▵ g ≡ yon g x f
      comp-eq▵ {x = x} f g =
          sym (readback (f ⨾▵ g))
        ∙ yon-composite f g (rx x)
        ∙ ap (yon g x) (readback f)

      unitr▿ : ∀ {x y} (f : edge x y) → f ⨾▿ rx y ≡ f
      unitr▿ {y = y} f = comp-eq▿ f (rx y) ∙ readback f

      unitl▵ : ∀ {x y} (f : edge x y) → rx x ⨾▵ f ≡ f
      unitl▵ {x} f = comp-eq▵ (rx x) f ∙ readback f
```

## The path groupoid

The discrete graph on `A` with the two-sided path action. The ternary
embedding is `Core.Groupoid.Virtual`'s `repr.emb q w p z r =
pcom (sym p) q r`, and it is an *equivalence* — so here the
composability tier holds at every target, not only at the strings a
pair spans. The path groupoid is the degenerate instance where
representability is total rather than propositional.

```agda

module path-groupoid {u} (A : Type u) where

  G : reflexive-graph u u
  G .reflexive-graph.vtx      = A
  G .reflexive-graph.edge x y = x ≡ y
  G .reflexive-graph.rx x     = refl

  E : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  E = yon-unbiased.emb {A = λ _ → A}

  E-equiv : {x y : A} → is-equiv (E {x} {y})
  E-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  open reflexive-graph G using (rx)
  open vgraph G E

  pull-contr : ∀ {x y z : A} (f : x ≡ y) (g : y ≡ z)
             → is-contr (fiber (E {x} {z}) (E▿ f g))
  pull-contr f g = eqv-fibers E-equiv (E▿ f g)

  push-contr : ∀ {x y z : A} (f : x ≡ y) (g : y ≡ z)
             → is-contr (fiber (E {x} {z}) (E▵ f g))
  push-contr f g = eqv-fibers E-equiv (E▵ f g)

  open hands pull-contr push-contr
```

Both absorptions are already in `Core.Kan`, as the two idempotence
lemmas of the ternary composite — one per slot.

```agda

  noy-refl : ∀ {x t : A} (b : x ≡ t) → noy (rx x) t b ≡ b
  noy-refl b = pcom.ideml b

  yon-refl : ∀ {x w : A} (a : w ≡ x) → yon (rx x) w a ≡ a
  yon-refl a = pcom.idemr a

  pull-eqv : ∀ {x t : A} → is-equiv (noy (rx x) t)
  pull-eqv = iso→equiv _ (λ b → b) noy-refl noy-refl .snd

  push-eqv : ∀ {x w : A} → is-equiv (yon (rx x) w)
  push-eqv = iso→equiv _ (λ a → a) yon-refl yon-refl .snd
```

Each string collapses at the unit, and the idempotence is the
`fst`-shadow of the collapse read against the fiber's center.

```agda

  collapse▿ : ∀ {x : A} → E▿ (rx x) (rx x) ≡ E (rx x)
  collapse▿ i w a t b = E refl w a t (noy-refl b i)

  collapse▵ : ∀ {x : A} → E▵ (rx x) (rx x) ≡ E (rx x)
  collapse▵ i w a t b = E refl w (yon-refl a i) t b

  idem▿ : ∀ {x : A} → rx x ⨾▿ rx x ≡ rx x
  idem▿ {x} = ap fst (pull-contr (rx x) (rx x) .paths (rx x , sym collapse▿))

  idem▵ : ∀ {x : A} → rx x ⨾▵ rx x ≡ rx x
  idem▵ {x} = ap fst (push-contr (rx x) (rx x) .paths (rx x , sym collapse▵))

  open unital pull-eqv push-eqv idem▿ idem▵
```

Readback is `pcom.unit`: evaluating at the identity context is the
ternary composite with both flanks reflexive.

```agda

  readback : ∀ {x y : A} (f : x ≡ y) → ev f ≡ f
  readback f = pcom.unit f

  open stable readback
```

