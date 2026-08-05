The chosen-edge carrier: one family `idn` fills both argument
slots, and nothing aligns the reflection with it. A hand is named
for the slot its second factor enters — `⁻` the coterm slot, `⁺`
the term slot — so this dialect's `⁻` hand is `Framing`'s `⁺` hand
read at the diagonal `rx = corx = idn`, and dually; every
definition below is that diagonal instance, restated in its own
register. The engine is contractibility of `reflect`'s fiber over
its own image, from two tiers — composability and unitality — with
no readback, no interchange, and no embedding-condition hypothesis: each
hand's projected unit makes a reflected edge its own composite, so
the fiber is a composability fiber transported along one unit law.
The dictionary at the end reads the same carrier in
reflexive-graph terms, where every answer is definitional.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Engine where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding
  using (is-embedding; is-embedding→ap-equiv; ap-is-embedding)

open import Core.Rx.Type
open import Core.Rx.Base

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding using (is-representable; normal; opⱽ)
open import Bb.VirtualGraphs.Graph using (rxgraph; op-rxgraph)
```

## The vocabulary, axiom-free

```agda
module chosen {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  var : (a : ob) → term a
  var a = a , idn a

  covar : (y : ob) → coterm y
  covar y = y , idn y

  argue : ∀ {x y} → term x → coterm y → argument x y
  argue h k = h , k

  intro : ∀ {x y} → hom x y → term y
  intro {x} f = x , f

  elim : ∀ {x y} → hom x y → coterm x
  elim {y = y} f = y , f

  eval : ∀ {x y} → judgment x y → hom x y
  eval {x} {y} α = α (var x , covar y)

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (argue (var x) γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (argue t (covar y))

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact {x} f e = elim (reflect f (argue (var x) e))

  act : ∀ {x y} → hom x y → term x → term y
  act {y = y} f t = intro (reflect f (argue t (covar y)))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (argue (γ .fst) (coact g (γ .snd)))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect g (argue (act f (γ .fst)) (γ .snd))
```

## Composability, and the distributive laws

Each action distributes over its own hand's composition. Stated at
the edge level the anonymous endpoint is a parameter rather than a
component, so the two forms below are the same witness read at one
argument and then bundled.

```agda
  module composable
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable G (composite⁻ f g)))
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable G (composite⁺ f g)))
    where

    _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾⁻ g = contr⁻ f g .center .fst

    _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾⁺ g = contr⁺ f g .center .fst

    reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → reflect (f ⨾⁻ g) ≡ composite⁻ f g
    reflect-⨾⁻ f g = contr⁻ f g .center .snd

    reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → reflect (f ⨾⁺ g) ≡ composite⁺ f g
    reflect-⨾⁺ f g = contr⁺ f g .center .snd

    coact-π-⨾⁻ : ∀ {x y z} (p : hom x y) (q : hom y z) (e : coterm z)
               → coact-π (p ⨾⁻ q) e ≡ coact-π p (coact q e)
    coact-π-⨾⁻ {x} p q e i = reflect-⨾⁻ p q i (argue (var x) e)

    act-π-⨾⁺ : ∀ {x y z} (p : hom x y) (q : hom y z) (t : term x)
             → act-π (p ⨾⁺ q) t ≡ act-π q (act p t)
    act-π-⨾⁺ {z = z} p q t i = reflect-⨾⁺ p q i (argue t (covar z))

    coact-⨾⁻ : ∀ {x y z} (p : hom x y) (q : hom y z) (e : coterm z)
             → coact (p ⨾⁻ q) e ≡ coact p (coact q e)
    coact-⨾⁻ p q e i = e .fst , coact-π-⨾⁻ p q e i

    act-⨾⁺ : ∀ {x y z} (p : hom x y) (q : hom y z) (t : term x)
           → act (p ⨾⁺ q) t ≡ act q (act p t)
    act-⨾⁺ p q t i = t .fst , act-π-⨾⁺ p q t i
```

## The engine

The chosen edge plays no part below. Everything runs on the unit
tier's own projected units — the tier's fiber centre is an edge
whose action is the identity action, which is the only property the
argument uses. `idn` is needed to state the vocabulary, and no
result here asks it to be a unit.

```agda
    module engine
      (unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd))
      (unit-fiber⁺ : ∀ x → is-contr (fiber (act-π   {x} {x}) snd))
      where

      unit⁻ unit⁺ : ∀ x → hom x x
      unit⁻ x = unit-fiber⁻ x .center .fst
      unit⁺ x = unit-fiber⁺ x .center .fst

      unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
      unit⁻-absorb x γ i = unit-fiber⁻ x .center .snd i γ

      unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
      unit⁺-absorb x t i = unit-fiber⁺ x .center .snd i t

      unit⁻-unique : ∀ x (e : hom x x)
                   → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ unit⁻ x
      unit⁻-unique x e abs = ap fst (sym (unit-fiber⁻ x .paths (e , funext abs)))

      unit⁺-unique : ∀ x (e : hom x x)
                   → (∀ t → act-π e t ≡ t .snd) → e ≡ unit⁺ x
      unit⁺-unique x e abs = ap fst (sym (unit-fiber⁺ x .paths (e , funext abs)))

      coact-unit : ∀ {y} (e : coterm y) → coact (unit⁻ y) e ≡ e
      coact-unit {y} e i = e .fst , unit⁻-absorb y e i

      act-unit : ∀ {x} (t : term x) → act (unit⁺ x) t ≡ t
      act-unit {x} t i = t .fst , unit⁺-absorb x t i

      composite⁻-unitr : ∀ {a y} (u : hom a y) → reflect u ≡ composite⁻ u (unit⁻ y)
      composite⁻-unitr u i γ = reflect u (argue (γ .fst) (coact-unit (γ .snd) (~ i)))

      composite⁺-unitl : ∀ {x c} (u : hom x c) → reflect u ≡ composite⁺ (unit⁺ x) u
      composite⁺-unitl u i γ = reflect u (argue (act-unit (γ .fst) (~ i)) (γ .snd))
```

A reflected edge is its own hand's composite with the projected
unit, so the composability fiber over that composite is the fiber
over the reflection: each hand delivers the same contractibility,
and with it left-cancellability, embedding-hood, and the iterated
`ap`-equivalence.

```agda
      reflect-fiber-contr⁻
        : ∀ {x y} (f : hom x y) → is-contr (is-representable G (reflect f))
      reflect-fiber-contr⁻ {y = y} f =
        subst (λ α → is-contr (is-representable G α))
              (sym (composite⁻-unitr f)) (contr⁻ f (unit⁻ y))

      reflect-fiber-contr⁺
        : ∀ {x y} (f : hom x y) → is-contr (is-representable G (reflect f))
      reflect-fiber-contr⁺ {x} f =
        subst (λ α → is-contr (is-representable G α))
              (sym (composite⁺-unitl f)) (contr⁺ (unit⁺ x) f)

      reflect-lc : ∀ {x y} {f g : hom x y} → reflect f ≡ reflect g → f ≡ g
      reflect-lc {y = y} {f} {g} p =
        ap fst (sym (c .paths (f , p)) ∙ c .paths (normal G g))
        where c = reflect-fiber-contr⁻ g

      reflect-embedding : ∀ {x y} → is-embedding (reflect {x} {y})
      reflect-embedding α c@(f , p) =
        subst (λ β → is-prop (is-representable G β)) p
              (is-contr→is-prop (reflect-fiber-contr⁻ f)) c

      ap-reflect-equiv
        : ∀ {x y} {f g : hom x y} → is-equiv (ap (reflect {x} {y}) {f} {g})
      ap-reflect-equiv = is-embedding→ap-equiv reflect-embedding

      ap-reflect-embedding
        : ∀ {x y} {f g : hom x y} → is-embedding (ap (reflect {x} {y}) {f} {g})
      ap-reflect-embedding = ap-is-embedding reflect-embedding
```

Associativity and the unit laws come per hand: both bracketings
represent one judgment, by the outer head's rewriting followed by
that hand's distributive law, and left-cancellation descends the
identity from judgments to edges. Readback is not among the inputs.

```agda
      composite⁻-assoc
        : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → composite⁻ (f ⨾⁻ g) h ≡ composite⁻ f (g ⨾⁻ h)
      composite⁻-assoc f g h = funext λ γ →
        (λ i → reflect-⨾⁻ f g i (argue (γ .fst) (coact h (γ .snd))))
        ∙ (λ i → reflect f (argue (γ .fst) (coact-⨾⁻ g h (γ .snd) (~ i))))

      assoc⁻ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
             → (f ⨾⁻ g) ⨾⁻ h ≡ f ⨾⁻ (g ⨾⁻ h)
      assoc⁻ f g h = reflect-lc
        ( reflect-⨾⁻ (f ⨾⁻ g) h
        ∙ composite⁻-assoc f g h
        ∙ sym (reflect-⨾⁻ f (g ⨾⁻ h)) )

      composite⁺-assoc
        : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → composite⁺ f (g ⨾⁺ h) ≡ composite⁺ (f ⨾⁺ g) h
      composite⁺-assoc f g h = funext λ γ →
        (λ i → reflect-⨾⁺ g h i (argue (act f (γ .fst)) (γ .snd)))
        ∙ (λ i → reflect h (argue (act-⨾⁺ f g (γ .fst) (~ i)) (γ .snd)))

      assoc⁺ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
             → f ⨾⁺ (g ⨾⁺ h) ≡ (f ⨾⁺ g) ⨾⁺ h
      assoc⁺ f g h = reflect-lc
        ( reflect-⨾⁺ f (g ⨾⁺ h)
        ∙ composite⁺-assoc f g h
        ∙ sym (reflect-⨾⁺ (f ⨾⁺ g) h) )

      unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ unit⁻ y ≡ f
      unitr⁻ {y = y} f =
        reflect-lc (reflect-⨾⁻ f (unit⁻ y) ∙ sym (composite⁻-unitr f))

      unitl⁺ : ∀ {x y} (f : hom x y) → unit⁺ x ⨾⁺ f ≡ f
      unitl⁺ {x} f =
        reflect-lc (reflect-⨾⁺ (unit⁺ x) f ∙ sym (composite⁺-unitl f))
```

## The reflexive-graph dictionary

The chosen edge is a reflexivity datum: a term at `x` is the cofan
of `x`, a coterm the fan, and the two axiom halves are the centres
reflexivity provides. Every proof is `refl`, so each answer is a
definitional equality: the two languages describe one object.

```agda
module dict {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  open chosen G idn

  graph : reflexive-graph o h
  graph = rxgraph G idn

  term-is-cofan  : ∀ x → term x ≡ rx.cofan graph x
  term-is-cofan  _ = refl

  coterm-is-fan  : ∀ y → coterm y ≡ rx.fan graph y
  coterm-is-fan  _ = refl

  var-is-center   : ∀ x → var x ≡ rx.cofan-center graph x
  var-is-center   _ = refl

  covar-is-center : ∀ y → covar y ≡ rx.fan-center graph y
  covar-is-center _ = refl

  term-op   : ∀ x → rx.fan (rx.op graph) x ≡ term x
  term-op   _ = refl

  coterm-op : ∀ y → rx.cofan (rx.op graph) y ≡ coterm y
  coterm-op _ = refl
```

Each action acts fiberwise over the anonymous endpoint, and at its
own axiom half returns the evaluation of the reflected edge —
readback is the single statement that both actions are the identity
there, the one place the two hands meet.

```agda
  act-fiberwise : ∀ {x y} (f : hom x y) (t : term x) → act f t .fst ≡ t .fst
  act-fiberwise _ _ = refl

  coact-fiberwise : ∀ {x y} (f : hom x y) (e : coterm y) → coact f e .fst ≡ e .fst
  coact-fiberwise _ _ = refl

  act-axiom : ∀ {x y} (f : hom x y) → act f (var x) ≡ (x , eval (reflect f))
  act-axiom _ = refl

  coact-axiom : ∀ {x y} (f : hom x y) → coact f (covar y) ≡ (y , eval (reflect f))
  coact-axiom _ = refl
```

The coslice at `a` carries the edges out of `a`, with a displayed
edge over `p` recording that its target is a composite; displayed
reflexivity is the flank absorption. Against that display the `⁻`
hand's composability is the covariant fibration condition, its
pushforward the composition, and its lift the head-rewriting
witness. The `⁺` hand is the mirror: the slice at a fixed target is
a contravariant fibration whose pullback is the composition.

```agda
  module hand⁻
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁻ f g)))
    where

    _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾ g = contr⁻ f g .center .fst

    reflect-⨾ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → reflect (f ⨾ g) ≡ composite⁻ f g
    reflect-⨾ f g = contr⁻ f g .center .snd

    module unital
      (absorb⁻ : ∀ {x y} (f : hom x y) → reflect f ≡ composite⁻ f (idn y))
      where

      coslice : ob → rx.disp graph h (o ⊔ h)
      coslice a .reflexive-graphᴰ.vtx z          = hom a z
      coslice a .reflexive-graphᴰ.edge y z p u w = reflect w ≡ composite⁻ u p
      coslice a .reflexive-graphᴰ.rx u           = absorb⁻ u

      coslice-fibration : ∀ a → rx.is-cov-fibration graph (coslice a)
      coslice-fibration _ _ _ p u = contr⁻ u p

      module F (a : ob) = rx.cov-fibration graph (coslice a) (coslice-fibration a)

      push-is-comp : ∀ a y z (p : hom y z) (u : hom a y) → F.push a y z p u ≡ u ⨾ p
      push-is-comp _ _ _ _ _ = refl

      lift-is-witness : ∀ a y z (p : hom y z) (u : hom a y)
                      → F.lift a y z p u ≡ reflect-⨾ u p
      lift-is-witness _ _ _ _ _ = refl

  module hand⁺
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁺ f g)))
    (absorb⁺ : ∀ {x y} (f : hom x y) → reflect f ≡ composite⁺ (idn x) f)
    where

    _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾ g = contr⁺ f g .center .fst

    slice : ob → rx.disp graph h (o ⊔ h)
    slice c .reflexive-graphᴰ.vtx x          = hom x c
    slice c .reflexive-graphᴰ.edge x y p u w = reflect u ≡ composite⁺ p w
    slice c .reflexive-graphᴰ.rx u           = absorb⁺ u

    slice-fibration : ∀ c → rx.is-ctrv-fibration graph (slice c)
    slice-fibration _ _ _ p w = contr⁺ p w

    module F (c : ob) = rx.ctrv-fibration graph (slice c) (slice-fibration c)

    pull-is-comp : ∀ c x y (p : hom x y) (w : hom y c) → F.pull c x y p w ≡ p ⨾ w
    pull-is-comp _ _ _ _ _ = refl
```

## The involution

The opposite graph of the dictionary is the opposite of its graph
(`op-rxgraph`), and opposition is involutive on the nose. The two
actions exchange on elements; judgments exchange only against the
swap of the argument pair, which is its own inverse definitionally,
and both `reflect` and the composite judgments commute with it at
the level of functions — so the exchange carries no coherence data,
and a tier statement transfers along `swap-judgment` by one `ap`.

```agda
module _ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  private
    module L  = chosen G idn
    module Lᵒ = chosen (opⱽ G) idn

  act-op : ∀ {x y} (f : hom y x) (t : coterm x) → Lᵒ.act f t ≡ L.coact f t
  act-op _ _ = refl

  coact-op : ∀ {x y} (f : hom y x) (t : term y) → Lᵒ.coact f t ≡ L.act f t
  coact-op _ _ = refl

  swap-arg  : ∀ {x z} → virtual-graph.argument (opⱽ G) x z → argument z x
  swap-arg  γ = γ .snd , γ .fst

  swap-arg⁻ : ∀ {x z} → argument z x → virtual-graph.argument (opⱽ G) x z
  swap-arg⁻ δ = δ .snd , δ .fst

  swap-judgment : ∀ {x z} → judgment z x → virtual-graph.judgment (opⱽ G) x z
  swap-judgment α γ = α (swap-arg γ)

  swap-invol : ∀ {x z} (γ : virtual-graph.argument (opⱽ G) x z)
             → swap-arg⁻ (swap-arg γ) ≡ γ
  swap-invol _ = refl

  reflect-op : ∀ {x z} (f : hom z x)
             → virtual-graph.reflect (opⱽ G) f ≡ swap-judgment (reflect f)
  reflect-op _ = refl

  composite-op : ∀ {x y z} (f : hom y x) (g : hom z y)
               → Lᵒ.composite⁻ f g ≡ swap-judgment (L.composite⁺ g f)
  composite-op _ _ = refl
```
