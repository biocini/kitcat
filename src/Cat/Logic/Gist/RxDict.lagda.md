Spike: what is a deductive system's data, read in reflexive-graph
terms?

Three questions, each answered by conversion alone.

Does `Cat.Logic.Type`'s sequent vocabulary — terms, coterms, the two
axiom halves — already name structure that `Cat.Graph.Refl` has names
for? Do the two actions a virtual graph generates assemble into the
transport data of the two lens variances? And is the composability
tier, stated as contractibility of a representability fiber, the same
condition as a fibration of a displayed reflexive graph?

Every proof below is `refl`, so each answer is a definitional equality
rather than an equivalence: the two languages describe one object, and
a construction may be read in whichever is convenient.

The naming keeps the two registers apart. A *hand* is named for the
slot its second factor enters — `⁻` the coterm slot, `⁺` the term slot
— and `act`/`coact` name the two actions and nothing else. The
registers cross: the `⁻` hand is the one whose coslice is a
*covariant* fibration, so a hand named for its action would be wired
against the variance it exhibits.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.RxDict where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Path.Base

open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base
-- The carrier, inlined: a spike in an in-development layer carries its
-- own copy of the data it probes, so a change to the layer cannot
-- silently retune it.

record virtual-graph o h : Type₊ (o ⊔ h) where
  field
    ob : Type o
    hom : ob → ob → Type h
    idn : (x : ob) → hom x x

  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v

  argument : ob → ob → Type (o ⊔ h)
  argument x y = term x × coterm y

  var : (a : ob) → term a
  var a = a , idn a

  covar : (y : ob) → coterm y
  covar y = y , idn y

  conclusion : ∀ {x y} → argument x y → Type h
  conclusion γ = hom (γ .fst .fst) (γ .snd .fst)

  judgment : ob → ob → Type (o ⊔ h)
  judgment x y = (γ : argument x y) → conclusion γ

  field
    reflect : ∀ {x y} → hom x y → judgment x y

module sequents {o h} (G : virtual-graph o h) where
  open virtual-graph G

  argue : ∀ {x y} → term x → coterm y → argument x y
  argue h k = h , k

  intro : ∀ {x y} → hom x y → term y
  intro {x} f = x , f

  elim : ∀ {x y} → hom x y → coterm x
  elim {y = y} f = y , f

  eval : ∀ {x y} → judgment x y → hom x y
  eval {x} {y} α = α (var x , covar y)

  is-representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  is-representable = fiber reflect

  normal : ∀ {x y} (f : hom x y) → is-representable (reflect f)
  normal f = f , refl
```

The opposite virtual graph reverses the edges and reads `reflect`
against the swapped argument. It is the generator of every mirror
statement below: one hand is written, the other is that text at `opⱽ`.

```agda
opⱽ : ∀ {o h} → virtual-graph o h → virtual-graph o h
opⱽ G .virtual-graph.ob          = virtual-graph.ob G
opⱽ G .virtual-graph.hom x y     = virtual-graph.hom G y x
opⱽ G .virtual-graph.idn         = virtual-graph.idn G
opⱽ G .virtual-graph.reflect f γ = virtual-graph.reflect G f (γ .snd , γ .fst)

module logic {o h} (G : virtual-graph o h) where
  open virtual-graph G public
  open sequents G public

  graph : reflexive-graph o h
  graph .reflexive-graph.vtx  = ob
  graph .reflexive-graph.edge = hom
  graph .reflexive-graph.rx   = idn
```

## The dictionary

A term at `x` is the type of edges *into* `x` paired with their
anonymous source — the cofan of `x`. A coterm at `y` is the fan. The
two axiom halves are the centers reflexivity provides, so `var` and
`covar` are not new data.

```agda
  term-is-cofan  : ∀ x → term x ≡ rx.cofan graph x
  term-is-cofan  _ = refl

  coterm-is-fan  : ∀ y → coterm y ≡ rx.fan graph y
  coterm-is-fan  _ = refl

  var-is-center   : ∀ x → var x ≡ rx.cofan-center graph x
  var-is-center   _ = refl

  covar-is-center : ∀ y → covar y ≡ rx.fan-center graph y
  covar-is-center _ = refl
```

Opposition exchanges the two families, so the term/coterm distinction
is the fan/cofan distinction and carries no further content.

```agda
  term-op   : ∀ x → rx.fan (rx.op graph) x ≡ term x
  term-op   _ = refl

  coterm-op : ∀ y → rx.cofan (rx.op graph) y ≡ coterm y
  coterm-op _ = refl
```

## The two actions

Reflecting an edge and holding one slot at its axiom half leaves a
transport of the other family: forward on terms, backward on coterms.
Each acts fiberwise over the anonymous endpoint, which is what lets
the composite judgments below be stated without transport.

```agda
  act : ∀ {x y} → hom x y → term x → term y
  act {y = y} f t = intro (reflect f (argue t (covar y)))

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact {x} f e = elim (reflect f (argue (var x) e))

  act-fiberwise : ∀ {x y} (f : hom x y) (t : term x) → act f t .fst ≡ t .fst
  act-fiberwise _ _ = refl

  coact-fiberwise : ∀ {x y} (f : hom x y) (e : coterm y) → coact f e .fst ≡ e .fst
  coact-fiberwise _ _ = refl
```

At its own axiom half each action returns the evaluation of the
reflected edge. Readback — that this evaluation is the edge again — is
therefore the single statement that both actions are the identity
there, which is the one place the two hands meet.

```agda
  act-axiom : ∀ {x y} (f : hom x y) → act f (var x) ≡ (x , eval (reflect f))
  act-axiom _ = refl

  coact-axiom : ∀ {x y} (f : hom x y) → coact f (covar y) ≡ (y , eval (reflect f))
  coact-axiom _ = refl
```

## The two composite judgments

One factor stays reflected as the head; the other acts on its slot.

```agda
  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (argue (γ .fst) (coact g (γ .snd)))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect g (argue (act f (γ .fst)) (γ .snd))
```

## The `⁻` hand

Composition is the center of the representability fiber over the
composite judgment, and the center's path is the head-rewriting
witness everything downstream consumes.

```agda
  module hand⁻
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable (composite⁻ f g)))
    where

    _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾ g = contr⁻ f g .center .fst

    reflect-⨾ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → reflect (f ⨾ g) ≡ composite⁻ f g
    reflect-⨾ f g = contr⁻ f g .center .snd
```

The coslice at `a` carries the edges out of `a`, with a displayed edge
over `p` recording that its target is a composite. Its displayed
reflexivity is the flank absorption, so the family is a displayed
reflexive graph from the unit tier onward; the composability condition
itself speaks only of vertices and edges and needs no reflexivity to
be stated.

Against that display, this hand's composability *is* the covariant
fibration condition, its pushforward *is* the composition, and its
lift *is* the head-rewriting witness.

```agda
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
```

## The `⁺` hand

The mirror, stated directly for legibility: the slice at a fixed
target, with the other flank absorption, is a contravariant fibration
whose pullback is this hand's composition.

```agda
  module hand⁺
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable (composite⁺ f g)))
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

The opposite graph of the logic is the opposite of its graph, and
opposition is involutive on the nose, so instantiating at `opⱽ` is a
bijection on virtual graphs rather than a passage to a quotient.

```agda
module _ {o h} (G : virtual-graph o h) where
  private
    module L  = logic G
    module Lᵒ = logic (opⱽ G)

  graph-op : Lᵒ.graph ≡ rx.op L.graph
  graph-op = refl

  op-invol : opⱽ (opⱽ G) ≡ G
  op-invol = refl
```

The two actions exchange on elements: what the opposite calls pushing
a term is what the base calls pulling a coterm.

```agda
  act-op : ∀ {x y} (f : L.hom y x) (t : L.coterm x) → Lᵒ.act f t ≡ L.coact f t
  act-op _ _ = refl

  coact-op : ∀ {x y} (f : L.hom y x) (t : L.term y) → Lᵒ.coact f t ≡ L.act f t
  coact-op _ _ = refl
```

Judgments exchange only against the swap of the argument pair. The
swap is its own inverse definitionally, and both `reflect` and the
composite judgments commute with it — at the level of functions, not
merely pointwise — so the exchange carries no coherence data.

What it is not is a coincidence of types: `Lᵒ.judgment x z` has
domain `coterm x × term z` where `L.judgment z x` has `term z ×
coterm x`. A tier statement therefore transfers along `swap-judgment`
by one `ap`, never by conversion, which is the reason both hands'
definitions are written out above and only their theorems travel.

```agda
  swap-arg  : ∀ {x z} → Lᵒ.argument x z → L.argument z x
  swap-arg  γ = γ .snd , γ .fst

  swap-arg⁻ : ∀ {x z} → L.argument z x → Lᵒ.argument x z
  swap-arg⁻ δ = δ .snd , δ .fst

  swap-judgment : ∀ {x z} → L.judgment z x → Lᵒ.judgment x z
  swap-judgment α γ = α (swap-arg γ)

  swap-invol : ∀ {x z} (γ : Lᵒ.argument x z) → swap-arg⁻ (swap-arg γ) ≡ γ
  swap-invol _ = refl

  reflect-op : ∀ {x z} (f : L.hom z x) → Lᵒ.reflect f ≡ swap-judgment (L.reflect f)
  reflect-op _ = refl

  composite-op : ∀ {x y z} (f : L.hom y x) (g : L.hom z y)
               → Lᵒ.composite⁻ f g ≡ swap-judgment (L.composite⁺ g f)
  composite-op _ _ = refl
```

## What this does not establish

The base graph of a deductive system is not univalent: `rx.is-univalent
graph` asks every coterm type to be a proposition, which holds in the
path-object regime and fails wherever an object carries distinct
outgoing edges. The lens-structure uniqueness results and the
classifying certificates hypothesise it, so they do not reach the
tiers above; the vocabulary, the displayed and fibration operations,
and the total-opposite duality do.

The displays above take their displayed edges in the judgments. Taking
the fibers discrete instead would make a lens unitor the `⨾`-unit law
rather than the flank absorption — a stability-tier fact, untested
here, and the reason the judgment-valued display is the one built.
