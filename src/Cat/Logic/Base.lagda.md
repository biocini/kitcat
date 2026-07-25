The axioms of a deductive system, on the vocabulary a virtual graph
already carries.

An argument has two slots. Reflecting an edge and holding one of them
at its axiom half leaves an action on the other; leaving a slot
packaged instead and letting the head stay a judgment leaves an
injection. Every operation below is one of those two moves, and is
therefore available on a bare virtual graph.

The axioms are three predicates over that vocabulary, each asserting
that some fiber is contractible. Nothing the theory computes with is
declared: the two compositions, the two units and the readback family
are projected from those fibers, which is what keeps every tier a
proposition and being a deductive system a property rather than
structure.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Path.Base
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.J using (J)
open import Core.Transport.Properties using (is-contr-is-prop)

open import Cat.Logic.Type
```

## The opposite

Edges reverse and `reflect` is read against the swapped argument. The
operation is definitionally involutive, and it exchanges every `⁻`
with its `⁺`, so each hand's text is the other's at `opⱽ`.

```agda
opⱽ : ∀ {o h} → virtual-graph o h → virtual-graph o h
opⱽ G .virtual-graph.ob          = virtual-graph.ob G
opⱽ G .virtual-graph.hom x y     = virtual-graph.hom G y x
opⱽ G .virtual-graph.idn         = virtual-graph.idn G
opⱽ G .virtual-graph.reflect f γ = virtual-graph.reflect G f (γ .snd , γ .fst)

opⱽ-invol : ∀ {o h} (G : virtual-graph o h) → opⱽ (opⱽ G) ≡ G
opⱽ-invol _ = refl

module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G
```

## The two actions

Holding one slot at its axiom half leaves the edge-valued form, whose
value's far endpoint is read off the argument. The family transports
are these bundled, so each preserves the anonymous endpoint by `refl`.

```agda
  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (argue (var x) γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (argue t (covar y))

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact {x} f e = elim (reflect f (argue (var x) e))

  act : ∀ {x y} → hom x y → term x → term y
  act {y = y} f t = intro (reflect f (argue t (covar y)))
```

## The two injections

Leaving the head a judgment and letting an edge absorb into one slot.
A *hand* is named for the slot that edge enters: `⁻` the coterm slot,
`⁺` the term slot. The composite judgments are these at a reflected
head.

```agda
  inj⁻ : ∀ {x y z} → judgment x y → hom y z → judgment x z
  inj⁻ α p γ = α (argue (γ .fst) (coact p (γ .snd)))

  inj⁺ : ∀ {x y z} → hom x y → judgment y z → judgment x z
  inj⁺ p β γ = β (argue (act p (γ .fst)) (γ .snd))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g = inj⁻ (reflect f) g

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g = inj⁺ f (reflect g)
```

## Composability

Both hands in one record. Each composition is the center of the
representability fiber over that hand's composite judgment, and the
center's path is the head-rewriting witness everything downstream
consumes.

```agda
  record is-composable : Type (o ⊔ h) where
    field
      contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
                 → is-contr (is-representable (composite⁻ f g))
      contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
                 → is-contr (is-representable (composite⁺ f g))

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
```

Each action distributes over its own hand's composition, and the
head-rewriting witness is the whole proof: the anonymous endpoint is
handed back untouched, so the identification is that witness read at
one argument.

```agda
    act-⨾⁺ : ∀ {x y z} (p : hom x y) (q : hom y z) (t : term x)
           → act (p ⨾⁺ q) t ≡ act q (act p t)
    act-⨾⁺ {z = z} p q t i = t .fst , reflect-⨾⁺ p q i (argue t (covar z))

    coact-⨾⁻ : ∀ {x y z} (p : hom x y) (q : hom y z) (e : coterm z)
             → coact (p ⨾⁻ q) e ≡ coact p (coact q e)
    coact-⨾⁻ {x} p q e i = e .fst , reflect-⨾⁻ p q i (argue (var x) e)
```

## Unitality

Both hands in one record: per hand, the fiber of that hand's action
map over the identity action. Neither field mentions `idn`, and the
unit each projects absorbs everything.

```agda
  record is-unital : Type (o ⊔ h) where
    field
      unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
      unit-fiber⁺ : ∀ x → is-contr (fiber (act-π   {x} {x}) snd)

    unit⁻ unit⁺ : ∀ x → hom x x
    unit⁻ x = unit-fiber⁻ x .center .fst
    unit⁺ x = unit-fiber⁺ x .center .fst

    unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
    unit⁻-absorb x γ i = unit-fiber⁻ x .center .snd i γ

    unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
    unit⁺-absorb x t i = unit-fiber⁺ x .center .snd i t
```

A candidate unit is an edge together with a proof that its action is
the identity action — an element of the very fiber the tier contracts.
Contractibility is therefore uniqueness, and the identification carries
the witness as well as the element.

```agda
    unit⁻-unique-σ : ∀ x (e : hom x x) (p : coact-π e ≡ snd)
                   → (e , p) ≡ unit-fiber⁻ x .center
    unit⁻-unique-σ x e p = sym (unit-fiber⁻ x .paths (e , p))

    unit⁺-unique-σ : ∀ x (e : hom x x) (p : act-π e ≡ snd)
                   → (e , p) ≡ unit-fiber⁺ x .center
    unit⁺-unique-σ x e p = sym (unit-fiber⁺ x .paths (e , p))

    unit⁻-unique : ∀ x (e : hom x x) → coact-π e ≡ snd → e ≡ unit⁻ x
    unit⁻-unique x e p = ap fst (unit⁻-unique-σ x e p)

    unit⁺-unique : ∀ x (e : hom x x) → act-π e ≡ snd → e ≡ unit⁺ x
    unit⁺-unique x e p = ap fst (unit⁺-unique-σ x e p)

    unit⁻-unique-pt : ∀ x (e : hom x x)
                    → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ unit⁻ x
    unit⁻-unique-pt x e abs = unit⁻-unique x e (funext abs)

    unit⁺-unique-pt : ∀ x (e : hom x x)
                    → (∀ t → act-π e t ≡ t .snd) → e ≡ unit⁺ x
    unit⁺-unique-pt x e abs = unit⁺-unique x e (funext abs)
```

## Stability

Readback bare is a torsor, so the tier is the contractible fiber over
the coherence that pins it at the flanks. Each flank canonical reads
one value of the family — that hand's projected unit — and transports
its absorption onto the chosen edge.

```agda
  readback : Type (o ⊔ h)
  readback = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f

  module _ (U : is-unital) where
    open is-unital U

    flank⁻-of : ∀ x → eval (reflect (unit⁻ x)) ≡ unit⁻ x
              → eval (reflect (idn x)) ≡ idn x
    flank⁻-of x p =
      ap (λ e → coact-π e (covar x)) (sym (sym p ∙ unit⁻-absorb x (covar x)))
      ∙ unit⁻-absorb x (covar x)

    flank⁺-of : ∀ x → eval (reflect (unit⁺ x)) ≡ unit⁺ x
              → eval (reflect (idn x)) ≡ idn x
    flank⁺-of x p =
      ap (λ e → act-π e (var x)) (sym (sym p ∙ unit⁺-absorb x (var x)))
      ∙ unit⁺-absorb x (var x)

    absorb-coh : readback → Type (o ⊔ h)
    absorb-coh u =
      ∀ x → (u (idn x) ≡ flank⁻-of x (u (unit⁻ x)))
          × (u (idn x) ≡ flank⁺-of x (u (unit⁺ x)))

    is-stable : Type (o ⊔ h)
    is-stable = is-contr (Σ absorb-coh)
```

The readback family and the coherence are projections, and with them
the chosen edge is identified with each hand's unit — so the two hands'
units agree and the chosen edge inherits both absorptions.

```agda
  module stability (U : is-unital) (S : is-stable U) where
    open is-unital U

    unit : readback
    unit = S .center .fst

    coh : absorb-coh U unit
    coh = S .center .snd

    flanks-agree : ∀ x → flank⁻-of U x (unit (unit⁻ x))
                       ≡ flank⁺-of U x (unit (unit⁺ x))
    flanks-agree x = sym (coh x .fst) ∙ coh x .snd

    unit⁻-is-idn : ∀ x → unit⁻ x ≡ idn x
    unit⁻-is-idn x = sym (unit (unit⁻ x)) ∙ unit⁻-absorb x (covar x)

    unit⁺-is-idn : ∀ x → unit⁺ x ≡ idn x
    unit⁺-is-idn x = sym (unit (unit⁺ x)) ∙ unit⁺-absorb x (var x)

    units-agree : ∀ x → unit⁻ x ≡ unit⁺ x
    units-agree x = unit⁻-is-idn x ∙ sym (unit⁺-is-idn x)

    idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
    idn-absorb⁻ x γ =
      ap (λ e → coact-π e γ) (sym (unit⁻-is-idn x)) ∙ unit⁻-absorb x γ

    idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
    idn-absorb⁺ x t =
      ap (λ e → act-π e t) (sym (unit⁺-is-idn x)) ∙ unit⁺-absorb x t

    coact-idn : ∀ {y} (e : coterm y) → coact (idn y) e ≡ e
    coact-idn {y} e i = e .fst , idn-absorb⁻ y e i

    act-idn : ∀ {x} (t : term x) → act (idn x) t ≡ t
    act-idn {x} t i = t .fst , idn-absorb⁺ x t i
```

Uniqueness against the chosen edge needs no unit tier: readback by
itself makes any edge acting as the identity equal to `idn`.

```agda
    unit⁻-canonical : ∀ x (e : hom x x)
                    → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ idn x
    unit⁻-canonical x e abs = sym (unit e) ∙ abs (covar x)

    unit⁺-canonical : ∀ x (e : hom x x)
                    → (∀ t → act-π e t ≡ t .snd) → e ≡ idn x
    unit⁺-canonical x e abs = sym (unit e) ∙ abs (var x)
```

There are then two routes from a candidate to the chosen edge — via
the projected unit, or directly through readback — and they agree.
Both are instances of one dependent function on the fiber, so they are
natural in paths between fiber elements, which path induction supplies.

```agda
    route⁻ : ∀ x (c : fiber (coact-π {x} {x}) snd) → c .fst ≡ idn x
    route⁻ x c = sym (unit (c .fst)) ∙ (λ i → c .snd i (covar x))

    route⁺ : ∀ x (c : fiber (act-π {x} {x}) snd) → c .fst ≡ idn x
    route⁺ x c = sym (unit (c .fst)) ∙ (λ i → c .snd i (var x))

    route⁻-natural
      : ∀ x (c₀ c₁ : fiber (coact-π {x} {x}) snd) (γ : c₀ ≡ c₁)
      → route⁻ x c₀ ≡ ap fst γ ∙ route⁻ x c₁
    route⁻-natural x c₀ c₁ γ =
      J (λ c₁' γ' → route⁻ x c₀ ≡ ap fst γ' ∙ route⁻ x c₁')
        (sym (Path.unitl (route⁻ x c₀))) γ

    route⁺-natural
      : ∀ x (c₀ c₁ : fiber (act-π {x} {x}) snd) (γ : c₀ ≡ c₁)
      → route⁺ x c₀ ≡ ap fst γ ∙ route⁺ x c₁
    route⁺-natural x c₀ c₁ γ =
      J (λ c₁' γ' → route⁺ x c₀ ≡ ap fst γ' ∙ route⁺ x c₁')
        (sym (Path.unitl (route⁺ x c₀))) γ

    unique-agrees⁻
      : ∀ x (e : hom x x) (abs : ∀ γ → coact-π e γ ≡ γ .snd)
      → unit⁻-unique-pt x e abs ∙ unit⁻-is-idn x ≡ unit⁻-canonical x e abs
    unique-agrees⁻ x e abs =
      ap (sym (ap fst γ) ∙_) (route⁻-natural x (unit-fiber⁻ x .center) c γ)
      ∙ Path.assoc (sym (ap fst γ)) (ap fst γ) (route⁻ x c)
      ∙ ap (_∙ route⁻ x c) (Path.invl (ap fst γ))
      ∙ Path.unitl (route⁻ x c)
      where
        c : fiber (coact-π {x} {x}) snd
        c = e , funext abs

        γ : unit-fiber⁻ x .center ≡ c
        γ = unit-fiber⁻ x .paths c

    unique-agrees⁺
      : ∀ x (e : hom x x) (abs : ∀ t → act-π e t ≡ t .snd)
      → unit⁺-unique-pt x e abs ∙ unit⁺-is-idn x ≡ unit⁺-canonical x e abs
    unique-agrees⁺ x e abs =
      ap (sym (ap fst γ) ∙_) (route⁺-natural x (unit-fiber⁺ x .center) c γ)
      ∙ Path.assoc (sym (ap fst γ)) (ap fst γ) (route⁺ x c)
      ∙ ap (_∙ route⁺ x c) (Path.invl (ap fst γ))
      ∙ Path.unitl (route⁺ x c)
      where
        c : fiber (act-π {x} {x}) snd
        c = e , funext abs

        γ : unit-fiber⁺ x .center ≡ c
        γ = unit-fiber⁺ x .paths c
```

## The bundle

```agda
  record is-deductive-system : Type (o ⊔ h) where
    field
      composable : is-composable
      unital     : is-unital
      stable     : is-stable unital

    open is-composable composable public
    open is-unital unital public
    open stability unital stable public
```

Each hand absorbs the chosen edge into the slot its second factor
enters, and only there. The `⁻` hand therefore has a right unit law
and the `⁺` hand a left one; neither has the other's, which is what a
one-handed composition means.

```agda
    composite⁻-unitr : ∀ {a y} (u : hom a y) → reflect u ≡ composite⁻ u (idn y)
    composite⁻-unitr u = funext λ γ →
      ap (λ e → reflect u (argue (γ .fst) e)) (sym (coact-idn (γ .snd)))

    composite⁺-unitl : ∀ {x c} (u : hom x c) → reflect u ≡ composite⁺ (idn x) u
    composite⁺-unitl u = funext λ γ →
      ap (λ t → reflect u (argue t (γ .snd))) (sym (act-idn (γ .fst)))

    unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ idn y ≡ f
    unitr⁻ {y = y} f =
      sym (unit (f ⨾⁻ idn y))
      ∙ ap eval (reflect-⨾⁻ f (idn y) ∙ sym (composite⁻-unitr f))
      ∙ unit f

    unitl⁺ : ∀ {x y} (f : hom x y) → idn x ⨾⁺ f ≡ f
    unitl⁺ {x} f =
      sym (unit (idn x ⨾⁺ f))
      ∙ ap eval (reflect-⨾⁺ (idn x) f ∙ sym (composite⁺-unitl f))
      ∙ unit f
```

## Propositionality

Every field of every tier is a contractibility statement, and a
product of propositions is one. The bundle follows field by field, its
stability component over the path the unit component supplies.

```agda
  is-composable-is-prop : is-prop is-composable
  is-composable-is-prop C C' i .is-composable.contr⁻ f g =
    is-contr-is-prop _
      (is-composable.contr⁻ C f g) (is-composable.contr⁻ C' f g) i
  is-composable-is-prop C C' i .is-composable.contr⁺ f g =
    is-contr-is-prop _
      (is-composable.contr⁺ C f g) (is-composable.contr⁺ C' f g) i

  is-unital-is-prop : is-prop is-unital
  is-unital-is-prop U U' i .is-unital.unit-fiber⁻ x =
    is-contr-is-prop _ (is-unital.unit-fiber⁻ U x) (is-unital.unit-fiber⁻ U' x) i
  is-unital-is-prop U U' i .is-unital.unit-fiber⁺ x =
    is-contr-is-prop _ (is-unital.unit-fiber⁺ U x) (is-unital.unit-fiber⁺ U' x) i

  is-stable-is-prop : ∀ U → is-prop (is-stable U)
  is-stable-is-prop U = is-contr-is-prop _

  is-deductive-system-is-prop : is-prop is-deductive-system
  is-deductive-system-is-prop D D' i .is-deductive-system.composable =
    is-composable-is-prop
      (is-deductive-system.composable D) (is-deductive-system.composable D') i
  is-deductive-system-is-prop D D' i .is-deductive-system.unital =
    is-unital-is-prop
      (is-deductive-system.unital D) (is-deductive-system.unital D') i
  is-deductive-system-is-prop D D' i .is-deductive-system.stable =
    is-prop→PathP
      (λ i → is-stable-is-prop
        (is-unital-is-prop
          (is-deductive-system.unital D) (is-deductive-system.unital D') i))
      (is-deductive-system.stable D) (is-deductive-system.stable D') i
```

## The boundary

Two conditions the tiers do not assert, named so that what lies
outside the theory can be stated in its own vocabulary. *Interchange*
identifies the two composite judgments; a *mediation* identifies the
two compositions. The first delivers the second, by reflecting both
compositions onto one judgment and reading the result back.

```agda
  interchange : Type (o ⊔ h)
  interchange = ∀ {x y z} (f : hom x y) (g : hom y z)
              → composite⁻ f g ≡ composite⁺ f g

  module _ (D : is-deductive-system) where
    open is-deductive-system D

    mediation : Type (o ⊔ h)
    mediation = ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁻ g ≡ f ⨾⁺ g

    interchange→mediation : interchange → mediation
    interchange→mediation I f g =
      sym (unit (f ⨾⁻ g))
      ∙ ap eval (reflect-⨾⁻ f g ∙ I f g ∙ sym (reflect-⨾⁺ f g))
      ∙ unit (f ⨾⁺ g)
```
