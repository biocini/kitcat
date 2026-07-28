Spike: what is `reflect`'s fiber over its own image, and what does it
buy?

`Bb.WeakDeductiveSystem.Type` supplies the point
`normal f : is-representable
(reflect f)` and says nothing about the rest of that fiber. If it is
contractible then `reflect` is left-cancellable, and every identity
between composites reduces to an identity between the judgments they
represent. That is the mechanism `composability.md` describes for
associativity; this spike inhabits it.

Two questions. What data does the fiber's contractibility need — and
in particular, does it need readback? And what is the shortest route to
the flank absorptions the engine runs on: through readback, or through
each hand's own action being an equivalence at the reflexive edge?

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.WeakDeductiveSystem.Gist.ReflectFiber where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding
  using (is-embedding; is-embedding→ap-equiv; ap-is-embedding)
open import Core.Kan using (is-contr→is-prop)

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

## The vocabulary, axiom-free

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G

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

Each action distributes over its own hand's composition. Stated at the
edge level the anonymous endpoint is a parameter rather than a
component, so the two forms below are the same witness read at one
argument and then bundled.

```agda
  module composable
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable (composite⁻ f g)))
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable (composite⁺ f g)))
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

The chosen edge plays no part. Everything below runs on the unit tier's
own projected units — the tier's fiber centre is an edge whose action
is the identity action, which is the only property the argument uses.

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

A reflected edge is its own hand's composite with the chosen edge, so
the composability fiber over that composite *is* the fiber over the
reflection. Each hand delivers the same contractibility.

```agda
      reflect-fiber-contr⁻
        : ∀ {x y} (f : hom x y) → is-contr (is-representable (reflect f))
      reflect-fiber-contr⁻ {y = y} f =
        subst (λ α → is-contr (is-representable α))
              (sym (composite⁻-unitr f)) (contr⁻ f (unit⁻ y))

      reflect-fiber-contr⁺
        : ∀ {x y} (f : hom x y) → is-contr (is-representable (reflect f))
      reflect-fiber-contr⁺ {x} f =
        subst (λ α → is-contr (is-representable α))
              (sym (composite⁺-unitl f)) (contr⁺ (unit⁺ x) f)
```

Contractibility of that fiber is left-cancellability of `reflect`: two
edges with the same reflection are the same edge, and the normal point
is one of the two elements being contracted.

```agda
      reflect-lc : ∀ {x y} {f g : hom x y} → reflect f ≡ reflect g → f ≡ g
      reflect-lc {y = y} {f} {g} p =
        ap fst (sym (c .paths (f , p)) ∙ c .paths (normal g))
        where c = reflect-fiber-contr⁻ g
```

Prop-fibers over the image is embedding-hood outright, and an
embedding makes `ap` an equivalence — which iterates, since `ap` of an
embedding is again one. So every identification between composites, at
every dimension, is equivalent to the corresponding identification
between the judgments they represent.

```agda
      reflect-embedding : ∀ {x y} → is-embedding (reflect {x} {y})
      reflect-embedding α c@(f , p) =
        subst (λ β → is-prop (is-representable β)) p
              (is-contr→is-prop (reflect-fiber-contr⁻ f)) c

      ap-reflect-equiv
        : ∀ {x y} {f g : hom x y} → is-equiv (ap (reflect {x} {y}) {f} {g})
      ap-reflect-equiv = is-embedding→ap-equiv reflect-embedding

      ap-reflect-embedding
        : ∀ {x y} {f g : hom x y} → is-embedding (ap (reflect {x} {y}) {f} {g})
      ap-reflect-embedding = ap-is-embedding reflect-embedding
```

## Associativity, per hand

Both bracketings represent the same judgment: rewriting the outer head
with `reflect-⨾⁻` exposes an inner action, and the distributive law
collects it back. Left-cancellation then identifies the edges.

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
```

The unit laws come the same way, and readback is not among their
inputs: a composite with the chosen edge and its factor have the same
reflection, and left-cancellation descends that.

```agda
      unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ unit⁻ y ≡ f
      unitr⁻ {y = y} f =
        reflect-lc (reflect-⨾⁻ f (unit⁻ y) ∙ sym (composite⁻-unitr f))

      unitl⁺ : ∀ {x y} (f : hom x y) → unit⁺ x ⨾⁺ f ≡ f
      unitl⁺ {x} f =
        reflect-lc (reflect-⨾⁺ (unit⁺ x) f ∙ sym (composite⁺-unitl f))
```

## What the spike settles

The engine is contractibility of `reflect`'s fiber over its own image,
and it needs exactly two tiers: composability, and unitality. A
reflected edge is its own hand's composite with that hand's projected
unit, so its fiber *is* a composability fiber transported along one
unit law. Each hand supplies it alone.

What the engine buys is left-cancellability of `reflect`, and with it
the unit laws and associativity of each composition — per hand, with no
interchange, no mediation, no truncation, and no readback family. Both
bracketings represent one judgment, by the outer head's rewriting
followed by that hand's distributive law, and left-cancellation
descends the identity from judgments to edges.

The chosen edge `idn` is not consumed anywhere above. It is needed to
*state* the vocabulary — `var`, `covar` and `eval` are defined from it,
and the unit tier's fiber is taken over `snd` of an argument built with
it — but no result here asks it to be a unit. The unit each hand runs
on is the one its own tier projects, canonical as the centre of a
contractible fiber and unique by `unit⁻-unique`.
