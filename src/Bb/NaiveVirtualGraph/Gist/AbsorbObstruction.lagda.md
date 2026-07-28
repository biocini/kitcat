Spike: can a proposition pin the chosen edge?

The virtual graph carries `idn` freely: nothing in `reflect` mentions
it, and `judgment` is built from objects and edges alone. A predicate
that is to make the graph a deductive system must therefore say, among
other things, that the chosen edge absorbs. This spike measures the cost
of asking that of a *proposition*.

The measurement is a rigidity theorem. Any propositional predicate
delivering absorption forces the doubling endomap of the identity family
to be constant on loops — an unconditional consequence, with no h-level
hypothesis anywhere and no commitment to how the predicate is packaged.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.NaiveVirtualGraph.Gist.AbsorbObstruction where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; module pcom; module cat)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Groupoid.Virtual using (module yon-unbiased)

open import Bb.NaiveVirtualGraph.Base
```

## Absorption as one path

Both slots of the coterm-hand's held argument are filled by the same
family of endo-edges, so the whole statement is a path between two
elements of one function type: the family obtained by holding `i`, and
the family that returns the coterm's own edge.

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G

  flank : Type (o ⊔ h)
  flank = (x : ob) (γ : coterm x) → hom x (γ .fst)

  held : ((x : ob) → hom x x) → flank
  held i x γ = reflect (i x) ((x , i x) , γ)

  cut : flank
  cut x γ = γ .snd

absorbs : ∀ {o h} (G : virtual-graph o h) → Type (o ⊔ h)
absorbs G = held G (virtual-graph.idn G) ≡ cut G
```

Pointwise this is `reflect (idn x) (var x , γ) ≡ γ .snd`; the funext'd
form is what makes the rigidity argument a square rather than a family
of squares.

## Perturbing the chosen edge

`ob`, `hom` and `reflect` are untouched, so a loop on the identity
family is a self-path of the graph.

```agda
perturb : ∀ {o h} (G : virtual-graph o h)
        → virtual-graph.idn G ≡ virtual-graph.idn G → G ≡ G
perturb G q i .virtual-graph.ob      = virtual-graph.ob G
perturb G q i .virtual-graph.hom     = virtual-graph.hom G
perturb G q i .virtual-graph.idn     = q i
perturb G q i .virtual-graph.reflect = virtual-graph.reflect G
```

Record eta makes both endpoints `G` on the nose, and `absorbs (perturb G
q i)` is `held G (q i) ≡ cut G` definitionally: the family varies, the
target does not.

## Rigidity

A propositional predicate has no room to distinguish the graph from its
perturbation, so a witness of it slides along the self-path; whatever
absorption the predicate delivers slides with it. The resulting square
has the doubling loop along one edge and reflexivity along the other.

```agda
module obstruction {o h ℓ}
  (P : virtual-graph o h → Type ℓ)
  (P-prop : (G : virtual-graph o h) → is-prop (P G))
  (pin : (G : virtual-graph o h) → P G → absorbs G)
  where

  drift : (G : virtual-graph o h) (p : P G)
          (q : virtual-graph.idn G ≡ virtual-graph.idn G)
        → PathP (λ i → absorbs (perturb G q i)) (pin G p) (pin G p)
  drift G p q i =
    pin (perturb G q i) (is-prop→PathP (λ j → P-prop (perturb G q j)) p p i)

  rigid : (G : virtual-graph o h) (p : P G)
          (q : virtual-graph.idn G ≡ virtual-graph.idn G)
        → ap (held G) q ≡ refl
  rigid G p q =
    Path.loop-refl (sym (pin G p)) (ap (held G) q)
      (λ i j → drift G p q i (~ j))
```

## The path groupoid, and what the loop is

```agda
module path {u} (A : Type u) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob        = A
  PG .virtual-graph.hom x y   = x ≡ y
  PG .virtual-graph.idn x     = refl
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  rx : (x : A) → x ≡ x
  rx x = refl
```

Reflexivity absorbs, at every carrier and with no h-level hypothesis:
holding it in both slots leaves the ternary composite standing on its
third argument. So the conclusion the predicate is asked to deliver is
true — what fails is the delivery.

```agda
  pg-absorbs : absorbs PG
  pg-absorbs = funext λ x → funext λ γ → pcom.ideml (γ .snd)
```

Reading the held family at the axiom half of each coterm leaves the
chosen edge standing in both remaining slots, so the flank restricts to
pointwise squaring.

```agda
  restrict : flank PG → (x : A) → x ≡ x
  restrict f x = f x (x , refl)

  dbl : ((x : A) → x ≡ x) → (x : A) → x ≡ x
  dbl i = restrict (held PG i)

  double : (i : (x : A) → x ≡ x) (x : A) → dbl i x ≡ i x ∙ i x
  double i x =
    pcom.unique (sym (i x)) (i x) refl
      (i x ∙ i x ∙ refl , cat.lcoh (i x) (i x) refl)
    ∙ Path.lwhisker (i x) (Path.unitr (i x))
```

Restriction is a map out of the flank, so rigidity transports along it.

```agda
module _ {u ℓ} (A : Type u)
  (P : virtual-graph u u → Type ℓ)
  (P-prop : (G : virtual-graph u u) → is-prop (P G))
  (pin : (G : virtual-graph u u) → P G → absorbs G)
  where
  open path A
  open obstruction P P-prop pin

  doubling-rigid : (p : P PG) (q : rx ≡ rx) → ap dbl q ≡ refl
  doubling-rigid p q i j = restrict (rigid PG p q i j)
```

## What the spike settles

`doubling-rigid` is the whole content of the question in one line. A
propositional predicate on `(ob, hom, idn, reflect)` that delivers
absorption, and holds of the path groupoid on `A`, forces every loop of
the reflexivity family to be annihilated by doubling. By `double` that
endomap is pointwise path-squaring, so on `π₀` of the loop space
`(x : A) → refl {x = x} ≡ refl` — that is, on the sections of `x ↦
Ω²(A , x)` — it is multiplication by two.

Where `A` is a groupoid that loop space is trivial and the demand costs
nothing, which is exactly why the shape succeeds on truncated carriers
and why success there is no evidence. Where `A` carries a section of `x
↦ Ω²(A , x)` of infinite order — `A = S²` and the generator of the
second homotopy group, CONJECTURED here, standard in the literature —
doubling is injective and the demand is false. No such predicate exists.

`pg-absorbs` locates the failure. The absorption the predicate must
deliver is available, unconditionally and untruncated; and the only
hypothesis of `rigid` that is not met by taking the predicate to be
`absorbs` itself is `P-prop`. So the obstruction is neither to
absorption nor to its constructibility, but to any propositional route
between them.

Two boundaries on the claim, stated exactly. It bounds predicates on the
virtual graph as given, not on a carrier that has already absorbed the
laws: moving `absorbs` into the record removes `perturb`'s source and
with it the argument. And it says nothing against a *merely* inhabited
absorption, which is propositional by construction and yields every
propositional consequence of absorption while yielding absorption
itself only where it splits.

The failures already on record are this obstruction seen from
particular angles. `Bb.NaiveVirtualGraph.Gist.StabilityShape` computes
the datum, given the unit fiber, as a path in a hom type;
`Bb.NaiveVirtualGraph.Gist.SelfUnit` finds that demoting the chosen
edge weakens *is a unit* to *squares to a unit* — the same doubling,
met head-on. What the rigidity theorem adds is that the obstruction is
not a property of any packaging: it is the free occurrence of `idn` in
the record.
