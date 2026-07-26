Spike: can the unit be characterised without a chosen edge?

The two-tier predicate leaves three things unfixed — the projected
units are not the graph's chosen edge, and the two hands' units are not
each other. A self-referential unit datum, after
`reference/ternary-composition/Virtual/Contractible-Unit.lagda.md`,
promises to fix all three at once: it asks for an edge that absorbs
with *itself* in the held slot, so it mentions no chosen edge, projects
one edge carrying both absorptions, and is `is-contr` of a Σ, hence
propositional.

This spike asks what that datum actually says.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeSelfUnit where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom)
open import Core.Path.Base
open import Core.Equiv.Base using (_≃_)
open import Core.Equiv.Properties using (Π-contr-dom)
open import Core.Groupoid.Virtual using (module yon-unbiased)
```

## A graph with no chosen edge

`reflect`'s type needs only objects and edges — terms, coterms,
arguments and conclusions are all built by `Σ` and `×` from those. The
chosen edge is needed for `var`, `covar` and `eval`, which are downstream
of the unit tier rather than upstream of it.

```agda
record pre-graph o h : Type₊ (o ⊔ h) where
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
```

## The self-referential datum

The edge stands in its own held slot, on each hand.

```agda
module _ {o h} (G : pre-graph o h) where
  open pre-graph G

  argue : ∀ {x y} → term x → coterm y → argument x y
  argue t k = t , k

  unit-data : ob → Type (o ⊔ h)
  unit-data x =
    Σ e ∶ hom x x
    , ((t : term x)   → reflect e (argue t (x , e)) ≡ t .snd)
    × ((γ : coterm x) → reflect e (argue (x , e) γ) ≡ γ .snd)

  is-unital : Type (o ⊔ h)
  is-unital = ∀ x → is-contr (unit-data x)
```

Being `is-contr` of a type, the tier is a proposition, and its centre
projects one edge carrying both absorptions — so the hands cannot
disagree. What remains is whether it says what a unit is.

## The path groupoid, as a graph with no chosen edge

```agda
module path {u} (A : Type u) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  PG : pre-graph u u
  PG .pre-graph.ob      = A
  PG .pre-graph.hom x y = x ≡ y
  PG .pre-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  open pre-graph PG
```

Terms and coterms are the based path spaces, so each condition is a
family over a contractible domain and collapses to its value at the
centre.

```agda
  term-contr : ∀ x → is-contr (term x)
  term-contr x .center = x , refl
  term-contr x .paths (w , p) i = p (~ i) , λ j → p (~ i ∨ j)

  coterm-contr : ∀ y → is-contr (coterm y)
  coterm-contr y .center = y , refl
  coterm-contr y .paths (v , p) i = p i , λ j → p (i ∧ j)

  collapse⁺ : ∀ x (e : x ≡ x)
            → ((t : term x) → reflect e (argue PG t (x , e)) ≡ t .snd)
            ≃ (emb e x refl x e ≡ refl)
  collapse⁺ x e = Π-contr-dom {B = λ t → reflect e (argue PG t (x , e)) ≡ t .snd}
                              (term-contr x)

  collapse⁻ : ∀ x (e : x ≡ x)
            → ((γ : coterm x) → reflect e (argue PG (x , e) γ) ≡ γ .snd)
            ≃ (emb e x e x refl ≡ refl)
  collapse⁻ x e = Π-contr-dom {B = λ γ → reflect e (argue PG (x , e) γ) ≡ γ .snd}
                              (coterm-contr x)

```

Both collapsed conditions are `pcom.composite refl e e ≡ refl` up to
which flank carries the reflexivity: the ternary composite of `e` with
*itself* is trivial. That is not the unit law — it is `e ∙ e ≡ refl`,
modulo the unit law for the trivial flank.

## What the spike settles

The self-referential datum does not characterise a unit. With both
held slots occupied by the edge itself, the condition on `e` is that
`e` composed with itself absorbs, which for the path groupoid is
`pcom.composite refl e e ≡ refl`. Reflexivity satisfies it, and so —
CONJECTURED, the instance is not checked here — does every loop of
order two, with its witnesses; over a carrier whose loop space has such
an element the type `unit-data x` would then have points with distinct
first components, so it is not contractible and the tier fails.

The reason is structural. Absorption is a statement about a *neutral*
edge in the held slot, and the self-referential form has no neutral
edge to put there, so it substitutes the very edge being tested. That
weakens *is a unit* to *squares to a unit*, and the two agree only
where the loop space is torsion-free.

So the chosen edge cannot be demoted this way. Either it stays a field
of the graph, in which case identifying it with the projected unit is
the hom-path `Test.SpikeStabilityShape` shows is not propositional, or
a characterisation of the unit is needed that refers to a neutral slot
without presupposing one — and this is not it.
