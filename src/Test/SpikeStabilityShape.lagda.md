Spike: can the stability datum be packaged propositionally?

The unit tier never mentions `idn`: it projects its own unit. The
reflexive graph supplies `idn` independently. Whatever the third tier
is called and however it is packaged, its job is to identify those two,
and this spike shows that job is *equivalent to inhabiting a path in a
hom type* — so no packaging of it is propositional unless the homs are
truncated, which the library refuses.

The argument does not depend on the shape chosen. It takes the most
economical possible datum — the chosen edge absorbs — and computes what
it is.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeStabilityShape where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (_≃_; iso→equiv; is-contr-equiv)
open import Core.Equiv.Properties using (_∙e_; esym; Σ-contr-fst)
open import Core.HLevel.Base using (is-prop-equiv)

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

module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (argue (var x) γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (argue t (covar y))
```

## The datum, and what it is

Given the unit tier, the third tier's content in its smallest form is
that `idn` acts as the identity action — every richer packaging,
readback included, delivers this and is delivered by it together with
the tier's uniqueness.

```agda
  module _ (U⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)) where

    unit⁻ : ∀ x → hom x x
    unit⁻ x = U⁻ x .center .fst

    datum : ∀ x → Type (o ⊔ h)
    datum x = coact-π (idn x) ≡ snd
```

The unit fiber is contractible, so its component at any edge is the
path space from that edge to the centre. Reassociating and contracting
the two singletons in turn — the fiber itself, and the based path space
at `idn x` — computes the datum outright.

```agda
    singl-contr : ∀ {x} (a : hom x x) → is-contr (Σ e ∶ hom x x , e ≡ a)
    singl-contr a .center = a , refl
    singl-contr a .paths (e , p) i = p (~ i) , λ j → p (~ i ∨ j)

    reassoc : ∀ {x} (a : hom x x)
            → (Σ t ∶ fiber (coact-π {x} {x}) snd , t .fst ≡ a)
            ≃ (Σ s ∶ (Σ e ∶ hom x x , e ≡ a) , coact-π (s .fst) ≡ snd)
    reassoc a = iso→equiv (λ ((e , q) , r) → (e , r) , q)
                          (λ ((e , r) , q) → (e , q) , r)
                          (λ _ → refl) (λ _ → refl)

    component≃path : ∀ {x} (a : hom x x) → (coact-π a ≡ snd) ≃ (unit⁻ _ ≡ a)
    component≃path a =
      esym (Σ-contr-fst (singl-contr a))
      ∙e esym (reassoc a)
      ∙e Σ-contr-fst (U⁻ _)

    datum≃path : ∀ x → datum x ≃ (unit⁻ x ≡ idn x)
    datum≃path x = component≃path (idn x)
```

## The obstruction

So the datum *is* a path in `hom x x`, and asking it to be
propositional asks the loop space of `hom x x` at `idn x` to be
propositional. That is a truncation condition on the homs, and it is
the same condition `Test.SpikeUnitCanonical` extracts from the
half-adjoint form by a twist argument — obtained here without
reference to any particular packaging.

```agda
    datum-prop→loop-prop
      : ∀ x → is-prop (datum x) → is-prop (unit⁻ x ≡ idn x)
    datum-prop→loop-prop x pr = is-prop-equiv (esym (datum≃path x)) pr

    datum-prop→truncation
      : ∀ x → is-prop (datum x) → datum x → is-prop (idn x ≡ idn x)
    datum-prop→truncation x pr a =
      subst (λ e → is-prop (e ≡ idn x))
            (datum≃path x .fst a) (datum-prop→loop-prop x pr)
```

## One fiber carrying both absorptions

The remaining candidate asks for a single edge absorbing on both
hands, contracted as one space. It is `is-contr` of a Σ, so
propositional, and its centre is one edge — the two hands cannot
disagree about their unit because there is only one. The question is
whether it is ever contractible.

```agda
    module _ (U⁺ : ∀ x → is-contr (fiber (act-π {x} {x}) snd)) where

      unit⁺ : ∀ x → hom x x
      unit⁺ x = U⁺ x .center .fst

      singl-contr⁺ : ∀ {x} (a : hom x x) → is-contr (Σ e ∶ hom x x , e ≡ a)
      singl-contr⁺ a .center = a , refl
      singl-contr⁺ a .paths (e , p) i = p (~ i) , λ j → p (~ i ∨ j)

      reassoc⁺ : ∀ {x} (a : hom x x)
               → (Σ t ∶ fiber (act-π {x} {x}) snd , t .fst ≡ a)
               ≃ (Σ s ∶ (Σ e ∶ hom x x , e ≡ a) , act-π (s .fst) ≡ snd)
      reassoc⁺ a = iso→equiv (λ ((e , q) , r) → (e , r) , q)
                             (λ ((e , r) , q) → (e , q) , r)
                             (λ _ → refl) (λ _ → refl)

      component≃path⁺ : ∀ {x} (a : hom x x) → (act-π a ≡ snd) ≃ (unit⁺ _ ≡ a)
      component≃path⁺ a =
        esym (Σ-contr-fst (singl-contr⁺ a))
        ∙e esym (reassoc⁺ a)
        ∙e Σ-contr-fst (U⁺ _)

      both : ∀ x → Type (o ⊔ h)
      both x = Σ e ∶ hom x x , (coact-π e ≡ snd) × (act-π e ≡ snd)

      both-reassoc : ∀ x
                   → both x ≃ (Σ c ∶ fiber (coact-π {x} {x}) snd , act-π (c .fst) ≡ snd)
      both-reassoc x = iso→equiv (λ (e , p , q) → (e , p) , q)
                                 (λ ((e , p) , q) → e , p , q)
                                 (λ _ → refl) (λ _ → refl)

      both≃path : ∀ x → both x ≃ (unit⁺ x ≡ unit⁻ x)
      both≃path x =
        both-reassoc x ∙e Σ-contr-fst (U⁻ x) ∙e component≃path⁺ (unit⁻ x)
```

So the combined tier is a path in a hom type too — between the two
hands' units rather than between one of them and `idn`. Contracting it
asks that path space to be contractible, which at an inhabited point
is a truncation condition exactly as before.

```agda
      both-contr→truncation
        : ∀ x → is-contr (both x) → both x → is-contr (unit⁻ x ≡ unit⁻ x)
      both-contr→truncation x c b =
        subst (λ e → is-contr (e ≡ unit⁻ x))
              (both≃path x .fst b) (is-contr-equiv (esym (both≃path x)) c)
```

## What the spike settles

The third tier's content is not propositional data, and the reason is
structural rather than a want of ingenuity. The unit tier's fiber is
contractible, so its component at `idn` is a path space to the
projected unit; the tier's content is an inhabitant of that path space;
and a path in an untruncated hom type is not a proposition.

Two limits on that claim are worth stating exactly. It bounds any
packaging *equivalent* to the datum, not every conceivable one: a
strictly stronger propositional condition is not excluded, though it
would be non-conservative, ruling out graphs whose chosen edge does
absorb. And wrapping the datum in `is-contr` makes the *statement*
propositional without making the content so — what is then asserted is
contractibility of a space whose readback component
`Test.SpikePathGroupoid` shows is not a proposition above h-level
three. Whether the flank coherence nonetheless contracts it there is
open.

The same computation disposes of the one-fiber-for-both-hands
candidate. Contracting a single space of edges absorbing on both sides
is propositional as a statement and does force the hands to share a
unit, but `both≃path` shows the space is the path type `unit⁺ x ≡
unit⁻ x`, so asserting its contractibility is again a truncation
condition — this time between the two projected units rather than
between one of them and the chosen edge. Moving the quantifier does not
change what is being asserted.

So every packaging tried reduces to a path in a hom type: `idn` against
a projected unit, or the two projected units against each other. That
is one obstruction wearing three costumes.

What is no longer at stake is the derived theory. Readback's remaining
consumers were the unit laws, and those follow from the engine of
`Cat.Logic.Gist.ReflectFiber` — composability plus the flank absorptions —
with no readback family in scope. Associativity never needed it either.
