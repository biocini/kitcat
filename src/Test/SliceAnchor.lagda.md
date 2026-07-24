Lane Biocini
July 2026

Over a reflexive graph whose over- and under-slices are contractible,
an embedding into two-sided composites together with its readback law
is contractible as a joint package: the anchored model is unique
outright, with no fixed embedding and no normalization pin — the
graph's own slices absorb the slack a pin would otherwise fix.
Contexts collapse onto the identity context, evaluation there is an
equivalence onto `hom`, and the package retracts onto the based
singleton at the identity operator. The path graph of any type has
singleton slices, so it carries a unique anchored model.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SliceAnchor where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat.Type
open import Core.Kan using (is-contr→is-prop)
open import Core.Transport
open import Core.Equiv.Base using (_≃_; module Equiv)
open import Core.Equiv.PropIndexed using (Π-prop-index)
open import Core.Retract
open import Core.Groupoid using (Singl-contr-cofan)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Groupoid using (path-Rx)
```

## Retract along a line of types

A line of types is a retract: transport forward sections, transport
backward retracts, and the inverse transport law seals the round trip.

```agda
path-◁ : ∀ {u} {X Y : Type u} → X ≡ Y → X ◁ Y
path-◁ P .section    = transport P
path-◁ P .retraction = transport⁻ P
path-◁ P .is-retract = transport-transport⁻ P
```

## Evaluation at the identity context

Assume both slices contract. A context is then a proposition — the
product of two contractible slices — so a composite, being a Π over
the contexts, is determined by its value at any one of them. Reading
at the identity context is `Π-prop-index`'s forward map, which is
definitionally `ev`, and the codomain `res (ov-idn x , un-idn y)` is
definitionally `hom x y`: evaluation is an equivalence.

```agda
module _ {o h} (S : reflexive-graph o h)
  (oc : ∀ x → is-contr (virtual.over S x))
  (uc : ∀ x → is-contr (virtual.under S x))
  where
  open virtual S

  ctx-prop : ∀ x y → is-prop (ctx x y)
  ctx-prop x y = is-contr→is-prop (is-contr-× (oc x) (uc y))

  idn-ctx : ∀ x y → ctx x y
  idn-ctx x y = ov-idn x , un-idn y

  eval-equiv : ∀ x y → composite x y ≃ hom x y
  eval-equiv x y = Π-prop-index (ctx-prop x y) (idn-ctx x y)

  ext : ∀ {x y} → hom x y → composite x y
  ext {x} {y} = Equiv.inv (eval-equiv x y)

  ext-ev : ∀ {x y} (α : composite x y) → ext (ev α) ≡ α
  ext-ev {x} {y} = Equiv.unit (eval-equiv x y)

  ev-ext : ∀ {x y} (f : hom x y) → ev (ext f) ≡ f
  ev-ext {x} {y} = Equiv.counit (eval-equiv x y)
```

## The anchored package

An anchored model pairs an embedding family with its readback law;
the anchor pairs an operator family on `hom` with a pointwise
identification against the identity. Evaluation sections the
embeddings onto the operators, the equivalence's unit closing the
round trip, and over an extended operator the readback condition is
the identity condition read through the counit — a line of types.
`Σ-◁` assembles the package as a retract of the anchor.

```agda
  embedding : Type (o ⊔ h)
  embedding = ∀ x y → hom x y → composite x y

  operator : Type (o ⊔ h)
  operator = ∀ x y → hom x y → hom x y

  readback : embedding → Type (o ⊔ h)
  readback emb = ∀ x y (f : hom x y) → ev (emb x y f) ≡ f

  identical : operator → Type (o ⊔ h)
  identical T = ∀ x y (f : hom x y) → T x y f ≡ f

  embedding-◁ : embedding ◁ operator
  embedding-◁ .section    emb x y f = ev (emb x y f)
  embedding-◁ .retraction T x y f = ext (T x y f)
  embedding-◁ .is-retract emb i x y f = ext-ev (emb x y f) i

  readback-line : ∀ T → readback (embedding-◁ .retraction T) ≡ identical T
  readback-line T i = ∀ x y (f : hom x y) → ev-ext (T x y f) i ≡ f

  anchored-◁
    : (Σ emb ∶ embedding , readback emb) ◁ (Σ T ∶ operator , identical T)
  anchored-◁ = Σ-◁ embedding-◁ λ T → path-◁ (readback-line T)
```

The anchor is a Π of reversed singletons at the identity operator;
one connection contracts it, and the package inherits along the
retract.

```agda
  anchor-contr : is-contr (Σ T ∶ operator , identical T)
  anchor-contr .center = (λ x y f → f) , λ x y f → refl
  anchor-contr .paths (T , k) i =
    (λ x y f → k x y f (~ i)) , λ x y f j → k x y f (~ i ∨ j)

  anchored-model-contr
    : is-contr
        (Σ emb ∶ (∀ x y → hom x y → composite x y)
         , (∀ x y (f : hom x y) → ev (emb x y f) ≡ f))
  anchored-model-contr = ◁→is-hlevel Z anchored-◁ anchor-contr
```

## The path graph instance

Over the path graph of a type the over-slices are reversed singletons
and the under-slices singletons, both contractible, so the anchored
model over paths is unique.

```agda
module _ {u} (A : Type u) where
  open virtual (path-Rx A)

  path-anchored-model-contr
    : is-contr
        (Σ emb ∶ (∀ (x y : A) → x ≡ y → composite x y)
         , (∀ x y (p : x ≡ y) → ev (emb x y p) ≡ p))
  path-anchored-model-contr =
    anchored-model-contr (path-Rx A) Singl-contr-cofan Singl-contr
```
