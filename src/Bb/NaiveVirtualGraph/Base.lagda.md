The carrier shared by the archive, and the vocabulary it supports
before any composability, unit, or stability hypothesis is imposed.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.NaiveVirtualGraph.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat.Type
open import Core.Transport
open import Core.Retract
```

## The carrier

A virtual graph is objects, edges between them, and a chosen edge
`idn` at each object. Terms and coterms are edges anchored at a
point, incoming and outgoing; an argument pairs one of each, and its
conclusion is the hom type between their far endpoints. `reflect` is
the one axiom: every edge names a judgment over its own endpoints.

```agda
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
```

## Sequents

The maps built from the carrier alone: pairing a term and a coterm
into an argument, viewing an edge as a term or a coterm at its own
endpoint, evaluating a judgment at the axiom argument, and the
representability fiber of `reflect` — the type a composability or
stability tier contracts.

```agda
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

## The axiom-free vocabulary

Each hand's action holds one slot of the argument at its axiom half —
`coact-π`/`act-π` at the level of edges, `coact`/`act` at the level of
terms and coterms — and `readback` is evaluation at the axiom read
back against the edge it came from. None of the four needs a
composability, unit, or stability hypothesis.

```agda
module vocab {o h} (G : virtual-graph o h) where
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

  readback : Type (o ⊔ h)
  readback = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f
```

## The pin lemma

A family `∀ x y (p : x ≡ y) → T p ≡ p`, for an operator `T` on paths,
is determined by its values at `refl` — singleton contraction along
the identity type. Fixing a pin `t₀` identifying those refl-values
with `refl` therefore makes the package of a family together with an
identification of its refl-component against `t₀` a retract of the
anchor `Σ v , (∀ x → v x ≡ t₀ x)`, which is contractible by one
connection. `pin-contr` is that contraction; `at-refl`, `extend`, and
`extend-retract` are the retraction it runs on.

```agda
path-◁ : ∀ {u} {X Y : Type u} → X ≡ Y → X ◁ Y
path-◁ P .section    = transport P
path-◁ P .retraction = transport⁻ P
path-◁ P .is-retract = transport-transport⁻ P

module pin {u} {A : Type u}
  (T : ∀ {x y : A} → x ≡ y → x ≡ y)
  (t₀ : ∀ x → T (refl {x = x}) ≡ refl)
  where

  refl-values : Type u
  refl-values = ∀ x → T (refl {x = x}) ≡ refl

  readback : Type u
  readback = ∀ x y (p : x ≡ y) → T p ≡ p

  pinned : readback → Type u
  pinned rd = ∀ x → rd x x refl ≡ t₀ x

  package : Type u
  package = Σ rd ∶ readback , pinned rd

  anchor : Type u
  anchor = Σ v ∶ refl-values , (∀ x → v x ≡ t₀ x)

  at-refl : readback → refl-values
  at-refl rd x = rd x x refl

  extend : refl-values → readback
  extend v x y p = J (λ _ q → T q ≡ q) (v x) p

  extend-refl : ∀ v x → extend v x x refl ≡ v x
  extend-refl v x = J-refl (λ _ q → T q ≡ q) (v x)

  extend-glue
    : ∀ rd x y (p : x ≡ y)
    → extend (at-refl rd) x y p ≡ rd x y p
  extend-glue rd x y p =
    J (λ y' q → extend (at-refl rd) x y' q ≡ rd x y' q)
      (extend-refl (at-refl rd) x) p

  extend-retract : ∀ rd → extend (at-refl rd) ≡ rd
  extend-retract rd i x y p = extend-glue rd x y p i

  readback-◁ : readback ◁ refl-values
  readback-◁ .section    = at-refl
  readback-◁ .retraction = extend
  readback-◁ .is-retract = extend-retract

  pinned-line : ∀ v → pinned (extend v) ≡ (∀ x → v x ≡ t₀ x)
  pinned-line v i = ∀ x → extend-refl v x i ≡ t₀ x

  package-◁ : package ◁ anchor
  package-◁ = Σ-◁ readback-◁ λ v → path-◁ (pinned-line v)

  anchor-contr : is-contr anchor
  anchor-contr .center = t₀ , λ _ → refl
  anchor-contr .paths (v , k) i =
    (λ x → k x (~ i)) , λ x j → k x (~ i ∨ j)

  pin-contr : is-contr package
  pin-contr = ◁→is-hlevel Z package-◁ anchor-contr
```
