Lane Biocini
July 2026

Positive half of the readback dichotomy: over a path-presented graph,
a readback family pinned at reflexivity is unique up to contractible
choice. A family over every `(x, y, p : x ≡ y)` is determined by its
values at `refl` — singleton contraction — so anchoring those values
collapses the package, and the anchoring datum's slack concentrates
entirely away from identity-generated presentations. The generic
lemma needs no category apparatus; the ∞-groupoid instance lands it
with the canonical pin drawn from the record's `unit` field.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.AnchorPin where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat.Type
open import Core.Transport
open import Core.Retract

open import Cat.Depreciated.Type
open import Cat.Depreciated.Groupoid
```

## Retract along a line of types

A path of types is a retract: transport forward for the section,
backward for the retraction, with the round trip closed by the
inverse transport law.

```agda
path-◁ : ∀ {u} {X Y : Type u} → X ≡ Y → X ◁ Y
path-◁ P .section    = transport P
path-◁ P .retraction = transport⁻ P
path-◁ P .is-retract = transport-transport⁻ P
```

## The pin lemma

Fix an operator `T` on paths and a pin `t₀` identifying its
refl-values with `refl`. The package pairs a readback family
`∀ p → T p ≡ p` with an identification of its refl-component
against `t₀`.

```agda
module _ {u} {A : Type u}
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
```

Evaluation at `refl` retracts the readback families onto their
refl-values, with the J-extension for the section's inverse; the
round trip closes by one more J whose base case is the extension's
own computation rule.

```agda
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
```

Over an extended family the pin condition is the anchor fiber read
through the extension's computation rule, a line of types; so the
package is a retract of the anchor by `Σ-◁`.

```agda
  pinned-line : ∀ v → pinned (extend v) ≡ (∀ x → v x ≡ t₀ x)
  pinned-line v i = ∀ x → extend-refl v x i ≡ t₀ x

  package-◁ : package ◁ anchor
  package-◁ = Σ-◁ readback-◁ λ v → path-◁ (pinned-line v)
```

The anchor is a Π of reversed singletons at `t₀`, contracted by one
connection; contractibility then transfers along the retract.

```agda
  anchor-contr : is-contr anchor
  anchor-contr .center = t₀ , λ _ → refl
  anchor-contr .paths (v , k) i =
    (λ x → k x (~ i)) , λ x j → k x (~ i ∨ j)

  pin-contr : is-contr package
  pin-contr = ◁→is-hlevel Z package-◁ anchor-contr
```

## The ∞-groupoid instance

For the path groupoid of any type the operator is evaluation of the
embedded morphism, and the record's `unit` field at `refl` is the
canonical pin: the readback family agreeing with it at reflexivity
is contractible data.

```agda
module _ {u} (B : Type u) where
  open category (∞-groupoid B)

  readback-pin-contr
    : is-contr
        (Σ rd ∶ (∀ (x y : B) (p : x ≡ y) → ev (emb p) ≡ p)
         , (∀ x → rd x x refl ≡ unit refl))
  readback-pin-contr = pin-contr (λ p → ev (emb p)) (λ x → unit refl)
```
