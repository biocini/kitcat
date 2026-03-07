Properties of coproducts.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Sum.Properties where

open import Core.Base
open import Core.Type
open import Core.Transport
open import Core.Equiv using (_≃_; Equiv)
open import Core.Path.IdType using (⊎-path-inl; ⊎-path-inr; ⊎-disjoint)
open import Core.Kan using (_∙_)
open import Core.Data.Nat.Type using (Nat; S)
open import Core.Data.Empty
open import Core.Data.Sum.Type
open import Core.Data.Sum.Base

open import Core.Trait.Trunc
  using ( is-hlevel; retract→is-hlevel; Path-is-hlevel
        ; is-prop→is-hlevel-suc )

private variable
  u v w x y z : Level
  A : Type u
  B : Type v
  C : Type w
  D : Type x
  E : Type y
  F : Type z

```

## Constructor properties

The constructors `inl` and `inr` are injective and disjoint.

```agda

private
  from-inl : {A : Type u} {B : Type v} → A → A ⊎ B → A
  from-inl d (inl a) = a
  from-inl d (inr _) = d

  from-inr : {A : Type u} {B : Type v} → B → A ⊎ B → B
  from-inr d (inl _) = d
  from-inr d (inr b) = b

inl-inj : {a a' : A} → inl {B = B} a ≡ inl a' → a ≡ a'
inl-inj {a = a} p = ap (from-inl a) p

inr-inj : {b b' : B} → inr {A = A} b ≡ inr b' → b ≡ b'
inr-inj {b = b} p = ap (from-inr b) p

disjoint : {a : A} {b : B} → inl a ≡ inr b → ⊥
disjoint p = subst f p tt where
  f : A ⊎ B → Type
  f (inl _) = ⊤
  f (inr _) = ⊥

```

## Swap

```agda

module swap where
  invol : ∀ (x : A ⊎ B) → swap (swap x) ≡ x
  invol (inl _) = refl
  invol (inr _) = refl

```

## Map

```agda

module map where
  id-id : ∀ (x : A ⊎ B) → map id id x ≡ x
  id-id (inl _) = refl
  id-id (inr _) = refl

  comp
    : (f : A → C) (g : C → E)
      (h : B → D) (k : D → F)
      (x : A ⊎ B)
    → map (g ∘ f) (k ∘ h) x ≡ map g k (map f h x)
  comp f g h k (inl _) = refl
  comp f g h k (inr _) = refl

```

## H-levels

Sum types preserve h-levels. Paths in sum types decompose: paths
between inl's come from paths in A, paths between inr's from paths
in B, and paths between inl and inr are impossible.

```agda

module _ {u' v'} {A' : Type u'} {B' : Type v'} where
  private
    module inl-path {a a' : A'} =
      Equiv (⊎-path-inl {B = B'} {a = a} {a' = a'})
    module inr-path {b b' : B'} =
      Equiv (⊎-path-inr {A = A'} {b = b} {b' = b'})

    inl-inl-hlevel
      : (n : Nat) → is-hlevel (S (S n)) A'
      → (a a' : A')
      → is-hlevel (S n) (inl {B = B'} a ≡ inl a')
    inl-inl-hlevel n ahl a a' =
      retract→is-hlevel (S n)
        encode decode linv
        (Path-is-hlevel {x = a} {y = a'} ahl)
      where
        encode : a ≡ a' → inl {B = B'} a ≡ inl a'
        encode = inl-path.inv

        decode : inl {B = B'} a ≡ inl a' → a ≡ a'
        decode = inl-path.fwd

        linv
          : (p : inl {B = B'} a ≡ inl a')
          → encode (decode p) ≡ p
        linv = inl-path.unit

    inr-inr-hlevel
      : (n : Nat) → is-hlevel (S (S n)) B'
      → (b b' : B')
      → is-hlevel (S n) (inr {A = A'} b ≡ inr b')
    inr-inr-hlevel n bhl b b' =
      retract→is-hlevel (S n)
        encode decode linv
        (Path-is-hlevel {x = b} {y = b'} bhl)
      where
        encode : b ≡ b' → inr {A = A'} b ≡ inr b'
        encode = inr-path.inv

        decode : inr {A = A'} b ≡ inr b' → b ≡ b'
        decode = inr-path.fwd

        linv
          : (p : inr {A = A'} b ≡ inr b')
          → encode (decode p) ≡ p
        linv = inr-path.unit

    inl-inr-hlevel
      : (n : Nat) → (a : A') (b : B')
      → is-hlevel (S n) (inl a ≡ inr b)
    inl-inr-hlevel n a b =
      is-prop→is-hlevel-suc {n = n}
        (λ p _ → ex-falso (⊎-disjoint p))

    inr-inl-hlevel
      : (n : Nat) → (b : B') (a : A')
      → is-hlevel (S n) (inr b ≡ inl a)
    inr-inl-hlevel n b a =
      is-prop→is-hlevel-suc {n = n}
        (λ p _ → ex-falso (⊎-disjoint (sym p)))

  ⊎-is-hlevel
    : (n : Nat)
    → is-hlevel (S (S n)) A' → is-hlevel (S (S n)) B'
    → is-hlevel (S (S n)) (A' ⊎ B')
  ⊎-is-hlevel n ahl bhl (inl a) (inl a') =
    inl-inl-hlevel n ahl a a'
  ⊎-is-hlevel n ahl bhl (inl a) (inr b) =
    inl-inr-hlevel n a b
  ⊎-is-hlevel n ahl bhl (inr b) (inl a) =
    inr-inl-hlevel n b a
  ⊎-is-hlevel n ahl bhl (inr b) (inr b') =
    inr-inr-hlevel n bhl b b'
```
