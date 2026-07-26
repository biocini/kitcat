Lane Biocini
February 2026


```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Base.Dual where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
open import Core.Equiv
open import Core.Function.Embedding

record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    repr
      : ∀ {x y} → hom x y ↪ (∀ {w} → hom w x → hom w y)
    unital
      : ∀ {x} → fiber (repr {x} {x} .fst) id
    coh
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → fiber (repr .fst) (repr .fst g ∘ repr .fst f)

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = coh f g .fst

  op-map
    : ∀ {x y}
    → hom x y → (∀ {z} → hom y z → hom x z)
  op-map f g = f ⨾ g

  field
    repr-op-emb
      : ∀ {x y} → is-embedding (op-map {x} {y})
    repr-yon
      : ∀ {w x y} (f : hom w x)
      → repr {w} {x} .fst f {y} ≡ λ (g : hom y w) → g ⨾ f
    fib : fiber {!!} {!!}
```

## Derived definitions

The covariant embedding gives injectivity: equal representations
imply equal morphisms. All category laws reduce to showing that
two representations coincide, then applying injectivity.

```agda
  private
    module R {x} {y} = Emb (repr {x} {y})

  idn : ∀ {x} → hom x x
  idn = unital .fst
```

## Contravariant representation

The op-representation sends a morphism to its post-composition
action. The embedding property is the extra axiom.

```agda
  repr-op : ∀ {x y} → hom x y ↪ (∀ {z} → hom y z → hom x z)
  repr-op .fst = op-map
  repr-op .snd = repr-op-emb

  private
    module Rop {x} {y} = Emb (repr-op {x} {y})
```

## Right unit law

`coh f idn .snd` gives a path from `repr .fst (f ⨾ idn)` to
`repr .fst idn ∘ repr .fst f`. Then `unital .snd` collapses
`repr .fst idn` to `id`, recovering `repr .fst f`.

```agda
  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  unitr f = R.inj
    (coh f idn .snd ∙ λ i h → unital .snd i (repr .fst f h))
```

## Left unit law

```agda
  unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  unitl f = R.inj
    (coh idn f .snd
    ∙ λ i h → repr .fst f (unital .snd i h))
```

## Associativity

Both `(f ⨾ g) ⨾ h` and `f ⨾ (g ⨾ h)` live in a fiber over the
fully-decomposed representation
`λ a → repr .fst h (repr .fst g (repr .fst f a))`.
We build each fiber element and then use propositional fibers to
identify them.

```agda
  assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (repr .snd _ lhs rhs)
    where
      decomposed
        : ∀ {v} → hom v _ → hom v _
      decomposed a =
        repr .fst h (repr .fst g (repr .fst f a))

      lhs : fiber (repr .fst) decomposed
      lhs .fst = (f ⨾ g) ⨾ h
      lhs .snd =
        coh (f ⨾ g) h .snd
        ∙ λ i a →
          repr .fst h (coh f g .snd i a)

      rhs : fiber (repr .fst) decomposed
      rhs .fst = f ⨾ (g ⨾ h)
      rhs .snd =
        coh f (g ⨾ h) .snd
        ∙ λ i a →
          coh g h .snd i (repr .fst f a)
```

## Derived op-structure

The unit and coherence witnesses for `repr-op` follow from
`unitl` and `assoc`.

```agda
  unital-op : ∀ {x} → fiber (repr-op {x} {x} .fst) id
  unital-op .fst = idn
  unital-op .snd i g = unitl g i

  coh-op
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → fiber (repr-op .fst)
        (repr-op .fst f ∘ repr-op .fst g)
  coh-op f g .fst = f ⨾ g
  coh-op f g .snd i h = assoc f g h i
```

## Repr-op injectivity

If `f` and `g` compose identically with every morphism on the
right, they must be equal. We instantiate at `idn` and cancel
the units.

```agda
  repr-op-inj
    : ∀ {x y} {f g : hom x y}
    → (∀ {z} (h : hom y z) → f ⨾ h ≡ g ⨾ h)
    → f ≡ g
  repr-op-inj {f = f} {g} p =
    pcom (unitr f) (p idn) (unitr g)
```

## The op construction

The opposite category swaps `repr` with the derived `repr-op`
and uses the derived `coh-op`. The Yoneda condition `repr-yon`
identifies `repr .fst` with post-composition, so the opposite's
`repr-op-emb` is `repr .snd` transported along `repr-yon`. The
opposite's `repr-yon` is `refl` since `repr-op .fst` is already
defined as pre-composition.

```agda
-- module _ {o h} (C : category o h) where
--   private module C = category C

--   op : category o h
--   op .category.ob          = C.ob
--   op .category.hom         = λ x y → C.hom y x
--   op .category.repr        = C.repr-op
--   op .category.unital      = C.unital-op
--   op .category.coh         = λ f g → C.coh-op g f
--   op .category.repr-op-emb {y} = subst is-embedding (λ i (f : C.hom y _) {w} → C.repr-yon f i) (C.repr .snd)
--   op .category.repr-yon f = refl
```
