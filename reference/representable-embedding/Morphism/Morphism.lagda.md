Lane Biocini
February 2026

Morphism vocabulary for a specific category, instantiated from
the generic magmoid theory.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Base

module Cat.Morphism {o h} (C : category o h) where

open import Cat.Data.Magmoid
open import Core.Base
open import Core.Type using (_∘_)
open import Core.Transport.J using (subst)
import Cat.Data.Base as B

open Cat C

private
  M : magmoids
  M = str ob hom yon yon-emb

open B M public
  hiding (o; h; ob; hom; yon; yon-op; yon-emb; _⨾_; yon-inj; assoc)
```

## Bridge lemmas

The category's `composable-contr` gives both `yon-composite` (the composition
witness) and `comp-eq` (the propositional equality between the two
compositions). We derive composability in the magmoid sense from these.

```agda
cat-composable
  : ∀ {x y z} (f : hom x y) (g : hom y z)
  → composable f g
cat-composable f g =
  subst (λ s → yon s ≡ λ w → yon g w ∘ yon f w)
    (comp-eq f g) (yon-composite f g)

cat-thunkable : ∀ {x y} (f : hom x y) → is-thunkable f
cat-thunkable f g = cat-composable f g

cat-linear : ∀ {y z} (h : hom y z) → is-linear h
cat-linear h g = cat-composable g h

cat-assoc-m : associativity
cat-assoc-m f g h = B.assoc M (cat-thunkable f) (cat-linear h)
```
