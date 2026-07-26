Lane Biocini
February 2026

Biinvertible equivalences in categories, instantiated from the
generic magmoid equivalence theory.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Eqv where

open import Cat.Base
open import Cat.Data.Magmoid
import Cat.Data.Eqv as E
import Cat.Iso as Iso

private
  mgm : ∀ {o h} → category o h → magmoids
  mgm C = str ob hom yon yon-emb where open Cat C

module _ {o h} (C : category o h) where
  open E (mgm C) (Iso.cat-unital C) public
```
