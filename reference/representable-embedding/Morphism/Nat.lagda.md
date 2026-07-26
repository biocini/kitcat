Lane Biocini
February 2026

Natural transformations between functors on categories, instantiated
from the generic magmoid theory.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Nat where

open import Cat.Base
open import Cat.Data.Magmoid
import Cat.Data.Nat as N

private
  mgm : ∀ {o h} → category o h → magmoids
  mgm C = str ob hom yon yon-emb where open Cat C

module _ {o h o' h'} (C : category o h) (D : category o' h') where
  open N (mgm C) (mgm D) public
```
