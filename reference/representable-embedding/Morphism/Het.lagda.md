Lane Biocini
February 2026

Adjunctions between categories, instantiated from the generic
magmoid heteromorphism theory.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Het where

open import Cat.Base
open import Cat.Data.Magmoid
import Cat.Data.Het as H

private
  mgm : ∀ {o h} → category o h → magmoids
  mgm C = str ob hom yon yon-emb where open Cat C

module _ {o h o' h'} (C : category o h) (D : category o' h') where
  open H (mgm C) (mgm D) public
```
