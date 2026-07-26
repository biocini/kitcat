Lane Biocini
February 2026

Isomorphisms in categories, instantiated from the generic magmoid
iso theory. Derives unitality of the category's identity morphism.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Iso where

open import Cat.Base
open import Cat.Data.Magmoid
import Cat.Data.Neutral as N
import Cat.Data.Iso as I
open import Core.Type using (id)
open import Core.Data.Sigma using (fst; snd; _,_)
open import Core.Equiv using (iso→equiv)

private
  mgm : ∀ {o h} → category o h → magmoids
  mgm C = str ob hom yon yon-emb where open Cat C

cat-unital
  : ∀ {o h} (C : category o h) → ∀ x → N.unital (mgm C) x
cat-unital C x = idn , u where
  open Cat C

  u : N.is-unital (mgm C) idn
  u .N.is-unital.neutral .fst =
    iso→equiv (λ g → yon g _ idn) id
      (yon-op-idn-pt _) (yon-op-idn-pt _) .snd
  u .N.is-unital.neutral .snd =
    iso→equiv (λ h → yon idn _ h) id
      (yon-idn-pt _) (yon-idn-pt _) .snd
  u .N.is-unital.lcoh f = yon-op-idn-pt _ _
  u .N.is-unital.rcoh f = yon-idn-pt _ _

module _ {o h} (C : category o h) where
  open I (mgm C) (cat-unital C) public
```
