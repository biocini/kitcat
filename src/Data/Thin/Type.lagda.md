Order-preserving embeddings (thinnings) between list scopes.
From McBride, "Everybody's Got To Be Somewhere" (MSFP 2018).

Scopes are ordinary lists with a right-associative snoc pattern
`_:-_` for readability: `kz :- k` is `k ∷ kz`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.Thin.Type where

open import Core.Type
open import Core.Data.List.Type using (List; []; _∷_)

pattern _:-_ kz k = k ∷ kz
infixl 7 _:-_

data _≤_ {u} {K : Type u} : List K → List K → Type u where
  o' : ∀ {iz jz k} → iz ≤ jz → iz ≤ (jz :- k)
  os : ∀ {iz jz k} → iz ≤ jz → (iz :- k) ≤ (jz :- k)
  oz : [] ≤ []

```
