Higher thinnings: order-preserving embeddings with
parametricity paths.

0-cells: `o'`, `os`, `oz` — the thinning structure, matching
`Data.Thin.Type._≤_`.

1-cells: `os-coh`, `o'-coh` — transport along element paths
is trivial. These make transport endpoints trivial (transport
of `os θ` along any element path returns `os θ`) and give
named computational paths for composition.

The 1-cells alone do NOT make the type a set: they freely
add loops (one per K-loop at each node), and these loops
are not forced to be trivial without 2-cells. The question
of what additional structure makes `≤H` a set — or gives
it enough coherence for compose-contr — is open.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Thinning.Type where

open import Core.Type
open import Core.Base using (_≡_; PathP)
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type using (_:-_)

private variable
  u : Level
  K : Type u
  k k₁ k₂ : K
  iz jz : List K

data _≤H_ {u} {K : Type u}
  : List K → List K → Type u where
  o' : iz ≤H jz → iz ≤H (jz :- k)
  os : iz ≤H jz → (iz :- k) ≤H (jz :- k)
  oz : [] ≤H []
  os-coh : (p : k₁ ≡ k₂) (θ : iz ≤H jz)
    → PathP (λ i → (iz :- p i) ≤H (jz :- p i))
        (os θ) (os θ)
  o'-coh : (p : k₁ ≡ k₂) (θ : iz ≤H jz)
    → PathP (λ i → iz ≤H (jz :- p i))
        (o' θ) (o' θ)

```
