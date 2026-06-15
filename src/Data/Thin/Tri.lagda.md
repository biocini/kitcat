Composition triangles: the graph of thinning composition.

Triangles allow unification on constructor indices, avoiding
the need to reason about the defined function `_⨾_`. Slice
morphisms `ψ →/ φ` are triangles with a common edge.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.Thin.Tri where

open import Core.Type
open import Core.Base using (_≡_)
open import Core.Data.Sigma using (Sigma; _,_)
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type
open import Data.Thin.Base

private variable
  u : Level
  K : Type u
  iz jz kz : List K

data Tri {u} {K : Type u} : {iz jz kz : List K}
  → iz ≤ jz → jz ≤ kz → iz ≤ kz → Type u where
  t-'' : ∀ {iz jz kz k} {θ : iz ≤ jz} {φ : jz ≤ kz} {ψ : iz ≤ kz}
       → Tri θ φ ψ → Tri θ (o' {k = k} φ) (o' ψ)
  t's' : ∀ {iz jz kz k} {θ : iz ≤ jz} {φ : jz ≤ kz} {ψ : iz ≤ kz}
       → Tri θ φ ψ → Tri (o' θ) (os {k = k} φ) (o' ψ)
  tsss : ∀ {iz jz kz k} {θ : iz ≤ jz} {φ : jz ≤ kz} {ψ : iz ≤ kz}
       → Tri θ φ ψ → Tri (os {k = k} θ) (os φ) (os ψ)
  tzzz : Tri oz oz oz

tri : {iz jz kz : List K}
    → (θ : iz ≤ jz) (φ : jz ≤ kz) → Tri θ φ (θ ⨾ φ)
tri θ      (o' φ) = t-'' (tri θ φ)
tri (o' θ) (os φ) = t's' (tri θ φ)
tri (os θ) (os φ) = tsss (tri θ φ)
tri oz     oz     = tzzz

-- comp : Tri θ φ ψ → ψ ≡ (θ ⨾ φ)
-- triU : Tri θ φ ψ → Tri θ' φ ψ → θ ≡ θ'
-- Path proofs — to be filled manually.

_→/_ : {K : Type u} {iz jz kz : List K}
     → iz ≤ kz → jz ≤ kz → Type u
ψ →/ φ = Sigma _ λ θ → Tri θ φ ψ

```

## Ternary composition graph

`Tri3` is the graph of `representation` — the fused ternary
composition that decomposes all three thinnings simultaneously.
All data lives in the indices, giving clean unification.

```agda

private variable
  wz vz mz : List K

data Tri3 {u} {K : Type u} : {wz iz jz vz : List K}
  → wz ≤ iz → iz ≤ jz → jz ≤ vz → wz ≤ vz → Type u where
  r-'''  : ∀ {k} {a : wz ≤ iz} {θ : iz ≤ jz} {b : jz ≤ kz} {c : wz ≤ kz}
         → Tri3 a θ b c → Tri3 a θ (o' {k = k} b) (o' c)
  r-'s'  : ∀ {k} {a : wz ≤ iz} {θ : iz ≤ jz} {b : jz ≤ kz} {c : wz ≤ kz}
         → Tri3 a θ b c → Tri3 a (o' θ) (os {k = k} b) (o' c)
  r's's' : ∀ {k} {a : wz ≤ iz} {θ : iz ≤ jz} {b : jz ≤ kz} {c : wz ≤ kz}
         → Tri3 a θ b c → Tri3 (o' a) (os {k = k} θ) (os b) (o' c)
  rssss  : ∀ {k} {a : wz ≤ iz} {θ : iz ≤ jz} {b : jz ≤ kz} {c : wz ≤ kz}
         → Tri3 a θ b c → Tri3 (os {k = k} a) (os θ) (os b) (os c)
  rzzzz  : Tri3 oz oz oz oz

tri3 : {wz iz jz vz : List K}
     → (a : wz ≤ iz) (θ : iz ≤ jz) (b : jz ≤ vz)
     → Tri3 a θ b (representation a θ b)
tri3 a θ      (o' b) = r-'''  (tri3 a θ b)
tri3 a (o' θ) (os b) = r-'s'  (tri3 a θ b)
tri3 (o' a) (os θ) (os b) = r's's' (tri3 a θ b)
tri3 (os a) (os θ) (os b) = rssss  (tri3 a θ b)
tri3 oz oz oz = rzzzz

-- repr3 : Tri3 a θ b c → c ≡ representation a θ b
-- tri3U : Tri3 a θ b c → Tri3 a' θ b c → a ≡ a'
-- Path proofs — to be filled manually.

```
