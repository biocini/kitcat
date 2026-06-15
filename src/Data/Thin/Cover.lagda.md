Covers: coproducts in slices of thinnings.

A `Cover ov θ' φ'` witnesses that `θ'` and `φ'` jointly cover
their common target — every variable is selected by at least
one. The flag `ov` controls overlap: `true` for coproducts
(overlap allowed), `false` for partitions (disjoint).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.Thin.Cover where

open import Core.Type
open import Core.Data.Sigma using (Sigma; _,_; _×_)
open import Core.Data.List using (List; []; _∷_)
open import Core.Data.Bool.Type using (Bool; true; false)
open import Data.Thin.Type
open import Data.Thin.Base
open import Data.Thin.Tri

open Core.Type using (⊤)

data ⊥ : Type where

Tt : Bool → Type
Tt true  = ⊤
Tt false = ⊥

private variable
  u : Level
  K : Type u
  iz jz kz ijz : List K

data Cover {u} {K : Type u} (ov : Bool)
  : {iz jz ijz : List K}
  → iz ≤ ijz → jz ≤ ijz → Type u where
  c's : ∀ {k} {θ : iz ≤ ijz} {φ : jz ≤ ijz}
      → Cover ov θ φ → Cover ov (o' θ) (os {k = k} φ)
  cs' : ∀ {k} {θ : iz ≤ ijz} {φ : jz ≤ ijz}
      → Cover ov θ φ → Cover ov (os {k = k} θ) (o' φ)
  css : ∀ {k} {θ : iz ≤ ijz} {φ : jz ≤ ijz}
      → {both : Tt ov}
      → Cover ov θ φ → Cover ov (os {k = k} θ) (os φ)
  czz : Cover ov oz oz

```

## Coproduct computation

Given two thinnings into the same scope, compute their
coproduct: the smallest subscope covering both.

```agda

CopData : {K : Type u} {iz jz kz : List K}
        → (θ : iz ≤ kz) (φ : jz ≤ kz) → Type u
CopData {iz = iz} {jz = jz} {kz = kz} θ φ =
  Sigma _ λ (ijz : List _) →
  Sigma (ijz ≤ kz) λ ψ →
  Sigma (iz ≤ ijz) λ θ' →
  Sigma (jz ≤ ijz) λ φ' →
  Tri θ' ψ θ × Cover true θ' φ' × Tri φ' ψ φ

cop : {K : Type u} {iz jz kz : List K}
    → (θ : iz ≤ kz) (φ : jz ≤ kz) → CopData θ φ
cop (o' θ) (o' φ) =
  let _ , _ , _ , _ , tl , c , tr = cop θ φ
  in  _ , _ , _ , _ , t-'' tl , c , t-'' tr
cop (o' θ) (os φ) =
  let _ , _ , _ , _ , tl , c , tr = cop θ φ
  in  _ , _ , _ , _ , t's' tl , c's c , tsss tr
cop (os θ) (o' φ) =
  let _ , _ , _ , _ , tl , c , tr = cop θ φ
  in  _ , _ , _ , _ , tsss tl , cs' c , t's' tr
cop (os θ) (os φ) =
  let _ , _ , _ , _ , tl , c , tr = cop θ φ
  in  _ , _ , _ , _ , tsss tl , css c , tsss tr
cop oz     oz     =
  _ , _ , _ , _ , tzzz , czz , tzzz

```

## Coproduct universal property

Any other diagram factors through the coproduct. Proof
left as a hole.

```agda

copU : {K : Type u} {iz jz ijz kz : List K}
       {θ' : iz ≤ ijz} {φ' : jz ≤ ijz}
       {ψ : ijz ≤ kz} {θ : iz ≤ kz} {φ : jz ≤ kz}
     → Tri θ' ψ θ → Cover true θ' φ' → Tri φ' ψ φ
     → {ψ' : _ ≤ kz}
     → θ →/ ψ' → φ →/ ψ' → ψ →/ ψ'
copU = {!!}

```
