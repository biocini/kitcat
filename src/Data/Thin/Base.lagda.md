Basic operations on thinnings: identity, composition, empty, singleton.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.Thin.Base where

open import Core.Type
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type

private variable
  u : Level
  K : Type u
  iz jz kz mz : List K
  k : K

oi : {kz : List K} → kz ≤ kz
oi {kz = kz :- _} = os oi
oi {kz = []}       = oz

_⨾_ : iz ≤ jz → jz ≤ kz → iz ≤ kz
θ      ⨾ o' φ  = o' (θ ⨾ φ)
o' θ   ⨾ os φ  = o' (θ ⨾ φ)
os θ   ⨾ os φ  = os (θ ⨾ φ)
oz     ⨾ oz    = oz

infixr 9 _⨾_

representation : iz ≤ jz → jz ≤ kz → kz ≤ mz → iz ≤ mz
representation θ φ (o' ψ) = o' (representation θ φ ψ)
representation θ (o' φ) (os ψ) = o' (representation θ φ ψ)
representation (o' θ) (os φ) (os ψ) = o' (representation θ φ ψ)
representation (os θ) (os φ) (os ψ) = os (representation θ φ ψ)
representation θ oz oz = θ

oe : {kz : List K} → [] ≤ kz
oe {kz = kz :- _} = o' oe
oe {kz = []}       = oz

_←_ : {K : Type u} → K → List K → Type u
k ← kz = ([] :- k) ≤ kz

```
