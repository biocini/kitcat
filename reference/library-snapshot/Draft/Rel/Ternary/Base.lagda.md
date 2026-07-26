A port of Rouvoet's excellent [ternary.agda:Relation/Ternarynary/Core](https://github.com/ajrouvoet/ternary.agda/blob/master/src/Relation/Ternarynary/Core.agda)

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Rel.Ternary.Base where

open import Core.Type
open import Lib.Sigma
open import Data.Path
open import Data.List

record Ternary {u} (A : Type u) v : Type (u ⊔ v ₊) where
  field _<>_<>_ : A → A → A → Type v

  _∙_ = _<>_<>_

  -- concise notation for "being separated"
  _◆_ : A → A → Type (u ⊔ v)
  _◆_ = λ Φ₁ Φ₂ → Σ Φ :: A , Φ₁ <> Φ₂ <> Φ

  whole : {Φ₁ Φ₂ : A} → Φ₁ ◆ Φ₂ → A
  whole = fst

  -- buy one, get a preorder for free
  _≤_ : A → A → Type (u ⊔ v)
  Φ₁ ≤ Φ = Σ Φ₂ :: A , Φ₁ <> Φ₂ <> Φ
