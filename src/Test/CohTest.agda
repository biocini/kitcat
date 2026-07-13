{-# OPTIONS --erased-cubical --no-guardedness --no-sized-types #-}

module Test.CohTest where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path
open import Core.Equiv
open import Core.Transport
open import Core.Function.Embedding

open import Cat.Base

module _ {o h} (C : category o h) where
  open category C
  private
    module R {x} {y} = Emb (repr {x} {y})
    R' = repr .fst

  -- Build 4-fold fiber elements for pentagon
  module Pentagon {v w x y z : ob}
    (f : hom v w) (g : hom w x) (h : hom x y) (k : hom y z) where

    d₄ : ∀ {u} → hom u v → hom u z
    d₄ a = R' k (R' h (R' g (R' f a)))

    -- F₁: ((f ⨾ g) ⨾ h) ⨾ k
    F₁ : fiber R' d₄
    F₁ .fst = ((f ⨾ g) ⨾ h) ⨾ k
    F₁ .snd =
      coh ((f ⨾ g) ⨾ h) k .snd
      ∙ (λ i a → R' k (coh (f ⨾ g) h .snd i a))
      ∙ (λ i a → R' k (R' h (coh f g .snd i a)))

    -- F₅: f ⨾ (g ⨾ (h ⨾ k))
    F₅ : fiber R' d₄
    F₅ .fst = f ⨾ (g ⨾ (h ⨾ k))
    F₅ .snd =
      coh f (g ⨾ (h ⨾ k)) .snd
      ∙ (λ i a → coh g (h ⨾ k) .snd i (R' f a))
      ∙ (λ i a → coh h k .snd i (R' g (R' f a)))

    -- Check: these should typecheck
    test : F₁ .fst ≡ F₅ .fst
    test = ap fst (repr .snd _ F₁ F₅)
