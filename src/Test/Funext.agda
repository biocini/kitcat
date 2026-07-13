{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.Funext where

open import Core.Base
open import Core.Type using (Level; Type)
open import Core.Kan

private
  funext⁴
    : ∀ {u v} {A : Type u}
      {B : A → A → A → A → Type v}
      {f g : ∀ a b c d → B a b c d}
    → (∀ a b c d → f a b c d ≡ g a b c d)
    → f ≡ g
  funext⁴ h = funext λ a → funext λ b →
    funext λ c → funext λ d → h a b c d

test⁴ : ∀ {u v} {A : Type u}
     {B : A → A → A → A → Type v}
     {f g h : ∀ a b c d → B a b c d}
     → (p : ∀ a b c d → f a b c d ≡ g a b c d)
     → (q : ∀ a b c d → g a b c d ≡ h a b c d)
     → funext⁴ (λ a b c d → p a b c d ∙ q a b c d)
     ≡ funext⁴ p ∙ funext⁴ q
test⁴ p q = refl
