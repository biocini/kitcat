Map instance for Maybe.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Maybe.Impl.Map where

open import Core.Type
open import Core.Base using (_≡_; refl; funext)
open import Core.Trait.Effect
open import Core.Trait.Map using (Map)

open import Agda.Builtin.Maybe

map-maybe
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A → B) → Maybe A → Maybe B
map-maybe f nothing  = nothing
map-maybe f (just x) = just (f x)

instance
  Map-Maybe : Map (impl Maybe)
  Map-Maybe .Map.map = map-maybe
  Map-Maybe .Map.map-id = funext go where
    go : ∀ {ℓ} {A : Type ℓ}
      (x : Maybe A) → map-maybe id x ≡ x
    go nothing  = refl
    go (just _) = refl
  Map-Maybe .Map.map-comp {f = f} {g} =
    funext go where
    go : ∀ x
      → map-maybe (f ∘ g) x
      ≡ (map-maybe f ∘ map-maybe g) x
    go nothing  = refl
    go (just _) = refl

```
