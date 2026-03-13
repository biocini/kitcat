Alternative instance for Maybe.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Maybe.Impl.Alternative where

open import Core.Type
open import Core.Base using (_≡_; refl)
open import Core.Trait.Effect
open import Core.Trait.Alternative using (Alternative)
open import Core.Data.Maybe.Impl.Applicative

open import Agda.Builtin.Maybe

instance
  Alternative-Maybe : Alternative (impl Maybe)
  Alternative-Maybe .Alternative.Applicative-Alternative =
    Applicative-Maybe
  Alternative-Maybe .Alternative.empty = nothing
  Alternative-Maybe .Alternative._<|>_ nothing  y = y
  Alternative-Maybe .Alternative._<|>_ (just x) _ = just x
  Alternative-Maybe .Alternative.<|>-unitl = refl
  Alternative-Maybe .Alternative.<|>-unitr
    {x = nothing} = refl
  Alternative-Maybe .Alternative.<|>-unitr
    {x = just _}  = refl
  Alternative-Maybe .Alternative.<|>-assoc
    {x = nothing} = refl
  Alternative-Maybe .Alternative.<|>-assoc
    {x = just _}  = refl

```
