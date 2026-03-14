Applicative instance for Maybe.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Maybe.Impl.Applicative where

open import Core.Type
open import Core.Base using (_≡_; refl)
open import Core.Trait.Effect
open import Core.Trait.Map using (Map)
open import Core.Trait.Applicative using (Applicative)
open import Core.Data.Maybe.Impl.Map

open import Agda.Builtin.Maybe

instance
  Applicative-Maybe : Applicative (impl Maybe)
  Applicative-Maybe .Applicative.Map-Applicative =
    Map-Maybe
  Applicative-Maybe .Applicative.pure = just
  Applicative-Maybe .Applicative._<*>_ nothing  _ =
    nothing
  Applicative-Maybe .Applicative._<*>_ (just f) mx =
    map-maybe f mx
  Applicative-Maybe .Applicative.pure-id
    {v = nothing}  = refl
  Applicative-Maybe .Applicative.pure-id
    {v = just _}   = refl
  Applicative-Maybe .Applicative.pure-∘
    {u = nothing}  = refl
  Applicative-Maybe .Applicative.pure-∘
    {u = just _} {v = nothing}  = refl
  Applicative-Maybe .Applicative.pure-∘
    {u = just _} {v = just _} {w = nothing}  = refl
  Applicative-Maybe .Applicative.pure-∘
    {u = just _} {v = just _} {w = just _}   = refl
  Applicative-Maybe .Applicative.pure-hom = refl
  Applicative-Maybe .Applicative.pure-interchange
    {u = nothing} = refl
  Applicative-Maybe .Applicative.pure-interchange
    {u = just _}  = refl

```
