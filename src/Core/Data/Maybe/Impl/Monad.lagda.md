Monad instance for Maybe.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Maybe.Impl.Monad where

open import Core.Type
open import Core.Base using (_≡_; refl)
open import Core.Trait.Effect
open import Core.Trait.Monad using (Monad)
open import Core.Data.Maybe.Impl.Applicative

open import Agda.Builtin.Maybe

instance
  Monad-Maybe : Monad (impl Maybe)
  Monad-Maybe .Monad.Applicative-Monad =
    Applicative-Maybe
  Monad-Maybe .Monad._>>=_ nothing  _ = nothing
  Monad-Maybe .Monad._>>=_ (just x) f = f x
  Monad-Maybe .Monad.>>=-unitl = refl
  Monad-Maybe .Monad.>>=-unitr {m = nothing} = refl
  Monad-Maybe .Monad.>>=-unitr {m = just _}  = refl
  Monad-Maybe .Monad.>>=-assoc {m = nothing} = refl
  Monad-Maybe .Monad.>>=-assoc {m = just _}  = refl

```
