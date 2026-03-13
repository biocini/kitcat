The Maybe type with Map, Applicative, Monad, and Alternative instances.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Data.Maybe where

open import Agda.Builtin.Maybe public

module maybe where
  open import Core.Data.Maybe.Properties public

  module impl where
    open import Core.Data.Maybe.Impl.Map public
    open import Core.Data.Maybe.Impl.Applicative public
    open import Core.Data.Maybe.Impl.Monad public
    open import Core.Data.Maybe.Impl.Alternative public
    open import Core.Data.Maybe.Impl.Trunc public

```
