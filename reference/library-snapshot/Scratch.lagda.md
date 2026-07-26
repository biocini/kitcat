```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Claude.Scratch where

open import Core.Type
open import Lib.Sigma
open import Core.Base
open import Core.Kan hiding (fill)
open import Lib.Path
open import Lib.Path.Gpd using (module cat) renaming (cat to infixr 40 _∙_)

open import Lib.Path.Homotopy
