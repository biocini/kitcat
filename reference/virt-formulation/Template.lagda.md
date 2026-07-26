Lane Biocini

```
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Virt.Homotopy where

open import Core.Type
open import Core.Base
open import Core.Data
open import Core.HLevel
open import Core.Cast
open import Lib.Virt.Base

module _ {u} {Γ : Type u} ⦃ V : Virtual Γ ⦄ where
  open Virtual V

  module _ {C : Γ} where
    private
      infix 6 _~>_ _=>_
      _~>_ = hom C
      _=>_ = hom2 C
      _⨾_ = cut
      _⊚_ = vcut; infixr 9 _⨾_ _⊚_
      _●_ = hcut; infixr 8 _●_
