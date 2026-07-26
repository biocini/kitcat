```agda

{-# OPTIONS --safe --erased-cubical #-}

module System.S where

open import Core.Type
open import Lib.Erased
open import Core.Base
open import Lib.Path.Erased
open import Lib.Sigma
open import Lib.Plus
open import Lib.Nat
open import Data.List
open import Data.List.Disjoint



data Ptm : Type
data Ptm where
  sq : Ptm
  star : Ptm
  abs : Ptm → Ptm → Ptm
  sub : Ptm → Ptm → Ptm
  iota : Ptm → Ptm → Ptm
  app : Ptm → Ptm → Ptm
  pi : Ptm → Ptm → Ptm
  all : Ptm → Ptm → Ptm
  eqv : Ptm → Ptm → Ptm → Ptm

Cx = List Ptm
data Exp : Ptm → Cx → Type
data Exp where
  var : ∀ {Γ a} → Own [ a ] Γ → Exp a Γ
  lam : ∀ {Γ a b} → Exp b (Γ :< a) → Exp star Γ → Exp (pi a b) Γ
  app : ∀ {Γ a b} → Exp (pi a b) Γ → Exp a Γ → Exp (app a b) Γ
  all : ∀ {Γ a} → Exp star (Γ :< self a) → Exp star Γ
  inst : ∀ {Γ a} → Exp (self a) Γ → Exp a Γ
  gen : ?
  iot-app : ∀ {Γ a} → Exp (self a) Γ → Exp (app a a) Γ

infix 3 _:-_
_:-_ : Cx → (Cx → Type) → Type
Γ :- P = P Γ
