```agda

{-# OPTIONS --safe --erased-cubical #-}

module System.LTLC where

open import Core.Type
open import Lib.Sigma
open import Lib.Plus
open import Lib.Nat
open import Data.Path
open import Data.List
open import Data.List.Disjoint
open import Rel.Ternary.Base
open import Rel.Ternary.SepAlg


data Ptm : Type where
  ref : Ptm → Ptm
  box : Ptm
  star : Ptm
  lam : Ptm → Ptm → Ptm
  app : Ptm → Ptm → Ptm → Ptm → Ptm
  pi : Ptm → Ptm → Ptm
  sg : Ptm → Ptm → Ptm
  all : Ptm → Ptm → Ptm
  eql : Ptm → Ptm → Ptm
  idn : Ptm → Ptm → Ptm → Ptm
  sub : Ptm → Ptm → Ptm → Ptm -- sub b x a -> b [x/t] where t : a
  dep : Ptm → Ptm → Ptm
  refl : Ptm → Ptm

Cx = List Ptm
StoreTy = List Ptm

module SAlg = SepAlg (Disj-SepAlg Ptm)
open SAlg

data _⟶_ : Cx → Cx → Type
data Exp : Ptm → Ptm → Cx → Cx → Type where
  var : ∀ {Ξ a} → Exp (ref a) box Ξ [ a ]
  typ : ∀ {Ξ} → Exp star box Ξ []
  eql : ∀ {Γ a b} → Exp a b Γ [] → Exp (eql a b) box Γ [] → Exp a b Γ []
  pi : ∀ {Γ a b} → Exp a star Γ [] → Exp b box (Γ :< a) → Exp (pi a b) box Γ
  lam : ∀ {Γ₁ Γ₂ Γ b} a
      → Exp a star Γ₁ → Exp b star (Γ₂ :< a) → Disj Γ₁ Γ₂ Γ
      → Exp (lam a b) (pi a b) Γ
  sg : ∀ {Γ a b} → Exp a star Γ → Exp b box (Γ :< a) → Exp (sg a b) box Γ
  app : ∀ {Γ a b f x} → Exp a star Γ → Exp b box (Γ :< a) → Exp f (pi a b) Γ → Exp x a Γ
      -- needs a cover for dependency on a and b
      → Exp (app a (dep a b) f x) (sub b x a) Γ
  app-eq : ∀ {Γ a b x y} → Exp a star Γ → Exp y b (Γ :< a) → Exp x a Γ
         → Exp (eql (app a (dep a b) (lam a b) a) (sub y x a)) (sub b x a) Γ
  app-ext : ∀ {Γ a b f g x y} → Exp f (pi a b) Γ → Exp g (pi a b) Γ
          → Exp (app a (dep a b) f y) (sub a (dep a b) {!!}) (Γ :< a)
          → Exp (eql f g) (pi a b) Γ
  idn : ∀ {Γ a x y} → Exp a box Γ → Exp x a Γ → Exp y a Γ → Exp (idn a x y) box Γ
  refl : ∀ {Γ a x} → Exp a box Γ  → Exp x a Γ → Exp (refl x) (idn a x x) Γ

empty : Exp star star [] → Exp star box []
empty = {!!}
data _⇒_ : Cx → Ptm → Type where
  box : ∀ {Γ} → Γ ⇒ box
  typ : ∀ {Γ a} → Exp a box Γ → Γ ⇒ a

infix 4 _⟶_
data _⟶_ where
  nil : [] ⟶ []
  -- exch1 : {Γ Δ φ ψ : Cx} → φ ⟶ Δ
  --      → {sep : Cx} → Disj φ ψ Γ
  --      → (φ₁ :< a) ⟶ (Δ :< a)

data Env : Cx → StoreTy → Type
data Val : Ptm → StoreTy → Type where
  uni : Val star []
  ref : ∀ {a} → Val (ref a) [ a ]
  clos : ∀ {Γ a t u φ} → Exp t a (Γ :< u) → Env Γ φ → Val (pi t u) φ

data Env where
  nil : Env [] []
  cons : ∀ {Γ t φ₁ φ₂ φ} → Val t φ₁ → Disj φ₁ φ₂ φ → Env Γ φ₂ → Env (Γ :< t) φ

Store : List Ptm → List Ptm → Type
Store φ₁ φ₂ = Env φ₁ φ₂

infix 3 _:-_
_:-_ : Cx → (Cx → Type) → Type
Γ :- P = P Γ
