A port of Rouvoet's excellent [ternary.agda:Relation/Ternarynary/Core](https://github.com/ajrouvoet/ternary.agda/blob/master/src/Relation/Ternarynary/Core.agda)

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Rel.Ternary.SepAlg where

open import Core.Type
open import Lib.Sigma

open import Data.Path
open import Data.List

open import Rel.Ternary.Base

record has-separation-alg {u v} {A : Type u} (T : Ternary A v) : Type (u ⊔ v) where
  open Ternary T
  field
    unit : A
    idl : ∀ a → unit <> a <> a
    to-path : ∀ {a b} → unit <> a <> b → a ≡ b
    comm : ∀ {a b c} → a <> b <> c → b <> a <> c
    assoc : ∀ {a b c ab abc}
          → a <> b <> ab → ab <> c <> abc
          → Σ bc :: A , a <> bc <> abc × (b <> c <> bc)

  Emp : A → Type u
  Emp = Own unit
  {-# INLINE Emp #-}

module SepAlg {a u} {A : Type a} {T : Ternary A u} (alg : has-separation-alg T) where
  open Ternary T renaming (_<>_<>_ to _∙_≋_)
  open has-separation-alg alg
  -- we can see the three point relation as a predicate on the carrier
 {- Partial products over the relation -}
  infixr 10 _∙⟨_⟩_
  record Conj {p q} (P : A → Type p) (Q : ∀ {Φ} → P Φ → A → Type q) Φ : Type (p ⊔ q ⊔ a ⊔ u) where
    pattern
    constructor _∙⟨_⟩_
    field
      {Φₗ Φᵣ} : A

      px  : P Φₗ
      sep : Φₗ ∙ Φᵣ ≋ Φ
      qx  : Q px Φᵣ

  infixr 9 Σ⋆-syntax
  Σ⋆-syntax : ∀ {p q} → (P : A → Type p) → (Q : ∀ {Φ} → P Φ → A → Type q) → A → Type (p ⊔ q ⊔ a ⊔ u)
  Σ⋆-syntax = Conj

  syntax Σ⋆-syntax A (λ x → B) = Σ✶ x :: A , B

  infixr 9 _✶_
  _✶_ : ∀ {p q} → (A → Type p) → (A → Type q) → A → Type (p ⊔ q ⊔ a ⊔ u)
  _✶_ P Q = Σ✶ x :: P , Q

  {- Partial exponents over the relation -}

  record Wand {b p q} {B : Type b}
    (P : B → Type p)
    (j : B → A)
    (Q : ∀ {Φ} → P Φ → A → Type q)
    (Φᵢ : A) : Type (p ⊔ q ⊔ a ⊔ b ⊔ u) where

    constructor arr

    infixl 10 _⟨_⟩_
    field
      _⟨_⟩_ : ∀ {Φₚ Φ} → Φᵢ ∙ j Φₚ ≋ Φ → (px : P Φₚ) → Q px Φ

  open Wand public

  infixr 8 _─✶[_]_
  _─✶[_]_ : ∀ {p q b} {B : Type b} (P : B → Type p) (j : B → A) (Q : A → Type q) → A → Type (p ⊔ q ⊔ a ⊔ b ⊔ u)
  (P ─✶[ j ] Q) = Wand P j (const Q)

  infixr 8 Π✶-syntax
  Π✶-syntax : ∀ {p q} → (P : A → Type p) → (Q : ∀ {Φ} → P Φ → A → Type q) → A → Type (p ⊔ q ⊔ a ⊔ u)
  Π✶-syntax P Q = Wand P id Q
  syntax Π✶-syntax P (λ x → Q) = Π[ x ∈ P ]✶ Q

  -- TODO this should be in Relation.Unary
  infixr 8 Π>-syntax
  Π>-syntax : ∀ {p q} → (P : A → Type p) → (Q : ∀ {Φ} → P Φ → A → Type q) → A → Type (p ⊔ q)
  Π>-syntax P Q = λ Φ → (px : P Φ) → Q px Φ
  syntax Π>-syntax P (λ x → Q) = Π> x :: P , Q

  infixr 8 _-✶_
  _-✶_ : ∀ {p q} (P : A → Type p) (Q : A → Type q) → A → Type (p ⊔ q ⊔ a ⊔ u)
  _-✶_ P Q = Wand P id (const Q)

  apply : ∀ {p q} {P : A → Type p} {Q : A → Type q} → ! (P -✶ Q) ✶ P => Q
  apply (f ∙⟨ σ ⟩ px) = f ⟨ σ ⟩ px

  ✶swap : ∀ {p q} {P : A → Type p} {Q : A → Type q} → ! (P ✶ Q) => (Q ✶ P)
  ✶swap (px ∙⟨ sep ⟩ qx) = qx ∙⟨ comm sep ⟩ px



  ✶assoc : ∀ {p q r} {P : A → Type p} {Q : A → Type q} {R : A → Type r}
         → ! (P ✶ Q) ✶ R => P ✶ (Q ✶ R)
  ✶assoc ((px ∙⟨ sep₁ ⟩ px') ∙⟨ sep₂ ⟩ qx) .Conj.Φₗ = _
  ✶assoc ((px ∙⟨ sep₁ ⟩ px') ∙⟨ sep₂ ⟩ qx) .Conj.Φᵣ = _
  ✶assoc ((px ∙⟨ sep₁ ⟩ px') ∙⟨ sep₂ ⟩ qx) .Conj.px = px
  ✶assoc ((px ∙⟨ sep₁ ⟩ px') ∙⟨ sep₂ ⟩ qx) .Conj.sep = assoc sep₁ sep₂ .snd .fst
  ✶assoc ((px ∙⟨ sep₁ ⟩ px') ∙⟨ sep₂ ⟩ qx) .Conj.qx .Conj.Φₗ = _
  ✶assoc ((px ∙⟨ sep₁ ⟩ px') ∙⟨ sep₂ ⟩ qx) .Conj.qx .Conj.Φᵣ = _
  ✶assoc ((px ∙⟨ sep₁ ⟩ px') ∙⟨ sep₂ ⟩ qx) .Conj.qx .Conj.px = px'
  ✶assoc ((px ∙⟨ sep₁ ⟩ px') ∙⟨ sep₂ ⟩ qx) .Conj.qx .Conj.sep = assoc sep₁ sep₂ .snd .snd
  ✶assoc ((px ∙⟨ sep₁ ⟩ px') ∙⟨ sep₂ ⟩ qx) .Conj.qx .Conj.qx = qx

  ✶rotate  : ∀ {p q r} {P : A → Type p} {Q : A → Type q} {R : A → Type r}
           → ! (P ✶ Q) ✶ R => R ✶ (P ✶ Q)
  ✶rotate ((px ∙⟨ k ⟩ qx) ∙⟨ s ⟩ rx) .Conj.Φₗ = _
  ✶rotate ((px ∙⟨ k ⟩ qx) ∙⟨ s ⟩ rx) .Conj.Φᵣ = _
  ✶rotate ((px ∙⟨ k ⟩ qx) ∙⟨ s ⟩ rx) .Conj.px = rx
  ✶rotate ((px ∙⟨ k ⟩ qx) ∙⟨ s ⟩ rx) .Conj.sep = comm s
  ✶rotate ((px ∙⟨ k ⟩ qx) ∙⟨ s ⟩ rx) .Conj.qx .Conj.Φₗ = _
  ✶rotate ((px ∙⟨ k ⟩ qx) ∙⟨ s ⟩ rx) .Conj.qx .Conj.Φᵣ = _
  ✶rotate ((px ∙⟨ k ⟩ qx) ∙⟨ s ⟩ rx) .Conj.qx .Conj.px = px
  ✶rotate ((px ∙⟨ k ⟩ qx) ∙⟨ s ⟩ rx) .Conj.qx .Conj.sep = k
  ✶rotate ((px ∙⟨ k ⟩ qx) ∙⟨ s ⟩ rx) .Conj.qx .Conj.qx = qx

  ✶idl : ∀ {u} {P : A → Type u} → ! P => P ✶ Emp
  ✶idl p .Conj.Φₗ = _
  ✶idl p .Conj.Φᵣ = _
  ✶idl p .Conj.px = p
  ✶idl p .Conj.sep = comm (idl _)
  ✶idl p .Conj.qx = λ i → unit

  ✶emp : ∀ {u} {P : A → Type u} → ! Emp ✶ P => P
  ✶emp {P} (px ∙⟨ sep ⟩ qx) = Path.tr P (to-path (Path.tr (_∙ _ ≋ _) px sep)) qx

  module _ {u v w} {P : A → Type u} {Q : A → Type v} {R : A → Type w} where
    uncurry : ! P ✶ Q => R → ! P => (Q -✶ R)
    uncurry f p ._⟨_⟩_ s q = f (p ∙⟨ s ⟩ q)

    curry : ! P => (Q -✶ R) → ! P ✶ Q => R
    curry f (px ∙⟨ sep ⟩ qx) = f px ⟨ sep ⟩ qx

  module _ {u} {P : A → Type u} where
    force : ! Emp => P → P unit
    force f = f (to-path (idl unit))

    abs : P unit → ! Emp => P
    abs p e = Path.tr P (hsym e) p

  Writer : ∀ {v w} {K : Type v} → (K → K → A → Type v) → K → K → (A → Type w) → A → Type (a ⊔ u ⊔ v ⊔ w)
  Writer W k1 k2 P = W k1 k2 ✶ P

  --force

  module Star where
    data Star {v} (P : A → Type v) : A → Type (a ⊔ u ⊔ v) where
      nil : Star P unit
      cons : ! P ✶ Star P => Star P

module _ {a} {A : Type a} where
  One : A → (List A) → Type _
  One t = Own [ t ]




{- Rel morphisms -}
-- module _ {a} {A : Type a} where

--   _flipped : Separation-alg A → Separation-alg A
--   Separation-alg._∙_≋_ (rel flipped) = let open Separation-alg rel in λ Φ₁ Φ₂ Φ → Φ₂ ∙ Φ₁ ≋ Φ

{- Properties of ternary relations -}
-- module _ {a} {A : Type a} where

--   Commutative : Separation-alg A → Type a
--   Commutative rel = let open Separation-alg rel
--     in ∀ {a b ab : A} → a ∙ b ≋ ab → b ∙ a ≋ ab

--   RightAssoc : Separation-alg A → Type a
--   RightAssoc rel = let open Separation-alg rel in
--     ∀ {a b ab c abc}
--       → a ∙ b ≋ ab → ab ∙ c ≋ abc
--       → Σ bc :: ? , a ∙ bc ≋ abc × b ∙ c ≋ bc

--   LeftAssoc : Separation-alg A → Type a
--   LeftAssoc rel = let open Separation-alg rel in
--     ∀ {a bc b c abc}
--       → a ∙ bc ≋ abc → b ∙ c ≋ bc
--       → Σ ab :: ? , a ∙ b ≋ ab × ab ∙ c ≋ abc

--   -- (a - b) - c ≈> a - (b + c)
--   RightAssoc′ : (add : Separation-alg A) → (sub : Separation-alg A) → Type a
--   RightAssoc′ add sub =
--     let open Separation-alg add renaming (_∙_≋_ to _+_≋_)
--         open Separation-alg sub renaming (_∙_≋_ to _∸_≋_)
--     in ∀ {a₁ a₂ a₃ a₁-₂ a₀ a₂+₃} →
--          a₁ ∸ a₂ ≋ a₁-₂ → a₁-₂ ∸ a₃ ≋ a₀ → a₂ + a₃ ≋ a₂+₃ →
--          a₁ ∸ a₂+₃ ≋ a₀

--   -- a - (b + c) ≈> (a - b) - c
--   LeftAssoc′ : (add : Separation-alg A) → (sub : Separation-alg A) → Type a
--   LeftAssoc′ add sub =
--     let open Separation-alg add renaming (_∙_≋_ to _+_≋_)
--         open Separation-alg sub renaming (_∙_≋_ to _∸_≋_)
--     in ∀ {a₁ a₂ a₃ a₂+₃ a₀} →
--          a₁ ∸ a₂+₃ ≋ a₀ → a₂ + a₃ ≋ a₂+₃ →
--          Σ a₁-₂ :: ? ,
--            a₁ ∸ a₂ ≋ a₁-₂ × a₁-₂ ∸ a₃ ≋ a₀

--   -- (a ∪ b) - c => (a - c) ∪ (b - c)
--   -- sub distributes over cup
--   _DistribOverᵣ_ : (sub : Separation-alg A) (cup : Separation-alg A) → Type a
--   _DistribOverᵣ_ sub cup =
--     let open Separation-alg cup renaming (_∙_≋_ to _⊎_≋_)
--         open Separation-alg sub renaming (_∙_≋_ to _∸_≋_)
--     in ∀ {a b c a∪b d}
--       → a ⊎ b ≋ a∪b → a∪b ∸ c ≋ d
--       → ∃₂ λ a-c b-c → a ∸ c ≋ a-c × b ∸ c ≋ b-c × a-c ⊎ b-c ≋ d

--   -- (a ∪ b) - c <= (a - c) ∪ (b - c)
--   _DistribOverₗ_ : (sub : Separation-alg A) → (cup : Separation-alg A) → Type a
--   _DistribOverₗ_ sub cup =
--     let open Separation-alg cup renaming (_∙_≋_ to _⊎_≋_)
--         open Separation-alg sub renaming (_∙_≋_ to _∸_≋_)
--     in ∀ {a b c d a-c b-c}
--       → a ∸ c ≋ a-c → b ∸ c ≋ b-c → a-c ⊎ b-c ≋ d
--       → ∃ λ a∪b → a ⊎ b ≋ a∪b × a∪b ∸ c ≋ d

--   LeftIdentity : Separation-alg A → A → Type a
--   LeftIdentity rel ε = let open Separation-alg rel in ∀ {Φ} → ε ∙ Φ ≋ Φ

--   LeftIdentity⁻ : ∀ {e} → (A → A → Type e) → Separation-alg A → A → Type (a ⊔ e)
--   LeftIdentity⁻ _≈_ rel ε = let open Separation-alg rel in ∀ {Φ Φ′} → ε ∙ Φ ≋ Φ′ → Φ ≈ Φ′

--   RightIdentity : Separation-alg A → A → Type a
--   RightIdentity rel ε = let open Separation-alg rel in ∀ {Φ} → Φ ∙ ε ≋ Φ

--   RightIdentity⁻ : ∀ {e} → (A → A → Type e) → Separation-alg A → A → Type (a ⊔ e)
--   RightIdentity⁻ _≈_ rel ε = let open Separation-alg rel in ∀ {Φ Φ′} → Φ ∙ ε ≋ Φ′ → Φ ≈ Φ′

--   LeftZero : Separation-alg A → A → Type a
--   LeftZero rel z = let open Separation-alg rel in ∀ {Φ} → z ∙ Φ ≋ z

--   LeftZero⁻ : ∀ {e} → (A → A → Type e) → Separation-alg A → A → Type (a ⊔ e)
--   LeftZero⁻ _≈_ rel z = let open Separation-alg rel in ∀ {Φ Φ′} → z ∙ Φ ≋ Φ′ → Φ′ ≈ z

--   RightZero : Separation-alg A → A → Type a
--   RightZero rel z = let open Separation-alg rel in ∀ {Φ} → Φ ∙ z ≋ z

--   RightZero⁻ : ∀ {e} → (A → A → Type e) → Separation-alg A → A → Type (a ⊔ e)
--   RightZero⁻ _≈_ rel z = let open Separation-alg rel in ∀ {Φ Φ′} → Φ ∙ z ≋ Φ′ → Φ′ ≈ z

--   Idempotent : Separation-alg A → Type a
--   Idempotent rel = let open Separation-alg rel in ∀ {Φ} → Φ ∙ Φ ≋ Φ

--   Idempotent⁻ : ∀ {e} → (A → A → Type e) → Separation-alg A → Type (a ⊔ e)
--   Idempotent⁻ _≈_ rel = let open Separation-alg rel in ∀ {Φ Φ′} → Φ ∙ Φ ≋ Φ′ → Φ ≈ Φ′

--   LeftMonotone : ∀ {e} → (A → A → Type e) → Separation-alg A → Type (a ⊔ e)
--   LeftMonotone _∼_ rel = let open Separation-alg rel in
--     ∀ {Φ₁ Φ₂ Φ Φ₃ Φ′} → Φ₁ ∙ Φ₂ ≋ Φ → Φ₁ ∼ Φ₃ → Φ₃ ∙ Φ₂ ≋ Φ′ → Φ ∼ Φ′

--   RightMonotone : ∀ {e} → (A → A → Type e) → Separation-alg A → Type (a ⊔ e)
--   RightMonotone _∼_ rel = LeftMonotone _∼_ (rel flipped)

--   Functional : ∀ {e} → (A → A → Type e) → Separation-alg A → Type (a ⊔ e)
--   Functional _≈_ rel = let open Separation-alg rel in
--     ∀ {a b c c'} → a ∙ b ≋ c → a ∙ b ≋ c' → c ≈ c'

--   -- a ∸ (b ∩ c) ≈ (a ∸ b) ∪ (a ∸ c)
--   DeMorganʳ : (sub cap cup : Separation-alg A) → Type a
--   DeMorganʳ sub cap cup =
--     let open Separation-alg cup renaming (_∙_≋_ to _⊎_≋_)
--         open Separation-alg sub renaming (_∙_≋_ to _∸_≋_)
--         open Separation-alg cap renaming (_∙_≋_ to _∩_≋_)
--     in
--       ∀ {a b c b∩c a-b∩c} → b ∩ c ≋ b∩c → a ∸ b∩c ≋ a-b∩c →
--       ∃₂ λ a-b a-c → (a ∸ b ≋ a-b) × (a ∸ c ≋ a-c) × (a-b ⊎ a-c ≋ a-b∩c)
