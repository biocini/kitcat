Ported from [ternary.agda](https://github.com/ajrouvoet/ternary.agda) (Andreas van Babel / Pouzet), `src/Relation/Ternary/Core.agda`.

A ternary (homogeneous) relation `Rel₃` over a carrier, together with the
separation-logic connectives it induces: the partial product `_✴_`
(separating conjunction) and the partial exponent / wand `_─✴_`. Defining a
`Rel₃` also yields, for free, a preorder `_≤_` (the extension order) and the
"being separated" relation `_◆_`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Ternary.Core where

open import Core.Type using (Type; Level; 0ℓ; _⊔_; _₊; id; const; Unit)
open import Core.Base using (_≡_; refl; sym)
open import Core.Transport.J using (subst)
open import Core.Data.Sigma using (Sigma; _,_; fst; snd; _×_; Σ-syntax)
open import Core.Data.List using (List; []; _∷_)
open import Lib.Relation.Unary hiding (_∪_; _∩_)
open import Lib.Relation.Binary using (Rel)

module _ {a} {A : Type a} where

  -- Existential over the carrier (kitcat has no built-in ∃).
  ∃ : ∀ {b} → (A → Type b) → Type (a ⊔ b)
  ∃ = Sigma A

  -- Anonymous existential witness: provide only the body, the point is inferred.
  infixr 0 -,
  -, : ∀ {b} {B : A → Type b} → {x : A} → B x → Sigma A B
  -, {x = x} y = x , y

  ∃₂ : ∀ {c} → (A → A → Type c) → Type (a ⊔ c)
  ∃₂ P = ∃ λ a → ∃ λ b → P a b

  -- A predicate that respects an equivalence relation.
  record Respect {e p} (_≈_ : A → A → Type e) (P : Pred A p) : Type (a ⊔ e ⊔ p) where
    no-eta-equality
    field
      coe : P Respects _≈_
  {-# INLINE Respect.constructor #-}

  -- A point is unique (up to ≈) when equality follows from relatedness.
  record IsUnique {e} (_≈_ : A → A → Type e) (el : A) : Type (a ⊔ e) where
    no-eta-equality
    field
      unique : ∀ {x} → el ≈ x → el ≡ x

    instance unique-respects : Respect _≈_ (｛ el ｝)
    Respect.coe unique-respects eq px =
      unique (subst (λ z → z ≈ _) (sym px) eq)
  {-# INLINE IsUnique.constructor #-}

  instance unique-≡ : ∀ {el} → IsUnique _≡_ el
  IsUnique.unique unique-≡ eq = eq

  open Respect ⦃ ... ⦄ public
  open IsUnique ⦃ ... ⦄ public

module _ {a} {A : Type a} where

  -- The always-true predicate (polymorphic in its level).
  True : ∀ {ℓ} → Pred A ℓ
  True {ℓ} = λ _ → Unit {ℓ}

-- The ternary relation itself.
record Rel₃ {a} (A : Type a) : Type (a ₊) where

  field
    _∙_≣_ : (Φ₁ Φ₂ : A) → Pred A a

  -- We can see the three-point relation as a predicate on the carrier.
  _∙_ = _∙_≣_

  -- Concise notation for "being separated": a pair witnesses the whole.
  _◆_ : A → A → Type a
  Φ₁ ◆ Φ₂ = ∃ λ Φ → Φ₁ ∙ Φ₂ ≣ Φ

  whole : ∀ {Φ₁ Φ₂} → Φ₁ ◆ Φ₂ → A
  whole = fst

  -- Buy one, get a preorder for free: the extension order.
  _≤_ : Rel A a
  Φ₁ ≤ Φ = ∃ λ Φ₂ → Φ₁ ∙ Φ₂ ≣ Φ

  {- Partial products over the relation -}

  infixr 10 _∙⟨_⟩_
  record Conj {p q} (P : Pred A p) (Q : ∀ {Φ} → P Φ → Pred A q) Φ : Type (p ⊔ q ⊔ a) where
    no-eta-equality
    pattern
    constructor _∙⟨_⟩_
    field
      {Φₗ Φᵣ} : A

      px  : P Φₗ
      sep : Φₗ ∙ Φᵣ ≣ Φ
      qx  : Q px Φᵣ

  infixr 9 Σ✴-syntax
  Σ✴-syntax
    : ∀ {p q} (P : Pred A p) (Q : ∀ {Φ} → P Φ → Pred A q) → Pred A (p ⊔ q ⊔ a)
  Σ✴-syntax = Conj

  syntax Σ✴-syntax A (λ x → B) = Σ[ x ∈ A ]✴ B

  infixr 9 _✴_
  _✴_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a)
  P ✴ Q = Σ[ x ∈ P ]✴ Q

  {- Partial exponents over the relation -}

  record Wand {b p q} {B : Type b}
    (P : Pred B p)
    (j : B → A)
    (Q : ∀ {Φ} → P Φ → Pred A q)
    (Φᵢ : A) : Type (p ⊔ q ⊔ a ⊔ b) where
    no-eta-equality

    constructor arr

    infixl 10 _⟨_⟩_
    field
      _⟨_⟩_ : ∀ {Φₚ Φ} → Φᵢ ∙ j Φₚ ≣ Φ → (px : P Φₚ) → Q px Φ
  {-# INLINE Wand.constructor #-}

  open Wand public

  infixr 8 _─✴[_]_
  _─✴[_]_
    : ∀ {p q b} {B : Type b} (P : Pred B p) (j : B → A) (Q : Pred A q)
    → Pred A (p ⊔ q ⊔ a ⊔ b)
  (P ─✴[ j ] Q) = Wand P j (const Q)

  infixr 8 Π✴-syntax
  Π✴-syntax
    : ∀ {p q} (P : Pred A p) (Q : ∀ {Φ} → P Φ → Pred A q) → Pred A (p ⊔ q ⊔ a)
  Π✴-syntax P Q = Wand P id Q
  syntax Π✴-syntax P (λ x → Q) = Π[ x ∈ P ]✴ Q

  -- The non-separating dependent function space.
  infixr 8 Π⇒-syntax
  Π⇒-syntax
    : ∀ {p q} (P : Pred A p) (Q : ∀ {Φ} → P Φ → Pred A q) → Pred A (p ⊔ q)
  Π⇒-syntax P Q = λ Φ → (px : P Φ) → Q px Φ
  syntax Π⇒-syntax P (λ x → Q) = Π[ x ∈ P ]⇒ Q

  infixr 8 _─✴_
  _─✴_ : ∀ {p q} (P : Pred A p) (Q : Pred A q) → Pred A (p ⊔ q ⊔ a)
  P ─✴ Q = Wand P id (const Q)

  module _ {p q} {P : Pred A p} {Q : Pred A q} where

    apply : ∀[ (P ─✴ Q) ✴ P ⇒ Q ]
    apply (f ∙⟨ σ ⟩ px) = f ⟨ σ ⟩ px

{- Rel morphisms -}
module _ {a} {A : Type a} where

  _flipped : Rel₃ A → Rel₃ A
  Rel₃._∙_≣_ (rel flipped) = λ Φ₁ Φ₂ Φ → let open Rel₃ rel in Φ₂ ∙ Φ₁ ≣ Φ

{- Properties of ternary relations -}
module _ {a} {A : Type a} where

  Commutative : Rel₃ A → Type a
  Commutative rel = let open Rel₃ rel
    in ∀ {a b ab : A} → a ∙ b ≣ ab → b ∙ a ≣ ab

  RightAssoc : Rel₃ A → Type a
  RightAssoc rel = let open Rel₃ rel in
    ∀ {a b ab c abc}
      → a ∙ b ≣ ab → ab ∙ c ≣ abc
      → ∃ λ bc → a ∙ bc ≣ abc × b ∙ c ≣ bc

  LeftAssoc : Rel₃ A → Type a
  LeftAssoc rel = let open Rel₃ rel in
    ∀ {a bc b c abc}
      → a ∙ bc ≣ abc → b ∙ c ≣ bc
      → ∃ λ ab → a ∙ b ≣ ab × ab ∙ c ≣ abc

  -- (a - b) - c ≈> a - (b + c)
  RightAssoc′ : (add : Rel₃ A) (sub : Rel₃ A) → Type a
  RightAssoc′ add sub =
    let open Rel₃ add renaming (_∙_≣_ to _+_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
    in ∀ {a₁ a₂ a₃ a₁-₂ a₀ a₂+₃} →
         a₁ ∸ a₂ ≣ a₁-₂ → a₁-₂ ∸ a₃ ≣ a₀ → a₂ + a₃ ≣ a₂+₃ →
         a₁ ∸ a₂+₃ ≣ a₀

  -- a - (b + c) ≈> (a - b) - c
  LeftAssoc′ : (add : Rel₃ A) (sub : Rel₃ A) → Type a
  LeftAssoc′ add sub =
    let open Rel₃ add renaming (_∙_≣_ to _+_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
    in ∀ {a₁ a₂ a₃ a₂+₃ a₀} →
         a₁ ∸ a₂+₃ ≣ a₀ → a₂ + a₃ ≣ a₂+₃ →
         ∃ λ a₁-₂ →
           a₁ ∸ a₂ ≣ a₁-₂ × a₁-₂ ∸ a₃ ≣ a₀

  -- (a ∪ b) - c => (a - c) ∪ (b - c): sub distributes over cup, rightward.
  _DistribOverᵣ_ : (sub : Rel₃ A) (cup : Rel₃ A) → Type a
  _DistribOverᵣ_ sub cup =
    let open Rel₃ cup renaming (_∙_≣_ to _⊎_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
    in ∀ {a b c a∪b d}
      → a ⊎ b ≣ a∪b → a∪b ∸ c ≣ d
      → ∃₂ λ a-c b-c → a ∸ c ≣ a-c × b ∸ c ≣ b-c × a-c ⊎ b-c ≣ d

  -- (a ∪ b) - c <= (a - c) ∪ (b - c): leftward distributivity.
  _DistribOverₗ_ : (sub : Rel₃ A) → (cup : Rel₃ A) → Type a
  _DistribOverₗ_ sub cup =
    let open Rel₃ cup renaming (_∙_≣_ to _⊎_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
    in ∀ {a b c d a-c b-c}
      → a ∸ c ≣ a-c → b ∸ c ≣ b-c → a-c ⊎ b-c ≣ d
      → ∃ λ a∪b → a ⊎ b ≣ a∪b × a∪b ∸ c ≣ d

  LeftIdentity : Rel₃ A → A → Type a
  LeftIdentity rel ε = let open Rel₃ rel in ∀ {Φ} → ε ∙ Φ ≣ Φ

  LeftIdentity⁻ : ∀ {e} → (A → A → Type e) → Rel₃ A → A → Type (a ⊔ e)
  LeftIdentity⁻ _≈_ rel ε = let open Rel₃ rel in ∀ {Φ Φ′} → ε ∙ Φ ≣ Φ′ → Φ ≈ Φ′

  RightIdentity : Rel₃ A → A → Type a
  RightIdentity rel ε = let open Rel₃ rel in ∀ {Φ} → Φ ∙ ε ≣ Φ

  RightIdentity⁻ : ∀ {e} → (A → A → Type e) → Rel₃ A → A → Type (a ⊔ e)
  RightIdentity⁻ _≈_ rel ε = let open Rel₃ rel in ∀ {Φ Φ′} → Φ ∙ ε ≣ Φ′ → Φ ≈ Φ′

  LeftZero : Rel₃ A → A → Type a
  LeftZero rel z = let open Rel₃ rel in ∀ {Φ} → z ∙ Φ ≣ z

  LeftZero⁻ : ∀ {e} → (A → A → Type e) → Rel₃ A → A → Type (a ⊔ e)
  LeftZero⁻ _≈_ rel z = let open Rel₃ rel in ∀ {Φ Φ′} → z ∙ Φ ≣ Φ′ → Φ′ ≈ z

  RightZero : Rel₃ A → A → Type a
  RightZero rel z = let open Rel₃ rel in ∀ {Φ} → Φ ∙ z ≣ z

  RightZero⁻ : ∀ {e} → (A → A → Type e) → Rel₃ A → A → Type (a ⊔ e)
  RightZero⁻ _≈_ rel z = let open Rel₃ rel in ∀ {Φ Φ′} → Φ ∙ z ≣ Φ′ → Φ′ ≈ z

  Idempotent : Rel₃ A → Type a
  Idempotent rel = let open Rel₃ rel in ∀ {Φ} → Φ ∙ Φ ≣ Φ

  Idempotent⁻ : ∀ {e} → (A → A → Type e) → Rel₃ A → Type (a ⊔ e)
  Idempotent⁻ _≈_ rel = let open Rel₃ rel in ∀ {Φ Φ′} → Φ ∙ Φ ≣ Φ′ → Φ ≈ Φ′

  LeftMonotone : ∀ {e} → (A → A → Type e) → Rel₃ A → Type (a ⊔ e)
  LeftMonotone _∼_ rel = let open Rel₃ rel in
    ∀ {Φ₁ Φ₂ Φ Φ₃ Φ′} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₁ ∼ Φ₃ → Φ₃ ∙ Φ₂ ≣ Φ′ → Φ ∼ Φ′

  RightMonotone : ∀ {e} → (A → A → Type e) → Rel₃ A → Type (a ⊔ e)
  RightMonotone _∼_ rel = LeftMonotone _∼_ (rel flipped)

  Functional : ∀ {e} → (A → A → Type e) → Rel₃ A → Type (a ⊔ e)
  Functional _≈_ rel = let open Rel₃ rel in
    ∀ {a b c c'} → a ∙ b ≣ c → a ∙ b ≣ c' → c ≈ c'

  -- a ∸ (b ∩ c) ≈ (a ∸ b) ∪ (a ∸ c)
  DeMorganʳ : (sub cap cup : Rel₃ A) → Type a
  DeMorganʳ sub cap cup =
    let open Rel₃ cup renaming (_∙_≣_ to _⊎_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
        open Rel₃ cap renaming (_∙_≣_ to _∩_≣_)
    in
      ∀ {a b c b∩c a-b∩c} → b ∩ c ≣ b∩c → a ∸ b∩c ≣ a-b∩c →
      ∃₂ λ a-b a-c → (a ∸ b ≣ a-b) × (a ∸ c ≣ a-c) × (a-b ⊎ a-c ≣ a-b∩c)


module _ {a} {A : Type a} where

  One : A → Pred (List A) a
  One t = ｛ t ∷ [] ｝

```
