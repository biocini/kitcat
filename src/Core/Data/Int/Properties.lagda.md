Properties and lemmas for integers.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Int.Properties where

open import Core.Base
open import Core.Type
open import Core.Kan
open import Core.Transport
open import Core.Data.Dec
open Dec
open import Core.Data.Empty
open import Core.Trait.Decidable using (dec-map)
open import Core.Data.Int.Type
open import Core.Data.Int.Base
open import Core.Data.Nat.Type
open import Core.Data.Nat.Base using (_+_)
import Core.Data.Nat.Properties as Nat

```

Int is a set (h-level 2).

```agda

private
  unpos : Int → Nat
  unpos (pos n)    = n
  unpos (negsuc _) = Z

  unneg : Int → Nat
  unneg (pos _)    = Z
  unneg (negsuc n) = n

  is-pos : Int → Type
  is-pos (pos _)    = ⊤
  is-pos (negsuc _) = ⊥

DecEq-Int : (m n : Int) → Dec (m ≡ n)
DecEq-Int (pos m)    (pos n)    = dec-map (ap pos) (ap unpos) (Nat.DecEq-Nat m n)
DecEq-Int (pos m)    (negsuc n) = no (λ p → subst is-pos p tt)
DecEq-Int (negsuc m) (pos n)    = no (λ p → subst is-pos (sym p) tt)
DecEq-Int (negsuc m) (negsuc n) = dec-map (ap negsuc) (ap unneg) (Nat.DecEq-Nat m n)

set : is-set Int
set = hedberg DecEq-Int
```

## Successor and predecessor commute with addition

The proof runs by induction over the `add`'s own `pos-negsuc` case
split.

```agda

zero-l : ∀ x → add (pos Z) x ≡ x
zero-l (pos n)    = refl
zero-l (negsuc n) = refl

private
  pn-succ : ∀ m n → add.pos-negsuc (S m) n ≡ zsuc (add.pos-negsuc m n)
  pn-succ Z     Z     = refl
  pn-succ (S m) Z     = refl
  pn-succ Z     (S n) = refl
  pn-succ (S m) (S n) = pn-succ m n

  pn-zero : ∀ n → zsuc (add.pos-negsuc n Z) ≡ pos n
  pn-zero Z     = refl
  pn-zero (S n) = refl

  succ-pn : ∀ n m → zsuc (add.pos-negsuc n (S m)) ≡ add.pos-negsuc n m
  succ-pn Z     m     = refl
  succ-pn (S n) Z     = pn-zero n
  succ-pn (S n) (S m) = succ-pn n m

  pred-pos : ∀ n → zpred (pos n) ≡ add.pos-negsuc n Z
  pred-pos Z     = refl
  pred-pos (S n) = refl

  pred-pn : ∀ m n → zpred (add.pos-negsuc (S m) n) ≡ add.pos-negsuc m n
  pred-pn Z     Z     = refl
  pred-pn (S m) Z     = refl
  pred-pn Z     (S n) = refl
  pred-pn (S m) (S n) = pred-pn m n

  pred-pn-r : ∀ n m → zpred (add.pos-negsuc n m) ≡ add.pos-negsuc n (S m)
  pred-pn-r Z     m     = refl
  pred-pn-r (S n) Z     = pred-pos n
  pred-pn-r (S n) (S m) = pred-pn-r n m

add-succ : ∀ m n → add (zsuc m) n ≡ zsuc (add m n)
add-succ (pos m)        (pos n)    = refl
add-succ (pos m)        (negsuc n) = pn-succ m n
add-succ (negsuc Z)     (pos n)    = sym (pn-zero n)
add-succ (negsuc Z)     (negsuc n) = refl
add-succ (negsuc (S m)) (pos n)    = sym (succ-pn n m)
add-succ (negsuc (S m)) (negsuc n) = refl

add-pred : ∀ m n → add (zpred m) n ≡ zpred (add m n)
add-pred (pos Z)     (pos n)    = sym (pred-pos n)
add-pred (pos Z)     (negsuc n) = refl
add-pred (pos (S m)) (pos n)    = refl
add-pred (pos (S m)) (negsuc n) = sym (pred-pn m n)
add-pred (negsuc m)  (pos n)    = sym (pred-pn-r n m)
add-pred (negsuc m)  (negsuc n) = refl

```

## The difference of naturals is a homomorphism

`_⊖_` commutes with successor and predecessor, and turns pointwise
addition into `add`.

```agda

⊖-suc : ∀ a b → (S a ⊖ b) ≡ zsuc (a ⊖ b)
⊖-suc a     Z         = refl
⊖-suc Z     (S Z)     = refl
⊖-suc Z     (S (S b)) = refl
⊖-suc (S a) (S b)     = ⊖-suc a b

⊖-pred : ∀ a b → (a ⊖ S b) ≡ zpred (a ⊖ b)
⊖-pred Z     Z     = refl
⊖-pred Z     (S b) = refl
⊖-pred (S a) Z     = refl
⊖-pred (S a) (S b) = ⊖-pred a b

⊖-hom : ∀ a b c d → add (a ⊖ b) (c ⊖ d) ≡ ((a + c) ⊖ (b + d))
⊖-hom Z     Z         c d = zero-l (c ⊖ d)
⊖-hom (S a) Z         c d =
  add-succ (pos a) (c ⊖ d) ∙ ap zsuc (⊖-hom a Z c d)
  ∙ sym (⊖-suc (a + c) d)
⊖-hom Z     (S Z)     c d =
  add-pred (pos Z) (c ⊖ d) ∙ ap zpred (zero-l (c ⊖ d)) ∙ sym (⊖-pred c d)
⊖-hom Z     (S (S b)) c d =
  add-pred (negsuc b) (c ⊖ d) ∙ ap zpred (⊖-hom Z (S b) c d)
  ∙ sym (⊖-pred c (S (b + d)))
⊖-hom (S a) (S b)     c d = ⊖-hom a b c d

cancel-l : ∀ k a b → ((k + a) ⊖ (k + b)) ≡ (a ⊖ b)
cancel-l Z     a b = refl
cancel-l (S k) a b = cancel-l k a b

⊖-balance : ∀ a b c d → a + d ≡ (c + b) → (a ⊖ b) ≡ (c ⊖ d)
⊖-balance a b c d e =
    sym (cancel-l d a b)
  ∙ ap (_⊖ (d + b)) (Nat.add.comm d a)
  ∙ ap (_⊖ (d + b)) e
  ∙ (λ i → Nat.add.comm c b i ⊖ Nat.add.comm d b i)
  ∙ cancel-l b c d

```
