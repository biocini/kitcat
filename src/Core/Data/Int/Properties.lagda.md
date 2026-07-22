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
open import Core.Data.Nat.Type
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
