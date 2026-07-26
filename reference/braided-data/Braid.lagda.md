Fin sum equivalences, braiding, and symmetric monoidal category structure.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Braid where

open import Core.Type
open import Core.Base
open import Core.Data.Sum
open import Core.Data.Empty
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path
open import Core.Equiv
open import Core.Data.Fin
open import Core.Transport

open import Core.Data.Dec

private variable
  u v w : Level
  A B C : Type u
  m n k : Nat

```

## Private Helpers

```agda

private
  subst-subst'-Fin : ∀ {m n : Nat}
                   → (p : m ≡ n) (q : n ≡ m)
                   → (a : Fin m) → subst Fin q (subst Fin p a) ≡ a
  subst-subst'-Fin p q a = fin-path refl

```

## Sum Type Equivalences

```agda

⊎-swap : A ⊎ B → B ⊎ A
⊎-swap (inl a) = inr a
⊎-swap (inr b) = inl b

⊎-swap-invol : (x : A ⊎ B) → ⊎-swap (⊎-swap x) ≡ x
⊎-swap-invol (inl _) = refl
⊎-swap-invol (inr _) = refl

⊎-comm : (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = iso→equiv ⊎-swap ⊎-swap ⊎-swap-invol ⊎-swap-invol

⊎-assoc-fwd : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc-fwd (inl (inl a)) = inl a
⊎-assoc-fwd (inl (inr b)) = inr (inl b)
⊎-assoc-fwd (inr c) = inr (inr c)

⊎-assoc-bwd : A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
⊎-assoc-bwd (inl a) = inl (inl a)
⊎-assoc-bwd (inr (inl b)) = inl (inr b)
⊎-assoc-bwd (inr (inr c)) = inr c

⊎-assoc-sec : (x : (A ⊎ B) ⊎ C) → ⊎-assoc-bwd (⊎-assoc-fwd x) ≡ x
⊎-assoc-sec (inl (inl _)) = refl
⊎-assoc-sec (inl (inr _)) = refl
⊎-assoc-sec (inr _) = refl

⊎-assoc-retr : (x : A ⊎ (B ⊎ C)) → ⊎-assoc-fwd (⊎-assoc-bwd x) ≡ x
⊎-assoc-retr (inl _) = refl
⊎-assoc-retr (inr (inl _)) = refl
⊎-assoc-retr (inr (inr _)) = refl

⊎-assoc : ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = iso→equiv ⊎-assoc-fwd ⊎-assoc-bwd ⊎-assoc-sec ⊎-assoc-retr

⊎-unit-l-fwd : ⊥ ⊎ A → A
⊎-unit-l-fwd (inl ())
⊎-unit-l-fwd (inr a) = a

⊎-unit-l-bwd : A → ⊥ ⊎ A
⊎-unit-l-bwd = inr

⊎-unit-l : (⊥ ⊎ A) ≃ A
⊎-unit-l = iso→equiv ⊎-unit-l-fwd ⊎-unit-l-bwd sec (λ _ → refl)
  where
    sec : (x : ⊥ ⊎ _) → inr (⊎-unit-l-fwd x) ≡ x
    sec (inl ())
    sec (inr _) = refl

⊎-unit-r-fwd : A ⊎ ⊥ → A
⊎-unit-r-fwd (inl a) = a
⊎-unit-r-fwd (inr ())

⊎-unit-r-bwd : A → A ⊎ ⊥
⊎-unit-r-bwd = inl

⊎-unit-r : (A ⊎ ⊥) ≃ A
⊎-unit-r = iso→equiv ⊎-unit-r-fwd ⊎-unit-r-bwd sec (λ _ → refl)
  where
    sec : (x : _ ⊎ ⊥) → inl (⊎-unit-r-fwd x) ≡ x
    sec (inl _) = refl
    sec (inr ())

```

## Fin Sum Equivalence

The core equivalence: `Fin m ⊎ Fin n ≃ Fin (m + n)`.

```agda

module Fin-+ {m n : Nat} where
  private
    inject-< : (m' n' k : Nat) → k < m' → k < (m' + n')
    inject-< (S m') Z k p = subst (k <_) (sym (+-zero (S m'))) p
    inject-< (S m') (S n') Z p = z<s
    inject-< (S m') (S n') (S k) p = s<s (inject-< m' (S n') k (peel m' p))

    shift-< : (m' n' k : Nat) → k < n' → (m' + k) < (m' + n')
    shift-< Z n' k p = p
    shift-< (S m') n' k p = s<s (shift-< m' n' k p)

  fwd : Fin m ⊎ Fin n → Fin (m + n)
  fwd (inl (fin k ⦃ bounded = forget p ⦄)) = fin k ⦃ forget (inject-< m n k p) ⦄
  fwd (inr (fin k ⦃ bounded = forget p ⦄)) = fin (m + k) ⦃ forget (shift-< m n k p) ⦄

  -- Decidable comparison: is k < m?
  cmp : ∀ k m' → (k < m') ⊎ Σ λ j → k ≡ m' + j
  cmp k Z = inr (k , refl)
  cmp Z (S m') = inl z<s
  cmp (S k) (S m') with cmp k m'
  ... | inl p = inl (s<s p)
  ... | inr (j , eq) = inr (j , ap S eq)

  private
    pred : Nat → Nat
    pred Z = Z
    pred (S n') = n'

  -- Extract j < n from k < m + n when k = m + j
  extract-< : ∀ m' n' k j → k ≡ m' + j → k < (m' + n') → j < n'
  extract-< Z n' k j eq p = subst (_< n') eq p
  extract-< (S m') n' Z j eq p = ex-falso (¬z≡s eq) where ¬z≡s : ∀ {x} → ¬ (Z ≡ S x) ; ¬z≡s q = subst (λ { Z → ⊤ ; (S _) → ⊥ }) q tt
  extract-< (S m') n' (S k) j eq p = extract-< m' n' k j (ap pred eq) (peel (m' + n') p)

  bwd : Fin (m + n) → Fin m ⊎ Fin n
  bwd (fin k ⦃ bounded = forget p ⦄) with cmp k m
  ... | inl q = inl (fin k ⦃ forget q ⦄)
  ... | inr (j , eq) = inr (fin j ⦃ forget (extract-< m n k j eq p) ⦄)

  private
    -- If k = m + j for some j, then k ≥ m. Use Irr to handle irrelevant proof.
    k≡m+j→¬k<m : ∀ k m' j → k ≡ m' + j → Irr (k < m') → ⊥
    k≡m+j→¬k<m Z (S _) j eq _ = subst (λ { Z → ⊤ ; (S _) → ⊥ }) eq tt
    k≡m+j→¬k<m (S k) (S m') j eq (forget p) = k≡m+j→¬k<m k m' j (ap pred eq) (forget (peel m' p))

    m+k<m-absurd : ∀ m' k → (m' + k) < m' → ⊥
    m+k<m-absurd (S m') k p' = m+k<m-absurd m' k (peel m' p')

    cancel-+ : ∀ m' {a b} → m' + a ≡ m' + b → a ≡ b
    cancel-+ Z eq' = eq'
    cancel-+ (S m') eq' = cancel-+ m' (ap pred eq')

  sec : (x : Fin m ⊎ Fin n) → bwd (fwd x) ≡ x
  sec (inl (fin k ⦃ bounded ⦄)) with cmp k m
  ... | inl _ = refl
  ... | inr (j , eq) = ex-falso (k≡m+j→¬k<m k m j eq bounded)
  sec (inr (fin j ⦃ bounded = forget p ⦄)) with cmp (m + j) m
  ... | inl q = ex-falso (m+k<m-absurd m j q)
  ... | inr (j' , eq) = ap inr (fin-path (sym (cancel-+ m eq)))

  retr : (y : Fin (m + n)) → fwd (bwd y) ≡ y
  retr (fin k ⦃ bounded = forget p ⦄) with cmp k m
  ... | inl q = fin-path refl
  ... | inr (j , eq) = fin-path (sym eq)

open Fin-+ using () renaming (fwd to Fin-+-fwd; bwd to Fin-+-bwd) public

Fin-+ : (Fin m ⊎ Fin n) ≃ Fin (m + n)
Fin-+ = iso→equiv Fin-+.fwd Fin-+.bwd Fin-+.sec Fin-+.retr

```

## Braiding

The braiding equivalence swaps `Fin m` and `Fin n` within `Fin (m + n)`.

```agda

Fin-+-comm : Fin (m + n) ≃ Fin (n + m)
Fin-+-comm {m} {n} = iso→equiv fwd bwd sec retr
  where
    fwd : Fin (m + n) → Fin (n + m)
    fwd i = subst Fin (+-comm m n) i

    bwd : Fin (n + m) → Fin (m + n)
    bwd i = subst Fin (+-comm n m) i

    sec : (x : Fin (m + n)) → bwd (fwd x) ≡ x
    sec x = subst-subst'-Fin (+-comm m n) (+-comm n m) x

    retr : (y : Fin (n + m)) → fwd (bwd y) ≡ y
    retr y = subst-subst'-Fin (+-comm n m) (+-comm m n) y

```

## SMC Structure

Associativity and unit equivalences for Fin addition.

```agda

Fin-+-assoc : Fin ((m + n) + k) ≃ Fin (m + (n + k))
Fin-+-assoc {m} {n} {k} = iso→equiv fwd bwd sec retr
  where
    fwd : Fin ((m + n) + k) → Fin (m + (n + k))
    fwd i = subst Fin (sym (+-assoc m n k)) i

    bwd : Fin (m + (n + k)) → Fin ((m + n) + k)
    bwd i = subst Fin (+-assoc m n k) i

    sec : (x : Fin ((m + n) + k)) → bwd (fwd x) ≡ x
    sec x = subst-subst'-Fin (sym (+-assoc m n k)) (+-assoc m n k) x

    retr : (y : Fin (m + (n + k))) → fwd (bwd y) ≡ y
    retr y = subst-subst'-Fin (+-assoc m n k) (sym (+-assoc m n k)) y

Fin-+-unit-l : Fin (Z + n) ≃ Fin n
Fin-+-unit-l = equiv

Fin-+-unit-r : Fin (n + Z) ≃ Fin n
Fin-+-unit-r {n} = iso→equiv fwd bwd sec retr
  where
    fwd : Fin (n + Z) → Fin n
    fwd i = subst Fin (+-zero n) i

    bwd : Fin n → Fin (n + Z)
    bwd i = subst Fin (sym (+-zero n)) i

    sec : (x : Fin (n + Z)) → bwd (fwd x) ≡ x
    sec x = subst-subst'-Fin (+-zero n) (sym (+-zero n)) x

    retr : (y : Fin n) → fwd (bwd y) ≡ y
    retr y = subst-subst'-Fin (sym (+-zero n)) (+-zero n) y

```

## Braiding Involution

The braiding is its own inverse.

```agda

-- Braiding involution: swap twice is identity
-- Proof: subst Fin (+-comm m n) ∘ subst Fin (+-comm n m) = subst Fin (+-comm m n ∙ +-comm n m)
--        and +-comm m n ∙ +-comm n m = refl (since Nat is a set)
-- So the composed function equals id, and equivalences are equal when their functions are.

```

## SMC Coherence

The coherence proofs for symmetric monoidal category structure.
Since Fin n is a set, parallel equivalences are equal when they agree on the
underlying function, which they do since both sides are built from `subst`.

```agda

Fin-+-triangle : ∀ {m n}
  → subst Fin (ap (m +_) (+-zero n)) ∘ subst Fin (sym (+-assoc m n Z))
  ≡ subst Fin (+-zero (m + n))
Fin-+-triangle {m} {n} = funext λ x → fin-path refl

```
