Properties and lemmas for natural numbers.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Nat.Properties where

open import Core.Base
open import Core.Type
open import Core.Kan
open import Core.Transport
open import Core.Data.Dec
open Dec
open import Core.Data.Empty
open import Core.Data.Sum.Type
open import Core.Data.Bool.Base using (So)
open import Core.Data.Nat.Type
open import Core.Data.Nat.Base

private variable
  m n k : Nat

```

Ordering lemmas.

```agda

module lt where
  open Core.Data.Nat.Base using (s<s) public

  z<s : Z < S n
  z<s {n = Z} = suc
  z<s {n = S n} = step z<s

  peel : ∀ n → S m < S n → m < n
  peel (S m) suc = suc
  peel (S n) (step p) = step (peel n p)

  ¬n<z : ∀ {n} → ¬ (n < Z)
  ¬n<z ()

  cat : ∀ {k} → m < n → n < k → m < k
  cat {k = Z} p q = ex-falso (¬n<z q)
  cat {k = S k} p suc = step p
  cat {k = S k} p (step q) = step (cat p q)

  irrefl : ∀ {n} → n < n → ⊥
  irrefl {n = S n} (step p) = irrefl (peel n (step p))

  <→z< : ∀ {i j} → i < j → Z < j
  <→z< {j = S _} _ = z<s

  instance
    z<s-irr : ∀ {n} → Irr (Z < (S n))
    z<s-irr = forget z<s

lt-le-cat : ∀ {k m n} → k < m → m ≤ n → k < n
lt-le-cat p suc = p
lt-le-cat p (step q) = lt.cat p q

le-lt-cat : ∀ {k m n} → k ≤ m → m < n → k < n
le-lt-cat suc q = q
le-lt-cat (step p) q = lt.cat p q

lt-le-absurd : ∀ {a b} → a < b → b ≤ a → ⊥
lt-le-absurd p q = lt.irrefl (lt-le-cat p q)

le-lt-pred : ∀ {j i k} → j ≤ i → i < k → j ≤ pred k
le-lt-pred {k = S k'} ji ik = lt-le-cat ji (s<s ik)

cmp : (m n : Nat) → (m < S n) ⊎ (n < m)
cmp Z _ = inl lt.z<s
cmp (S m) Z = inr lt.z<s
cmp (S m) (S n) with cmp m n
... | inl p = inl (s<s p)
... | inr q = inr (s<s q)

module le where
  rx : n ≤ n
  rx = suc

  cat : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  cat suc = id
  cat (step p) = lt.cat p

  pred-mono : ∀ {a b} → a ≤ b → pred a ≤ pred b
  pred-mono {a = Z} _ = lt.z<s
  pred-mono {a = S a} {b = Z} p = ex-falso (lt-le-absurd lt.z<s p)
  pred-mono {a = S a} {b = S b} p = lt.peel (S b) p

```

The order relations are decidable, and antisymmetry of `≤` turns a pair of
bounds into an identity of numbers.

```agda

≤-antisym : m ≤ n → n ≤ m → m ≡ n
≤-antisym suc       _ = refl
≤-antisym (step p)  q = ex-falso (lt-le-absurd p q)

<-dec : (m n : Nat) → Dec (m < n)
<-dec m n with cmp n m
... | inl n≤m = no λ m<n → lt-le-absurd m<n n≤m
... | inr m<n = yes m<n

≤-dec : (m n : Nat) → Dec (m ≤ n)
≤-dec m n = <-dec m (S n)

```

Arithmetic lemmas.

```agda

module add where
  unitr : ∀ n → n + Z ≡ n
  unitr Z = refl
  unitr (S n) = ap S (unitr n)

  +suc : ∀ m n → m + S n ≡ S (m + n)
  +suc Z n = refl
  +suc (S m) n = ap S (+suc m n)

  comm : ∀ m n → m + n ≡ n + m
  comm Z n = sym (unitr n)
  comm (S m) n = ap S (comm m n) ∙ sym (+suc n m)

  assoc : ∀ m n k → m + (n + k) ≡ (m + n) + k
  assoc Z n k = refl
  assoc (S m) n k = ap S (assoc m n k)

distr : ∀ m n k → (m + n) * k ≡ m * k + n * k
distr Z n k = refl
distr (S m) n k = ap (k +_) (distr m n k)
  ∙ add.assoc k (m * k) (n * k)

module mul where
  zeror : ∀ n → n * Z ≡ Z
  zeror Z = refl
  zeror (S n) = zeror n

  *suc : ∀ m n → m * S n ≡ m + m * n
  *suc Z n = refl
  *suc (S m) n =
    ap (S n +_) (*suc m n)
    ∙ ap S (add.assoc n m (m * n)
      ∙ ap (_+ m * n) (add.comm n m)
      ∙ sym (add.assoc m n (m * n)))

  comm : ∀ m n → m * n ≡ n * m
  comm Z n = sym (zeror n)
  comm (S m) n = ap (n +_) (comm m n) ∙ sym (*suc n m)

  assoc : ∀ m n k → m * (n * k) ≡ (m * n) * k
  assoc Z n k = refl
  assoc (S m) n k = ap (n * k +_) (assoc m n k)
    ∙ sym (distr n (m * n) k)

  unitl : ∀ n → S Z * n ≡ n
  unitl n = add.unitr n

  unitr : ∀ n → n * S Z ≡ n
  unitr n = *suc n Z ∙ ap (n +_) (zeror n) ∙ add.unitr n

distl : ∀ m n k → m * (n + k) ≡ m * n + m * k
distl m n k =
  mul.comm m (n + k)
  ∙ distr n k m
  ∙ ap (_+ k * m) (mul.comm n m)
  ∙ ap (m * n +_) (mul.comm k m)

module max where
  unitl : max Z n ≡ n
  unitl = refl

  unitr : max n Z ≡ n
  unitr {n = Z}   = refl
  unitr {n = S n} = refl

  comm : ∀ m n → max m n ≡ max n m
  comm Z     Z     = refl
  comm Z     (S n) = refl
  comm (S m) Z     = refl
  comm (S m) (S n) = ap S (comm m n)

  assoc : ∀ m n k → max (max m n) k ≡ max m (max n k)
  assoc Z     n     k     = refl
  assoc (S m) Z     k     = refl
  assoc (S m) (S n) Z     = refl
  assoc (S m) (S n) (S k) = ap S (assoc m n k)

  idem : ∀ n → max n n ≡ n
  idem Z     = refl
  idem (S n) = ap S (idem n)

  ≤l : ∀ n m → n ≤ max n m
  ≤l Z     m     = lt.z<s
  ≤l (S n) Z     = suc
  ≤l (S n) (S m) = s<s (≤l n m)

  ≤r : ∀ n m → m ≤ max n m
  ≤r Z     m     = suc
  ≤r (S n) Z     = lt.z<s
  ≤r (S n) (S m) = s<s (≤r n m)

```

`_≤ᵇ_` and `_==ᵇ_` decide the order and equality relations. Each
boolean check is sound and complete against its propositional
counterpart.

```agda

≤ᵇ-sound : ∀ m n → So (m ≤ᵇ n) → m ≤ n
≤ᵇ-sound Z     n     s = lt.z<s
≤ᵇ-sound (S m) Z     s = ex-falso s
≤ᵇ-sound (S m) (S n) s = s<s (≤ᵇ-sound m n s)

≤ᵇ-complete : ∀ m n → m ≤ n → So (m ≤ᵇ n)
≤ᵇ-complete Z     n     p = tt
≤ᵇ-complete (S m) Z     p = lt.¬n<z (lt.peel Z p)
≤ᵇ-complete (S m) (S n) p = ≤ᵇ-complete m n (lt.peel (S n) p)

==ᵇ-sound : ∀ m n → So (m ==ᵇ n) → m ≡ n
==ᵇ-sound Z     Z     s = refl
==ᵇ-sound Z     (S n) s = ex-falso s
==ᵇ-sound (S m) Z     s = ex-falso s
==ᵇ-sound (S m) (S n) s = ap S (==ᵇ-sound m n s)

==ᵇ-refl : ∀ m → So (m ==ᵇ m)
==ᵇ-refl Z     = tt
==ᵇ-refl (S m) = ==ᵇ-refl m

==ᵇ-complete : ∀ m n → m ≡ n → So (m ==ᵇ n)
==ᵇ-complete m n p = subst (λ k → So (m ==ᵇ k)) p (==ᵇ-refl m)

```

`a` is below `a + b`, and monus recovers `max` when added back.

```agda

le-plus : ∀ a b → a ≤ (a + b)
le-plus Z     b = lt.z<s
le-plus (S a) b = s<s (le-plus a b)

monus-max : ∀ a b → (a - b) + b ≡ max a b
monus-max a     Z     = add.unitr a ∙ sym max.unitr
monus-max Z     (S b) = refl
monus-max (S a) (S b) = add.+suc (a - b) b ∙ ap S (monus-max a b)

```

Nat is a set (h-level 2).

```agda

DecEq-Nat : (m n : Nat) → Dec (m ≡ n)
DecEq-Nat Z Z = yes refl
DecEq-Nat Z (S _) = no (λ p → subst f p tt) where f = λ { Z → ⊤ ; (S _) → ⊥ }
DecEq-Nat (S _) Z = no (λ p → subst f p tt) where f = λ { Z → ⊥ ; (S _) → ⊤ }
DecEq-Nat (S m) (S n) with DecEq-Nat m n
... | yes p = yes (ap S p)
... | no ¬p = no λ q → ¬p (ap pred q)

set : is-set Nat
set = hedberg DecEq-Nat
