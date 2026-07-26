```agda
{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Lib.Data where

open import Core.Type
open import Lib.Literals

```

Sigma

```

open import Agda.Builtin.Sigma public
  renaming ( Σ to Sigma
           ; _,_ to infixr 4 _,_ )
  using ( fst; snd; module Σ ) -- keep the module the same name, it works

Σ : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Σ {A = A} B = Sigma A B

{-# INLINE Σ #-}
{-# INLINE _,_ #-}
{-# DISPLAY Sigma _ B = Σ B #-}

```

Empty and Unit

```

data 𝟘 {u} : Type u where
record 𝟙 {u} : Type u where instance constructor tt

{-# BUILTIN UNIT 𝟙 #-}

```

Plus

```

infixr 1 _⊎_

data _⊎_ {u v} (A : Type u) (B : Type v) : Type (u ⊔ v) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

```

Nat

```agda
open import Agda.Builtin.Nat public
  renaming ( _<_ to _<₂_
           ; _+_ to _+ℕ_
           ; _*_ to _*ℕ_
           ; _-_ to _-ℕ_
           )

infix 7 _≤ℕ_ _<ℕ_

data _≤ℕ_ : Nat → Nat → Type where
  instance 0≤x : ∀ {x} → zero ≤ℕ x
  s≤s : ∀ {x y} → x ≤ℕ y → suc x ≤ℕ suc y

open _≤ℕ_ public

_<ℕ_ : Nat → Nat → Type
m <ℕ n = suc m ≤ℕ n

instance
  Number-Nat : Number Nat
  Number-Nat .Number.Constraint = λ _ → 𝟙
  Number-Nat .Number.fromNat n = n

  0<suc : ∀ {n} → zero <ℕ suc n
  0<suc = s≤s 0≤x

```
