Lane Biocini
February 2025

Magmoids and the structures we can characterize within them.

We compile all the definitions into a module meant to instantiate uniform definitions
for any category-like (i.e. magmoidal) structure; we also even have the machinery
for heteromorphisms between structures that only agree in being magmoidal,
see the definitions for functor, adjunctions, nat-trans, etc.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Data.Magmoid

module Cat.Data.Base (M : Magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv renaming (_≃_ to _≃e_)
open import Core.Function.Surjection using (is-surjective)
open import Core.Function.Embedding using (is-embedding)

open Magmoids M public

associator : ∀ {w x y z} → hom w x → hom x y → hom y z → Type h
associator f g h = f ⨾ (g ⨾ h) ≡ (f ⨾ g) ⨾ h
{-# INLINE associator #-}

triangle : ∀ {x y z} → hom x y → hom y z → hom x z → Type h
triangle f g s = f ⨾ g ≡ s

square : ∀ {w x y z} → hom x w → hom x y → hom y z → hom w z → Type h
square f h k g = f ⨾ g ≡ h ⨾ k

is-thunkable : ∀ {w x} → hom w x → Type (o ⊔ h)
is-thunkable {x} f = ∀ {y z} (g : hom x y) (h : hom y z) → associator f g h

is-linear : ∀ {y z} → hom y z → Type (o ⊔ h)
is-linear {y} h = ∀ {w x} (f : hom w x) (g : hom x y) → associator f g h

is-medial : ∀ {x y} → hom x y → Type (o ⊔ h)
is-medial {x} {y} f = ∀ {w z} (g : hom w x) (h : hom y z) → associator g f h

thunkable : ∀ {w x y} → hom w x → hom x y → Type (o ⊔ h)
thunkable {y} f g = ∀ {z} (h : hom y z) → associator f g h

linear : ∀ {x y z} → hom y z → hom x y → Type (o ⊔ h)
linear {x} h g = ∀ {w} (f : hom w x) → associator f g h

associativity : Type (o ⊔ h)
associativity
  = ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z) → associator f g h

_✶_
  : ∀ {x y z} {f f' : hom x y} {g g' : hom y z}
  → f ≡ f' → g ≡ g' → f ⨾ g ≡ f' ⨾ g'
(α ✶ β) i = α i ⨾ β i

_▹_
  : ∀ {x y z} {f f' : hom x y}
  → f ≡ f' → (h : hom y z)
  → (f ⨾ h) ≡ (f' ⨾ h)
γ ▹ h = ap (_⨾ h) γ
infixr 25 _▹_

_◃_
  : ∀ {w x y} (h : hom w x)
  → {f f' : hom x y} → f ≡ f'
  → (h ⨾ f) ≡ (h ⨾ f')
_◃_ h = ap (h ⨾_)
infixl 26 _◃_

nat-sq
  : ∀ {x y z} {f f' : hom x y}
    {g g' : hom y z}
  → (α : f ≡ f') (β : g ≡ g')
  → Square (α ▹ g) (f ◃ β) (α ▹ g') (f' ◃ β)
nat-sq α β i j = α j ⨾ β i

module _ {x y} (f : hom x y) where
  is-left-divisible : Type (o ⊔ h)
  is-left-divisible = ∀ {z} → is-equiv (λ (g : hom y z) → f ⨾ g)

  is-right-divisible : Type (o ⊔ h)
  is-right-divisible = ∀ {w} → is-equiv (λ (h : hom w x) → h ⨾ f)

is-neutral : ∀ {x y} → hom x y → Type (o ⊔ h)
is-neutral {x} {y} f = is-left-divisible f × is-right-divisible f

is-neutral-is-prop
  : ∀ {x y} (f : hom x y) → is-prop (is-neutral f)
is-neutral-is-prop f = is-prop-×
  (Πi-is-prop λ _ → is-equiv-is-prop _) (Πi-is-prop λ _ → is-equiv-is-prop _)
```

## Divisibility and cancellability

Neutrality decomposes into two independent conditions: divisibility
(composition maps are surjective — division solutions exist) and
cancellability (composition maps are embeddings — division solutions
are unique). This follows from the general HoTT fact that a map is
an equivalence iff it is both surjective and an embedding.

```agda
module _ {x y} (f : hom x y) where
  has-left-division : Type (o ⊔ h)
  has-left-division =
    ∀ {z} → is-surjective (λ (g : hom y z) → f ⨾ g)

  has-right-division : Type (o ⊔ h)
  has-right-division =
    ∀ {w} → is-surjective (λ (h : hom w x) → h ⨾ f)

is-divisible : ∀ {x y} → hom x y → Type (o ⊔ h)
is-divisible f = has-left-division f × has-right-division f

module _ {x y} (f : hom x y) where
  is-left-cancellable : Type (o ⊔ h)
  is-left-cancellable =
    ∀ {z} → is-embedding (λ (g : hom y z) → f ⨾ g)

  is-right-cancellable : Type (o ⊔ h)
  is-right-cancellable =
    ∀ {w} → is-embedding (λ (h : hom w x) → h ⨾ f)

is-cancellable : ∀ {x y} → hom x y → Type (o ⊔ h)
is-cancellable f = is-left-cancellable f × is-right-cancellable f

pentagon
  : ∀ {w x y z a} (f : hom w x) (g : hom x y) (k : hom y z) (l : hom z a)
  → g ⨾ k ⨾ l ≡ (g ⨾ k) ⨾ l
  → f ⨾ (g ⨾ k) ⨾ l ≡ (f ⨾ g ⨾ k) ⨾ l
  → f ⨾ g ⨾ k ≡ (f ⨾ g) ⨾ k
  → f ⨾ g ⨾ k ⨾ l ≡ (f ⨾ g) ⨾ k ⨾ l
  → (f ⨾ g) ⨾ k ⨾ l ≡ ((f ⨾ g) ⨾ k) ⨾ l
  → Type h
pentagon f g k l a0 a1 a2 b0 b1 = (f ◃ a0) ∙ a1 ∙ (a2 ▹ l) ≡ b0 ∙ b1
{-# INLINE pentagon #-}
```

-- record is-pullback {b c d ρ} {f : hom b d} {g : hom c d} {π₁ : hom ρ b} {π₂ : hom ρ c}
--   (pb : commutative-sq π₁ π₂ f g) : Type (o ⊔ h) where
--   no-eta-equality
--   field
--     universal
--       : ∀ {a} (α : hom a b) (β : hom a c) → commutative-sq α β f g
--       → is-contr (Σ h ∶ hom a ρ , (h ⨾ π₁ ≡ α) × (h ⨾ π₂ ≡ β))

--   gap : ∀ {a} (α : hom a b) (β : hom a c) → commutative-sq α β f g → hom a ρ
--   gap α β s = universal α β s .center .fst

--   gap-π₁
--     : ∀ {a} (α : hom a b) (β : hom a c) (s : commutative-sq α β f g)
--     → gap α β s ⨾ π₁ ≡ α
--   gap-π₁ α β s = universal α β s .center .snd .fst

--   gap-π₂
--     : ∀ {a} (α : hom a b) (β : hom a c) (s : commutative-sq α β f g)
--     → gap α β s ⨾ π₂ ≡ β
--   gap-π₂ α β s = universal α β s .center .snd .snd

-- {-# INLINE is-pullback.constructor #-}

-- record pullback {b c d} (f : hom b d) (g : hom c d) : Type (o ⊔ h) where
--   no-eta-equality
--   field
--     apex   : ob
--     π₁     : hom apex b
--     π₂     : hom apex c
--     square : commutative-sq π₁ π₂ f g
--     is-pb  : is-pullback square
--   open is-pullback is-pb public

-- {-# INLINE pullback.constructor #-}
