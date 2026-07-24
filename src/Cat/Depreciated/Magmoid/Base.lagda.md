Lane Biocini
February 2025

Magmoids and the structures we can characterize within them.

We compile all the definitions into a module meant to instantiate uniform definitions
for any category-like (i.e. magmoidal) structure; we also even have the machinery
for heteromorphisms between structures that only agree in being magmoidal,
see the definitions for functor, adjunctions, nat-trans, etc.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Depreciated.Magmoid.Magmoid

module Cat.Depreciated.Magmoid.Base (M : magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel.Base
open import Core.Kan
open import Core.Transport.Base
open import Core.Equiv.Properties renaming (_≃_ to _≃e_)
open import Core.Function.Surjection using (is-surjective)
open import Core.Function.Embedding using (is-embedding; is-embedding→injective)

open magmoids M public
```

## Composability

A pair of morphisms f : hom x y and g : hom y z is composable when
yon distributes their composition pointwise: the representable action
of f ⨾ g equals the pointwise composite of the representable actions.

```agda
composable
  : ∀ {x y z} → hom x y → hom y z → Type (o ⊔ h)
composable f g = yon (f ⨾ g) ≡ λ w → yon g w ∘ yon f w

is-thunkable : ∀ {w x} → hom w x → Type (o ⊔ h)
is-thunkable f = ∀ {y} (g : hom _ y) → composable f g

is-linear : ∀ {y z} → hom y z → Type (o ⊔ h)
is-linear h = ∀ {x} (g : hom x _) → composable g h

thunkable : ∀ {w x y} → hom w x → hom x y → Type (o ⊔ h)
thunkable f g = composable f g

linear : ∀ {x y z} → hom y z → hom x y → Type (o ⊔ h)
linear h g = composable g h
```

## Associator

```agda
associator : ∀ {w x y z} → hom w x → hom x y → hom y z → Type h
associator f g h = f ⨾ (g ⨾ h) ≡ (f ⨾ g) ⨾ h
{-# INLINE associator #-}

is-medial : ∀ {x y} → hom x y → Type (o ⊔ h)
is-medial {x} {y} f = ∀ {w z} (g : hom w x) (h : hom y z)
  → associator g f h
```

## Yon injectivity

The Yoneda embedding is an embedding, so it is injective.

```agda
yon-inj
  : ∀ {x y} {f g : hom x y}
  → yon f ≡ yon g → f ≡ g
yon-inj = is-embedding→injective yon-emb
```

## Thunkable + linear implies associativity

When f is thunkable and h is linear, the triple f g h associates.

```agda
assoc
  : ∀ {w x y z} {f : hom w x} {g : hom x y} {h : hom y z}
  → is-thunkable f → is-linear h
  → associator f g h
assoc {f = f} {g} {h} tf lh = yon-inj (step₁ ∙ sym step₂) where
  step₁ : yon (f ⨾ (g ⨾ h)) ≡ λ w k → yon h w (yon g w (yon f w k))
  step₁ = tf (g ⨾ h) ∙ λ i w k → lh g i w (yon f w k)

  step₂ : yon ((f ⨾ g) ⨾ h) ≡ λ w k → yon h w (yon g w (yon f w k))
  step₂ = lh (f ⨾ g) ∙ λ i w k → yon h w (tf g i w k)

associativity : Type (o ⊔ h)
associativity
  = ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z) → associator f g h
```

## Path algebra

```agda
triangle : ∀ {x y z} → hom x y → hom y z → hom x z → Type h
triangle f g s = f ⨾ g ≡ s

square : ∀ {w x y z} → hom x w → hom x y → hom y z → hom w z → Type h
square f h k g = f ⨾ g ≡ h ⨾ k

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
```

## Divisibility and cancellability

Neutrality decomposes into two independent conditions: divisibility
(composition maps are surjective — division solutions exist) and
cancellability (composition maps are embeddings — division solutions
are unique). This follows from the general HoTT fact that a map is
an equivalence iff it is both surjective and an embedding.

```agda
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
