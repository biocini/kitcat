Bundled propositions and sets with propositional extensionality.

This module consolidates the theory of propositions (h-level 1 types) and sets
(h-level 2 types) as bundled structures, along with propositional extensionality
and conversions to/from `nType`.

This module uses `--cubical` (not `--erased-cubical`) because we need `ua` from
`Core.Univalence` for propositional extensionality.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Core.Set where

open import Core.Data.Nat using (Nat)
open import Core.Transport
open import Core.Univalence
open import Core.HLevel
open import Core.Equiv
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Bool
open import Core.Path
open import Core.Base
open import Core.Type
open import Core.Kan

private variable
  u v : Level
```


## Bundled Propositions

A `Prop` bundles a type with a proof that it is a proposition (h-level 1).

```agda

record Prop (u : Level) : Type (u ₊) where
  no-eta-equality
  field
    ∣_∣ᴾ : Type u
    has-is-prop : is-prop ∣_∣ᴾ

open Prop public
{-# INLINE Prop.constructor #-}
```


## Bundled Sets

A `Set` bundles a type with a proof that it is a set (h-level 2).

```agda

record Set (u : Level) : Type (u ₊) where
  no-eta-equality
  field
    ∣_∣ˢ : Type u
    has-is-set : is-set ∣_∣ˢ

open Set public
{-# INLINE Set.constructor #-}
```


## Propositional Extensionality

Two propositions are equal if they are logically equivalent (bi-implication).
This is a key consequence of univalence for propositions.

```agda

prop-bi-impl→equiv
  : {A : Type u} {B : Type v}
  → is-prop A → is-prop B
  → (A → B) → (B → A)
  → A ≃ B
prop-bi-impl→equiv pA pB f g = iso→equiv f g (λ x → pA (g (f x)) x) (λ y → pB (f (g y)) y)

propext
  : {A B : Type u}
  → is-prop A → is-prop B
  → (A → B) → (B → A)
  → A ≡ B
propext pA pB f g = ua (prop-bi-impl→equiv pA pB f g)
```


## Prop and Set Lemmas

The type of propositions at a given universe level is itself a set. This follows
from the fact that paths between propositions are determined by logical
equivalence, and logical equivalence between propositions is a proposition.

```agda

Type-path-is-prop
  : {A B : Type u}
  → is-prop A → is-prop B
  → is-prop (A ≡ B)
Type-path-is-prop {A = A} {B} pA pB p q = path
  where
    e1 e2 : A ≃ B
    e1 = idtoeqv p
    e2 = idtoeqv q

    fwd-eq : e1 .fst ≡ e2 .fst
    fwd-eq = funext (λ a → pB (e1 .fst a) (e2 .fst a))

    eqv-eq : e1 ≡ e2
    eqv-eq i .fst = fwd-eq i
    eqv-eq i .snd = is-prop→PathP (λ i → is-equiv-is-prop (fwd-eq i))
      (e1 .snd) (e2 .snd) i

    path : p ≡ q
    path = sym (ua-η p) ∙ ap ua eqv-eq ∙ ua-η q


Prop-is-set : is-set (Prop u)
Prop-is-set {u} P Q p q i j .∣_∣ᴾ = type-sq i j
  where
    p' q' : ∣ P ∣ᴾ ≡ ∣ Q ∣ᴾ
    p' i = ∣ p i ∣ᴾ
    q' i = ∣ q i ∣ᴾ

    type-sq : p' ≡ q'
    type-sq = Type-path-is-prop (P .has-is-prop) (Q .has-is-prop) p' q'
Prop-is-set {u} P Q p q i j .has-is-prop =
  is-prop→SquareP (λ i j → is-prop-is-prop (Prop-is-set P Q p q i j .∣_∣ᴾ))
    (λ j → (p j) .has-is-prop)
    (λ i → P .has-is-prop)
    (λ j → (q j) .has-is-prop)
    (λ i → Q .has-is-prop)
    i j


prop-iff : (P Q : Prop u)
         → (∣ P ∣ᴾ → ∣ Q ∣ᴾ) → (∣ Q ∣ᴾ → ∣ P ∣ᴾ)
         → P ≡ Q
prop-iff P Q f g i .∣_∣ᴾ = propext (P .has-is-prop) (Q .has-is-prop) f g i
prop-iff P Q f g i .has-is-prop =
  is-prop→PathP (λ i → is-prop-is-prop (propext (P .has-is-prop) (Q .has-is-prop) f g i))
    (P .has-is-prop) (Q .has-is-prop) i
```


## Standard Instances

```agda

⊤-Prop : Prop 0ℓ
⊤-Prop .∣_∣ᴾ = ⊤
⊤-Prop .has-is-prop _ _ = refl

⊥-Prop : Prop 0ℓ
⊥-Prop .∣_∣ᴾ = ⊥
⊥-Prop .has-is-prop ()

Bool-Set : Set 0ℓ
Bool-Set .∣_∣ˢ = Bool
Bool-Set .has-is-set = Bool.set

Nat-Set : Set 0ℓ
Nat-Set .∣_∣ˢ = Nat
Nat-Set .has-is-set = Nat.set
```


## Coercions

```agda

Prop→Type : Prop u → Type u
Prop→Type P = ∣ P ∣ᴾ

Set→Type : Set u → Type u
Set→Type X = ∣ X ∣ˢ

Prop→Set : Prop u → Set u
Prop→Set P .∣_∣ˢ = ∣ P ∣ᴾ
Prop→Set P .has-is-set = is-prop→is-set (P .has-is-prop)

Prop-Lift : ∀ v → Prop u → Prop (u ⊔ v)
Prop-Lift v P .∣_∣ᴾ = Lift v (∣ P ∣ᴾ)
Prop-Lift v P .has-is-prop (liftℓ a) (liftℓ b) i = liftℓ (P .has-is-prop a b i)

Set-Lift : ∀ v → Set u → Set (u ⊔ v)
Set-Lift v X .∣_∣ˢ = Lift v (∣ X ∣ˢ)
Set-Lift {u} v X .has-is-set = Lift-is-hlevel 2 (X .has-is-set)
```


## nType Conversions

```agda

Prop→nType : Prop u → nType u 1
Prop→nType P .nType.∣_∣ = ∣ P ∣ᴾ
Prop→nType P .nType.is-tr = P .has-is-prop

nType-1→Prop : nType u 1 → Prop u
nType-1→Prop N .∣_∣ᴾ = nType.∣_∣ N
nType-1→Prop N .has-is-prop = nType.is-tr N

Set→nType : Set u → nType u 2
Set→nType X .nType.∣_∣ = ∣ X ∣ˢ
Set→nType X .nType.is-tr = X .has-is-set

nType-2→Set : nType u 2 → Set u
nType-2→Set N .∣_∣ˢ = nType.∣_∣ N
nType-2→Set N .has-is-set = nType.is-tr N
```


## Presheaves

A presheaf over a type `I` (in the context of sets) is an `I`-indexed family of
sets. This definition is useful for defining set-valued functors.

```agda

PSh : (u v : Level) → Type u → Type (u ⊔ v ₊)
PSh u v I = I → Set v
```


## Subtypes

A subtype of `A` is a family of propositions over `A`. The key property is that
equality in the subtype (the Σ-type) is controlled by equality in the base type.

```agda

Subtype : Type u → Type (u ₊)
Subtype A = A → Prop _
```

Two elements of a Σ-type over a propositional family are equal if and only if
their first components are equal. This is the fundamental characterization of
paths in subtypes.

```agda

Σ-Prop-path
  : {A : Type u} (P : A → Prop v)
  → {x y : Σ a ∶ A , ∣ P a ∣ᴾ}
  → x .fst ≡ y .fst → x ≡ y
Σ-Prop-path P {x} {y} p i .fst = p i
Σ-Prop-path P {x} {y} p i .snd =
  is-prop→PathP (λ i → P (p i) .has-is-prop) (x .snd) (y .snd) i
```

Two subtypes are equal if they have the same elements (subtype extensionality).
This follows from propositional extensionality applied pointwise.

```agda

subtype-ext
  : {A : Type u} (P Q : Subtype A)
  → ((a : A) → ∣ P a ∣ᴾ → ∣ Q a ∣ᴾ)
  → ((a : A) → ∣ Q a ∣ᴾ → ∣ P a ∣ᴾ)
  → P ≡ Q
subtype-ext P Q f g = funext λ a → prop-iff (P a) (Q a) (f a) (g a)
```


## Power Set

The power set of `X` is the type of all subtypes of `X`. Since `Subtype X` is
defined as `X → Prop _`, this is definitionally the same.

```agda

𝒫 : Type u → Type (u ₊)
𝒫 X = X → Prop _
```

The power set is a set. This follows because `Prop` is a set and function types
into sets are sets.

```agda

𝒫-is-set : {A : Type u} → is-set (𝒫 A)
𝒫-is-set = Π-is-set (λ _ → Prop-is-set)
```

Membership in a subset is given by extracting the underlying type of the
proposition at a point.

```agda

_∈_ : {A : Type u} → A → 𝒫 A → Type _
a ∈ P = ∣ P a ∣ᴾ

infix 5 _∈_
```

The subset relation holds when every element of one subset is in the other.

```agda

_⊆_ : {A : Type u} → 𝒫 A → 𝒫 A → Type _
P ⊆ Q = ∀ a → a ∈ P → a ∈ Q

infix 4 _⊆_
```

The subset relation is a proposition, since it is a dependent product of
propositions (membership in `Q` is propositional).

```agda

⊆-is-prop : {A : Type u} (P Q : 𝒫 A) → is-prop (P ⊆ Q)
⊆-is-prop P Q = Π-is-prop λ a → Π-is-prop λ _ → Q a .has-is-prop
```

Extensionality for power sets: two subsets are equal when they have the same
elements in both directions.

```agda

𝒫-ext : {A : Type u} {P Q : 𝒫 A} → P ⊆ Q → Q ⊆ P → P ≡ Q
𝒫-ext f g = subtype-ext _ _ f g
```


## Standard Subsets

The empty subset contains no elements.

```agda

∅ : {A : Type u} → 𝒫 A
∅ {u} a = Prop-Lift u ⊥-Prop
```

The full subset (total) contains all elements.

```agda

full : {A : Type u} → 𝒫 A
full {u} a = Prop-Lift u ⊤-Prop
```
