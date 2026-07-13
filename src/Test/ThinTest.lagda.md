Test: Thin-is-set and ≤-is-set attempt.

`Thin-is-set` is proven via Hedberg with code/decode. The p-dependent
endomorphism `f-collapse` compiles using `com` along the retraction.
The constantness proof for `f-collapse` is blocked: two `com`
expressions with different type families (determined by `p i` vs
`q i`) cannot be shown equal without already having `p ≡ q`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Test.ThinTest where

open import Core.Type
open import Core.Base
  using ( _≡_; refl; ap; sym; is-set; is-prop; PathP
        ; I; i0; i1; _∧_; _∨_; ~_; ∂)
open import Core.Kan
  using (hcom; hfil; pcom; transp; com)
open import Core.HCompU
open import Core.Data.List using (List; []; _∷_)
open import Core.Data.List.Base using (length)
open import Core.Data.Nat.Type using (Nat; Z; S)
open import Core.Data.Empty using (⊥)
open import Core.Data.Sigma using (Σ; _,_; fst; snd)
open import Core.Data.Dec.Properties
  using (collapsible-id→is-set)
open import Core.Data.Dec.Type using (is-collapsible)
open import Data.Thin.Type using (_≤_; o'; os; oz; _:-_)

open Core.Type using (⊤; tt)

private variable
  u : Level
  K : Type u
  kz iz jz : List K
  m n : Nat

```

## Thin type

Bitmask-indexed thinning. The element `k` appears only in the list
index, so matching two Thin values at `os` produces no equation on K.

```agda

data Thin {u} {K : Type u}
  : List K → Nat → Nat → Type u where
  o' : ∀ {kz m n k}
     → Thin kz m n → Thin (kz :- k) m (S n)
  os : ∀ {kz m n k}
     → Thin kz m n → Thin (kz :- k) (S m) (S n)
  oz : Thin [] Z Z

```

## Thin-is-set via Hedberg

```agda

code : ∀ {u} {K : Type u} {kz : List K} {m n}
  → Thin kz m n → Thin kz m n → Type
code (o' t₁) (o' t₂) = code t₁ t₂
code (os t₁) (os t₂) = code t₁ t₂
code oz      oz       = ⊤
code (o' _)  (os _)   = ⊥
code (os _)  (o' _)   = ⊥

refl-code : (t : Thin kz m n) → code t t
refl-code (o' t) = refl-code t
refl-code (os t) = refl-code t
refl-code oz     = tt

encode : {t₁ t₂ : Thin kz m n}
  → t₁ ≡ t₂ → code t₁ t₂
encode {t₁ = t} p =
  transp (λ i → code t (p i)) i0 (refl-code t)

decode : (t₁ t₂ : Thin kz m n) → code t₁ t₂ → t₁ ≡ t₂
decode (o' t₁) (o' t₂) c = ap o' (decode t₁ t₂ c)
decode (os t₁) (os t₂) c = ap os (decode t₁ t₂ c)
decode oz      oz       _ = refl

code-is-prop : (t₁ t₂ : Thin kz m n)
  → is-prop (code t₁ t₂)
code-is-prop (o' t₁) (o' t₂) = code-is-prop t₁ t₂
code-is-prop (os t₁) (os t₂) = code-is-prop t₁ t₂
code-is-prop oz      oz   tt tt = refl
code-is-prop (o' _)  (os _)  ()
code-is-prop (os _)  (o' _)  ()

Thin-is-set : is-set (Thin kz m n)
Thin-is-set = collapsible-id→is-set λ x y →
  (λ p → decode x y (encode p))
  , λ p q → ap (decode x y)
      (code-is-prop x y (encode p) (encode q))

```

## Conversion between ≤ and Thin

```agda

select : ∀ {u} {K : Type u} {kz : List K} {m n}
  → Thin kz m n → List K
select (o' t)          = select t
select (os {k = k} t)  = select t :- k
select oz              = []

to-thin : iz ≤ jz → Thin jz (length iz) (length jz)
to-thin (o' θ) = o' (to-thin θ)
to-thin (os θ) = os (to-thin θ)
to-thin oz     = oz

from-thin : ∀ {u} {K : Type u} {kz : List K} {m n}
  → (t : Thin kz m n) → select t ≤ kz
from-thin (o' t) = o' (from-thin t)
from-thin (os t) = os (from-thin t)
from-thin oz     = oz

select-to-thin
  : (θ : iz ≤ jz) → select (to-thin θ) ≡ iz
select-to-thin (o' θ) = select-to-thin θ
select-to-thin (os {k = k} θ) =
  ap (_:- k) (select-to-thin θ)
select-to-thin oz = refl

retraction
  : (θ : iz ≤ jz)
  → PathP (λ i → select-to-thin θ i ≤ jz)
      (from-thin (to-thin θ)) θ
retraction (o' θ) i = o' (retraction θ i)
retraction (os θ) i = os (retraction θ i)
retraction oz = refl

```

## select is constant along decode

`decode` builds paths from `ap o'`, `ap os`, and `refl`.
Applying `select` erases the constructor: `select ∘ o' = select`
and `select ∘ os = select _ :- k`. So `select` sees no change.

```agda

select-const
  : ∀ {u} {K : Type u} {kz : List K} {m n}
    (t₁ t₂ : Thin kz m n) (c : code t₁ t₂)
  → ap select (decode t₁ t₂ c) ≡ refl
select-const (o' t₁) (o' t₂) c = select-const t₁ t₂ c
select-const (os t₁) (os t₂) c =
  ap (ap (_:- _)) (select-const t₁ t₂ c)
select-const oz oz _ = refl

```

## ≤-is-set

Factor through the propositional `code`. The endomorphism
`decode-≤ ∘ encode-≤` is weakly constant because `code` is
propositional.

`decode-≤` uses `com` along `select-to-thin` to transport
`from-thin` (at varying source type) into the fixed `iz ≤ jz`.

```agda

module _ {u} {K : Type u} {iz jz : List K} where

  encode-≤ : {θ φ : iz ≤ jz}
    → θ ≡ φ → code (to-thin θ) (to-thin φ)
  encode-≤ {θ = θ} p =
    transp (λ i → code (to-thin θ) (to-thin (p i))) i0
      (refl-code (to-thin θ))

  decode-≤ : (θ φ : iz ≤ jz)
    → code (to-thin θ) (to-thin φ) → θ ≡ φ
  decode-≤ θ φ c i =
    com (λ j → select-to-thin θ j ≤ jz) (∂ i) λ where
      j (i = i0) → retraction θ j
      j (i = i1) →
        com (λ j' → select-path i1 j' ≤ jz) (∂ j) λ where
          j' (j = i0) → from-thin (thin-path i1)
          j' (j = i1) → retraction φ j'
          j' (j' = i0) → from-thin (thin-path i1)
      j (j = i0) → from-thin (thin-path i)
    where
      thin-path = decode (to-thin θ) (to-thin φ) c
      select-path : (i : I) → select (thin-path i) ≡ select (to-thin θ)
      select-path i j = select-const (to-thin θ) (to-thin φ) c j i

  ≤-is-set : is-set (iz ≤ jz)
  ≤-is-set = collapsible-id→is-set λ θ φ →
    (λ p → decode-≤ θ φ (encode-≤ p))
    , λ p q → ap (decode-≤ θ φ)
        (code-is-prop (to-thin θ) (to-thin φ)
          (encode-≤ p) (encode-≤ q))

```
