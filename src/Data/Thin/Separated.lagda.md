Separated thinnings: a K-elimination-free proof that `≤` is a set.

The standard `os` constructor shares a single `k` across both list
indices, so matching two thinnings simultaneously generates a
reflexive equation `k ≡ k` that requires K-elimination.  Separated
thinnings replace this shared `k` with explicit `k₁ k₂ : K` and an
equality proof `k₁ ≡ k₂`, turning the K-blocked equation into
first-order unification on the list spine.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.Thin.Separated where

open import Core.Type
open import Core.Base
  using (_≡_; refl; ap; ap2; sym; is-set; is-prop)
open import Core.Kan using (_∙_)
open import Core.HCompU
open import Core.Transport.Base using (transport; transport-refl)
open import Core.Transport.J using (J; J-refl; subst)
open import Core.HLevel.Base
  using (retract→is-hlevel; retract→is-prop;
         Lift-is-hlevel)
open import Core.Data.Sigma using (Sigma; _,_; fst; snd)
open import Core.Data.List using (List; []; _∷_)
open import Core.Data.Empty using (⊥)
open import Data.Thin.Type

open Core.Type using (⊤; tt; Lift; liftℓ)

private variable
  u : Level
  K : Type u
  iz jz : List K

```

## Separated thinnings

```agda

data Thin {u} {K : Type u}
  : List K → List K → Type u where
  o' : ∀ {iz jz k}
     → Thin iz jz → Thin iz (jz :- k)
  os : ∀ {iz jz} (k₁ k₂ : K) → k₁ ≡ k₂
     → Thin iz jz → Thin (iz :- k₁) (jz :- k₂)
  oz : Thin [] []

```

## Code identity system

```agda

code : {iz jz : List K}
  → Thin iz jz → Thin iz jz → Type u
code (o' t₁)           (o' t₂)         = code t₁ t₂
code (os k₁ k₂ p₁ t₁) (os _ _ p₂ t₂) = code t₁ t₂
code oz                oz              = Lift _ ⊤
code (o' _)            (os _ _ _ _)    = Lift _ ⊥
code (os _ _ _ _)      (o' _)          = Lift _ ⊥

refl-code : (t : Thin {K = K} iz jz) → code t t
refl-code (o' t)         = refl-code t
refl-code (os _ _ _ t)   = refl-code t
refl-code oz             = liftℓ tt

encode
  : {t₁ t₂ : Thin {K = K} iz jz}
  → t₁ ≡ t₂ → code t₁ t₂
encode {t₁ = t₁} p = subst (code t₁) p (refl-code t₁)

code-is-prop
  : (t₁ t₂ : Thin {K = K} iz jz) → is-prop (code t₁ t₂)
code-is-prop (o' t₁)           (o' t₂)
  = code-is-prop t₁ t₂
code-is-prop (os k₁ k₂ p₁ t₁) (os _ _ p₂ t₂)
  = code-is-prop t₁ t₂
code-is-prop oz                oz
  (liftℓ tt) (liftℓ tt) = refl
code-is-prop (o' _)            (os _ _ _ _)
  (liftℓ ())
code-is-prop (os _ _ _ _)      (o' _)
  (liftℓ ())

```

The `os` case of decode varies the equality proof and the
sub-thinning simultaneously along a cubical path, using
`is-set K` to identify `p₁` and `p₂`.

```agda

decode
  : is-set K
  → {t₁ t₂ : Thin {K = K} iz jz}
  → code t₁ t₂ → t₁ ≡ t₂
decode ks {o' t₁}           {o' t₂}         c =
  ap o' (decode ks c)
decode ks {os k₁ k₂ p₁ t₁} {os _ _ p₂ t₂} c i =
  os k₁ k₂ (ks k₁ k₂ p₁ p₂ i) (decode ks c i)
decode ks {t₁ = oz}        {t₂ = oz}        c = refl

decode-refl
  : (ks : is-set K) (t : Thin {K = K} iz jz)
  → decode ks (refl-code t) ≡ refl
decode-refl ks (o' t) =
  ap (ap o') (decode-refl ks t)
decode-refl ks (os k₁ k₂ p t) i j =
  os k₁ k₂ (is-set→sq ks k₁ k₂ p i j) (decode-refl ks t i j)
  where
    is-set→sq
      : is-set K → (a b : K) (q : a ≡ b)
      → ks a b q q ≡ refl
    is-set→sq s a b q = s a b q q refl refl
decode-refl ks oz = refl

```


## Thin-is-set

`code t₁ t₂` is propositional, `decode ∘ encode` is a section, and
`t₁ ≡ t₂` is a retract of `code t₁ t₂`.  So path types in `Thin`
are propositional, making `Thin` a set.

```agda

Thin-is-set
  : is-set K → is-set (Thin {K = K} iz jz)
Thin-is-set ks t₁ t₂ =
  retract→is-prop (decode ks) encode section
    (code-is-prop t₁ t₂)
  where
    section : (p : t₁ ≡ t₂) → decode ks (encode p) ≡ p
    section = J
      (λ _ p → decode ks (encode p) ≡ p)
      (ap (decode ks) (transport-refl (refl-code t₁))
        ∙ decode-refl ks t₁)

```


## Conversions

```agda

to-thin : iz ≤ jz → Thin {K = K} iz jz
to-thin (o' θ) = o' (to-thin θ)
to-thin (os θ) = os _ _ refl (to-thin θ)
to-thin oz     = oz

from-thin : Thin {K = K} iz jz → iz ≤ jz
from-thin (o' t)          = o' (from-thin t)
from-thin (os k₁ k₂ p t) =
  J (λ k₂' _ → (_ :- k₁) ≤ (_ :- k₂'))
    (os (from-thin t)) p
from-thin oz              = oz

retraction
  : (θ : _≤_ {K = K} iz jz) → from-thin (to-thin θ) ≡ θ
retraction (o' θ) = ap o' (retraction θ)
retraction (os θ) =
  J-refl (λ k₂' _ → (_ :- _) ≤ (_ :- k₂'))
    (os (from-thin (to-thin θ)))
  ∙ ap os (retraction θ)
retraction oz = refl

```


## Main result

```agda

≤-is-set
  : is-set K → is-set (_≤_ {K = K} iz jz)
≤-is-set ks =
  retract→is-hlevel 2 from-thin to-thin retraction
    (Thin-is-set ks)

```
