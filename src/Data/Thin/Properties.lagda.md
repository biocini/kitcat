Category laws and structural properties of thinnings.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.Thin.Properties where

open import Core.Type
open import Core.Base
  using (_≡_; PathP; refl; ap; sym; is-set; is-prop;
         is-contr; center; paths)
open import Core.Kan
  using (is-contr→is-prop; is-contr→is-set;
         total-contr-unique; _∙_)
open import Core.Transport.Base using (transport; transport-refl)
open import Core.Transport.J using (J; subst)
open import Core.HLevel.Base using (retract→is-prop)
open import Core.Data.Sigma using (Sigma; _,_; _×_; fst; snd)
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type
open import Data.Thin.Base

open Core.Type using (⊤; tt)

private variable
  u : Level
  K : Type u
  iz jz kz : List K
  k : K

law-oi⨾ : {θ : iz ≤ jz} → oi ⨾ θ ≡ θ
law-oi⨾ = {!!}

law-⨾oi : {θ : iz ≤ jz} → θ ⨾ oi ≡ θ
law-⨾oi = {!!}

law-⨾⨾ : {lz : List K} {θ : iz ≤ jz} {φ : jz ≤ kz} {ψ : kz ≤ lz}
        → θ ⨾ (φ ⨾ ψ) ≡ (θ ⨾ φ) ⨾ ψ
law-⨾⨾ = {!!}

law-oe : {kz : List K} (θ : [] ≤ kz) → θ ≡ oe
law-oe = {!!}

```

## Code identity system

`Code θ φ` is a reflexive relation on thinnings whose total
space is contractible by `code-path`. The `os` constructor of
`_≤_` places `k` in both indices, so pattern-matching two
thinnings simultaneously requires K-elimination.  Code's
constructors avoid this for distinct-target matches: each
`co'/cos` match assigns its own fresh `{k}` to the fixed
index. `code-path` exploits this to match two codes whose
targets are distinct implicit variables.
for (f : iz ≤ jz) (g : jz ≤ kz), then: ¬ (Σ sz ∶ List K , f ⨾ g ≡ os sz)

```agda

data Code {u} {K : Type u} : {iz jz : List K}
  → iz ≤ jz → iz ≤ jz → Type u where
  co' : ∀ {iz jz k} {θ φ : iz ≤ jz}
      → Code θ φ → Code (o' {k = k} θ) (o' φ)
  cos : ∀ {iz jz k} {θ φ : iz ≤ jz}
      → Code θ φ → Code (os {k = k} θ) (os φ)
  coz : Code oz oz

refl-code : (θ : iz ≤ jz) → Code θ θ
refl-code (o' θ) = co' (refl-code θ)
refl-code (os θ) = cos (refl-code θ)
refl-code oz     = coz

decode : {θ φ : iz ≤ jz} → Code θ φ → θ ≡ φ
decode (co' c) = ap o' (decode c)
decode (cos c) = ap os (decode c)
decode coz     = refl

code-path
  : {θ φ ψ : iz ≤ jz}
  → (c₁ : Code θ φ) (c₂ : Code θ ψ)
  → _≡_ {A = Sigma (iz ≤ jz) (Code θ)} (φ , c₁) (ψ , c₂)
code-path (co' c₁) (co' c₂) =
  ap (λ (φ , c) → o' φ , co' c) (code-path c₁ c₂)
code-path (cos c₁) (cos c₂) =
  ap (λ (φ , c) → os φ , cos c) (code-path c₁ c₂)
code-path coz       coz       = refl

Code-total-contr
  : {θ : iz ≤ jz}
  → is-contr (Sigma (iz ≤ jz) (Code θ))
Code-total-contr {θ = θ} .center = θ , refl-code θ
Code-total-contr {θ = θ} .paths (φ , c) =
  code-path (refl-code θ) c

Code-is-prop : {θ φ : iz ≤ jz} → is-prop (Code θ φ)
Code-is-prop = {!!}

decode-refl : (θ : iz ≤ jz) → decode (refl-code θ) ≡ refl
decode-refl (o' θ) = ap (ap o') (decode-refl θ)
decode-refl (os θ) = ap (ap os) (decode-refl θ)
decode-refl oz     = refl

≤-is-set : {iz jz : List K} → is-set (iz ≤ jz)
≤-is-set θ φ =
  retract→is-prop decode encode section Code-is-prop
  where
    encode : θ ≡ φ → Code θ φ
    encode p = transport (λ i → Code θ (p i)) (refl-code θ)

    section : (p : θ ≡ φ) → decode (encode p) ≡ p
    section = J
      (λ _ p → decode (transport (λ i → Code θ (p i))
                  (refl-code θ)) ≡ p)
      (ap decode (transport-refl (refl-code θ))
        ∙ decode-refl θ)

```
