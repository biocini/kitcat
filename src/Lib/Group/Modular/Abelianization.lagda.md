Abelianization of the modular group PSL(2,Z).

This module defines the abelianization map
`ab : PSL2Z → Bool × 𝟛` and proves it is a surjective homomorphism
with respect to the group structures on PSL2Z and the product of
cyclic groups Z/2 × Z/3.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Abelianization where

open import Core.Base using (_≡_; refl; sym; ap; ap2)
open import Core.Kan using (_∙_; _≡⟨_⟩_; _∎)
open import Core.Type using (Type; 0ℓ; ⊤; tt)
open import Core.Data.Sigma using (Σ; _,_; fst; snd; _×_)
open import Core.Data.Sum using (_⊎_; inl; inr)
open import Core.Data.Bool using (Bool; true; false)
open import Core.Data.Empty using (⊥; ex-falso)
open import Core.Path using (_≢_)
open import Core.Transport.J using (subst)

open import Lib.Group.Modular.Multiplication
open import Lib.Group.Modular.Properties
open import Lib.Group.Modular.Base
open import Lib.Group.Modular.Type

```


## The three-element type

The cyclic group Z/3 represented as a three-element sum type.

```agda
𝟛 : Type 0ℓ
𝟛 = ⊤ ⊎ ⊤ ⊎ ⊤

pattern 𝟬 = inl tt
pattern 𝟭 = inr (inl tt)
pattern 𝟮 = inr (inr tt)
```


## Modular arithmetic

Addition mod 3 and mod 2, defined by exhaustive case split.

```agda
_+₃_ : 𝟛 → 𝟛 → 𝟛
𝟬 +₃ y = y
𝟭 +₃ 𝟬 = 𝟭
𝟭 +₃ 𝟭 = 𝟮
𝟭 +₃ 𝟮 = 𝟬
𝟮 +₃ 𝟬 = 𝟮
𝟮 +₃ 𝟭 = 𝟬
𝟮 +₃ 𝟮 = 𝟭

_+₂_ : Bool → Bool → Bool
false +₂ y = y
true  +₂ false = true
true  +₂ true  = false
```


## Arithmetic lemmas

All proved by exhaustive case split; every case is `refl`.

```agda
+₂-comm : (x y : Bool) → x +₂ y ≡ y +₂ x
+₂-comm false false = refl
+₂-comm false true  = refl
+₂-comm true  false = refl
+₂-comm true  true  = refl

+₂-assoc : (x y z : Bool) → (x +₂ y) +₂ z ≡ x +₂ (y +₂ z)
+₂-assoc false y     z     = refl
+₂-assoc true  false z     = refl
+₂-assoc true  true  false = refl
+₂-assoc true  true  true  = refl

+₂-unit-right : (x : Bool) → x +₂ false ≡ x
+₂-unit-right false = refl
+₂-unit-right true  = refl

+₂-cancel : (x : Bool) → x +₂ x ≡ false
+₂-cancel false = refl
+₂-cancel true  = refl

+₂-cancel-inv : (x : Bool) → true +₂ (true +₂ x) ≡ x
+₂-cancel-inv false = refl
+₂-cancel-inv true  = refl

+₃-comm : (x y : 𝟛) → x +₃ y ≡ y +₃ x
+₃-comm 𝟬 𝟬 = refl
+₃-comm 𝟬 𝟭 = refl
+₃-comm 𝟬 𝟮 = refl
+₃-comm 𝟭 𝟬 = refl
+₃-comm 𝟭 𝟭 = refl
+₃-comm 𝟭 𝟮 = refl
+₃-comm 𝟮 𝟬 = refl
+₃-comm 𝟮 𝟭 = refl
+₃-comm 𝟮 𝟮 = refl

+₃-assoc : (x y z : 𝟛) → (x +₃ y) +₃ z ≡ x +₃ (y +₃ z)
+₃-assoc 𝟬 y z = refl
+₃-assoc 𝟭 𝟬 z = refl
+₃-assoc 𝟭 𝟭 𝟬 = refl
+₃-assoc 𝟭 𝟭 𝟭 = refl
+₃-assoc 𝟭 𝟭 𝟮 = refl
+₃-assoc 𝟭 𝟮 𝟬 = refl
+₃-assoc 𝟭 𝟮 𝟭 = refl
+₃-assoc 𝟭 𝟮 𝟮 = refl
+₃-assoc 𝟮 𝟬 z = refl
+₃-assoc 𝟮 𝟭 𝟬 = refl
+₃-assoc 𝟮 𝟭 𝟭 = refl
+₃-assoc 𝟮 𝟭 𝟮 = refl
+₃-assoc 𝟮 𝟮 𝟬 = refl
+₃-assoc 𝟮 𝟮 𝟭 = refl
+₃-assoc 𝟮 𝟮 𝟮 = refl

+₃-unit-right : (x : 𝟛) → x +₃ 𝟬 ≡ x
+₃-unit-right 𝟬 = refl
+₃-unit-right 𝟭 = refl
+₃-unit-right 𝟮 = refl
```


## The abelianization type

The target group is the product Z/2 × Z/3 with componentwise
addition.

```agda
Ab : Type 0ℓ
Ab = Bool × 𝟛

_+ᴬ_ : Ab → Ab → Ab
(s₁ , r₁) +ᴬ (s₂ , r₂) = (s₁ +₂ s₂) , (r₁ +₃ r₂)

0ᴬ : Ab
0ᴬ = false , 𝟬
```


## Abelian group laws for Ab

```agda
+ᴬ-comm : (a b : Ab) → a +ᴬ b ≡ b +ᴬ a
+ᴬ-comm (s₁ , r₁) (s₂ , r₂) =
  ap2 _,_ (+₂-comm s₁ s₂) (+₃-comm r₁ r₂)

+ᴬ-assoc : (a b c : Ab) → (a +ᴬ b) +ᴬ c ≡ a +ᴬ (b +ᴬ c)
+ᴬ-assoc (s₁ , r₁) (s₂ , r₂) (s₃ , r₃) =
  ap2 _,_ (+₂-assoc s₁ s₂ s₃) (+₃-assoc r₁ r₂ r₃)

+ᴬ-unit-right : (a : Ab) → a +ᴬ 0ᴬ ≡ a
+ᴬ-unit-right (s₁ , r₁) =
  ap2 _,_ (+₂-unit-right s₁) (+₃-unit-right r₁)
```


## The abelianization map

Defined by mutual recursion on S-edges and R-edges.

```agda
ab-η : S-edge → Ab
ab-θ : R-edge → Ab

ab-η e₀         = false , 𝟬
ab-η e₁         = true , 𝟬
ab-η (cross re) =
  (true +₂ fst (ab-θ re)) , snd (ab-θ re)

ab-θ (r+ se) =
  fst (ab-η se) , (𝟭 +₃ snd (ab-η se))
ab-θ (r- se) =
  fst (ab-η se) , (𝟮 +₃ snd (ab-η se))

ab : PSL2Z → Ab
ab (η se) = ab-η se
ab (θ re) = ab-θ re
```


## Generator interaction lemmas

How the abelianization map interacts with the generators s, r, and
r-squared.

```agda
ab-s : (x : PSL2Z) → ab (s x) ≡ (true , 𝟬) +ᴬ ab x
ab-s (η e₀)         = refl
ab-s (η e₁)         = refl
ab-s (η (cross re)) =
  sym (ap2 _,_ (+₂-cancel-inv (fst (ab-θ re))) refl)
ab-s (θ re)          = refl

ab-r : (x : PSL2Z) → ab (r x) ≡ (false , 𝟭) +ᴬ ab x
ab-r (η e₀)         = refl
ab-r (η e₁)         = refl
ab-r (η (cross re)) = refl
ab-r (θ (r+ se))    =
  ap2 _,_ refl (+₃-assoc 𝟭 𝟭 (snd (ab-η se)))
ab-r (θ (r- se))    =
  ap2 _,_ refl (+₃-assoc 𝟭 𝟮 (snd (ab-η se)))
```

The r-squared case derives from two applications of `ab-r`.

```agda
ab-r² : (x : PSL2Z) → ab (r² x) ≡ (false , 𝟮) +ᴬ ab x
ab-r² x =
  ab-r (r x)
  ∙ ap ((false , 𝟭) +ᴬ_) (ab-r x)
  ∙ sym (+ᴬ-assoc (false , 𝟭) (false , 𝟭) (ab x))
```


## Key structural lemmas

Right-addition lemmas for the abelianization of R-edges.

```agda
ab-η+R : (se : S-edge) → ab-η se +ᴬ (false , 𝟭) ≡ ab-θ (r+ se)
ab-η+R se =
  ap2 _,_ (+₂-unit-right (fst (ab-η se)))
           (+₃-comm (snd (ab-η se)) 𝟭)

ab-η+R² : (se : S-edge) → ab-η se +ᴬ (false , 𝟮) ≡ ab-θ (r- se)
ab-η+R² se =
  ap2 _,_ (+₂-unit-right (fst (ab-η se)))
           (+₃-comm (snd (ab-η se)) 𝟮)
```


## The homomorphism proof

The abelianization map preserves multiplication.

```agda
ab-hom : (x y : PSL2Z) → ab (x · y) ≡ ab x +ᴬ ab y
ab-hom (η e₀) y = refl
ab-hom (η e₁) y = ab-s y
ab-hom (η (cross re)) y =
  ab ((s∙ re) · y)
    ≡⟨ ap ab (·-s-left (θ re) y) ⟩
  ab (s ((θ re) · y))
    ≡⟨ ab-s ((θ re) · y) ⟩
  (true , 𝟬) +ᴬ ab ((θ re) · y)
    ≡⟨ ap ((true , 𝟬) +ᴬ_) (ab-hom (θ re) y) ⟩
  (true , 𝟬) +ᴬ (ab-θ re +ᴬ ab y)
    ≡⟨ sym (+ᴬ-assoc (true , 𝟬) (ab-θ re) (ab y)) ⟩
  ((true , 𝟬) +ᴬ ab-θ re) +ᴬ ab y
    ∎
ab-hom (θ (r+ se)) y =
  ab ((r∙ se) · y)
    ≡⟨ ap (λ z → ab (z · y)) (sym (r-η se)) ⟩
  ab ((r (η se)) · y)
    ≡⟨ ap ab (·-r-left (η se) y) ⟩
  ab (r ((η se) · y))
    ≡⟨ ab-r ((η se) · y) ⟩
  (false , 𝟭) +ᴬ ab ((η se) · y)
    ≡⟨ ap ((false , 𝟭) +ᴬ_) (ab-hom (η se) y) ⟩
  (false , 𝟭) +ᴬ (ab-η se +ᴬ ab y)
    ≡⟨ sym (+ᴬ-assoc (false , 𝟭) (ab-η se) (ab y)) ⟩
  ((false , 𝟭) +ᴬ ab-η se) +ᴬ ab y
    ≡⟨ ap (_+ᴬ ab y) (+ᴬ-comm (false , 𝟭) (ab-η se)) ⟩
  (ab-η se +ᴬ (false , 𝟭)) +ᴬ ab y
    ≡⟨ ap (_+ᴬ ab y) (ab-η+R se) ⟩
  ab-θ (r+ se) +ᴬ ab y
    ∎
ab-hom (θ (r- se)) y =
  ab ((r²∙ se) · y)
    ≡⟨ ap (λ z → ab (z · y)) (sym (r²-η se)) ⟩
  ab ((r² (η se)) · y)
    ≡⟨ ap ab (·-r²-left (η se) y) ⟩
  ab (r² ((η se) · y))
    ≡⟨ ab-r² ((η se) · y) ⟩
  (false , 𝟮) +ᴬ ab ((η se) · y)
    ≡⟨ ap ((false , 𝟮) +ᴬ_) (ab-hom (η se) y) ⟩
  (false , 𝟮) +ᴬ (ab-η se +ᴬ ab y)
    ≡⟨ sym (+ᴬ-assoc (false , 𝟮) (ab-η se) (ab y)) ⟩
  ((false , 𝟮) +ᴬ ab-η se) +ᴬ ab y
    ≡⟨ ap (_+ᴬ ab y) (+ᴬ-comm (false , 𝟮) (ab-η se)) ⟩
  (ab-η se +ᴬ (false , 𝟮)) +ᴬ ab y
    ≡⟨ ap (_+ᴬ ab y) (ab-η+R² se) ⟩
  ab-θ (r- se) +ᴬ ab y
    ∎
```


## Surjectivity

Every element of the abelian target is in the image of ab.

```agda
ab-surj : (a : Ab) → Σ λ x → ab x ≡ a
ab-surj (false , 𝟬) = E  , refl
ab-surj (false , 𝟭) = R  , refl
ab-surj (false , 𝟮) = R² , refl
ab-surj (true  , 𝟬) = S  , refl
ab-surj (true  , 𝟭) = SR , refl
ab-surj (true  , 𝟮) = SR² , refl
```


## Commutativity

The abelianization witnesses the commutativity of PSL2Z up to the
abelianization map.

```agda
ab-commutative : (x y : PSL2Z)
  → ab (x · y) ≡ ab (y · x)
ab-commutative x y =
  ab-hom x y
  ∙ +ᴬ-comm (ab x) (ab y)
  ∙ sym (ab-hom y x)
```
