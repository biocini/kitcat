Pentagon test file.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Test.Pentagon where

open import Core.Base
open import Core.Type using (Level; Type)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Kan
open import Core.Transport.Base
open import Core.Path.Base using (ap-comp)

private
  variable
    u : Level

module _ {A : Type u} {v w x y z : A}
  (p : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z) where

  private
    HC = HComposite (sym p) q (r ∙ s)
    HC-contr = pcom.contr (sym p) q (r ∙ s)
    HC-set = is-contr→is-set HC-contr
    lcoh = cat.lcoh p q (r ∙ s)
    rcoh = cat.rcoh p q (r ∙ s)

    e₁ e₂ : HC
    e₁ = _ , lcoh
    e₂ = _ , rcoh

    path₁₂ : e₁ ≡ e₂
    path₁₂ = HComposite.unique (sym p) q (r ∙ s) e₁ e₂

    sys-L : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
    sys-L i j k (i = i0) = p (~ j)
    sys-L i j k (i = i1) = (r ∙ s) j
    sys-L i j k (j = i0) = q i
    sys-L i j k (j = i1) = Path.assoc (p ∙ q) r s k i
    sys-L i j k (k = i0) = rcoh i j

    e₃ : HC
    e₃ = _ , λ i j → hcom (∂ i ∨ ∂ j) λ k → sys-L i j k

    lift₂₃ : e₂ ≡ e₃
    lift₂₃ k = _ , λ i j →
      hfil (∂ i ∨ ∂ j) k λ l → sys-L i j l

    sys-R₁ : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
    sys-R₁ i j k (i = i0) = p (~ j)
    sys-R₁ i j k (i = i1) = (r ∙ s) j
    sys-R₁ i j k (j = i0) = q i
    sys-R₁ i j k (j = i1) =
      ap (p ∙_) (Path.assoc q r s) k i
    sys-R₁ i j k (k = i0) = lcoh i j

    e₄ : HC
    e₄ = _ , λ i j →
      hcom (∂ i ∨ ∂ j) λ k → sys-R₁ i j k

    lift₁₄ : e₁ ≡ e₄
    lift₁₄ k = _ , λ i j →
      hfil (∂ i ∨ ∂ j) k λ l → sys-R₁ i j l

    sys-R₂ : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
    sys-R₂ i j k (i = i0) = p (~ j)
    sys-R₂ i j k (i = i1) = (r ∙ s) j
    sys-R₂ i j k (j = i0) = q i
    sys-R₂ i j k (j = i1) =
      Path.assoc p (q ∙ r) s k i
    sys-R₂ i j k (k = i0) = e₄ .snd i j

    e₅ : HC
    e₅ = _ , λ i j →
      hcom (∂ i ∨ ∂ j) λ k → sys-R₂ i j k

    lift₄₅ : e₄ ≡ e₅
    lift₄₅ k = _ , λ i j →
      hfil (∂ i ∨ ∂ j) k λ l → sys-R₂ i j l

    sys-R₃ : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
    sys-R₃ i j k (i = i0) = p (~ j)
    sys-R₃ i j k (i = i1) = (r ∙ s) j
    sys-R₃ i j k (j = i0) = q i
    sys-R₃ i j k (j = i1) =
      ap (_∙ s) (Path.assoc p q r) k i
    sys-R₃ i j k (k = i0) = e₅ .snd i j

    e₆ : HC
    e₆ = _ , λ i j →
      hcom (∂ i ∨ ∂ j) λ k → sys-R₃ i j k

    lift₅₆ : e₅ ≡ e₆
    lift₅₆ k = _ , λ i j →
      hfil (∂ i ∨ ∂ j) k λ l → sys-R₃ i j l

    lhs-HC : e₁ ≡ e₃
    lhs-HC = path₁₂ ∙ lift₂₃

    rhs-HC : e₁ ≡ e₆
    rhs-HC = lift₁₄ ∙ lift₄₅ ∙ lift₅₆

    bridge : e₆ ≡ e₃
    bridge = is-contr→is-prop HC-contr e₆ e₃

  pentagon
    : Path.assoc p q (r ∙ s) ∙ Path.assoc (p ∙ q) r s
      ≡ ap (p ∙_) (Path.assoc q r s)
        ∙ Path.assoc p (q ∙ r) s
        ∙ ap (_∙ s) (Path.assoc p q r)
  pentagon = ap (ap fst) {!e₁!} where
    ff : lhs-HC ≡ rhs-HC ∙ bridge
    ff = (HC-set e₁ e₃ lhs-HC (rhs-HC ∙ bridge))

    e1f : v ≡ z
    e1f = fst e₁

    aff : ap fst {!e₁!} ≡ {!!}
    aff i = ap fst (ff i)

```
