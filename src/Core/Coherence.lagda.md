Lane Biocini, March 2026

Pentagon and triangle coherences for the path groupoid.

The pentagon identity holds from the contractible fiber at the
common target of all five bracketings. Each bracketing decomposes
via `pcom.lsplit` and `yon-composite` from `Core.Groupoid`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Coherence where

open import Core.Base
open import Core.Type using (Level; Type; _₊)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Kan
open import Core.Equiv.Base using (eqv-fibers)
open import Core.Path.Base using (ap-comp)
open import Core.Groupoid

private variable
  u : Level
```

## Pentagon

All five bracketings of a four-fold composite decompose via
`pcom.lsplit` and `yon-composite` to a common target. The
pentagon identity follows from `is-contr→is-set` on the
contractible fiber at this target.

```agda

module _ {A : Type u} where

  module pentagon-fibers {v w x y z : A}
    (a : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z)
    where

    private
      funext⁴
        : ∀ {v} {z₀ : A}
          {B : ∀ (y' : A) → z₀ ≡ y' → ∀ (z' : A) → y' ≡ z' → Type v}
          {f g : ∀ y' q' z' r' → B y' q' z' r'}
        → (∀ y' q' z' r' → f y' q' z' r' ≡ g y' q' z' r')
        → f ≡ g
      funext⁴ h = funext λ y' → funext λ q' →
        funext λ z' → funext λ r' → h y' q' z' r'

    -- Common target: fully expanded via yon
    E₄ : ∀ y' → z ≡ y' → ∀ z' → y' ≡ z' → v ≡ z'
    E₄ y' q' z' r' = yon a _ (yon q _ (yon r _ (yon s _ q'))) ∙ r'

    private
      E₄c : is-contr (fiber emb E₄)
      E₄c = eqv-fibers emb-equiv E₄

      c₁ : ∀ y' (q' : z ≡ y') z' (r' : y' ≡ z')
        → emb (((a ∙ q) ∙ r) ∙ s) y' q' z' r' ≡ E₄ y' q' z' r'
      c₁ y' q' z' r' =
        pcom.lsplit (((a ∙ q) ∙ r) ∙ s) q' r'
        ∙ ap (_∙ r')
            (pcom (sym (yon-composite ((a ∙ q) ∙ r) s q'))
              (yon-composite (a ∙ q) r (yon s _ q'))
              (yon-composite a q (yon r _ (yon s _ q'))))

      c₂ : ∀ y' (q' : z ≡ y') z' (r' : y' ≡ z')
        → emb ((a ∙ (q ∙ r)) ∙ s) y' q' z' r' ≡ E₄ y' q' z' r'
      c₂ y' q' z' r' =
        pcom.lsplit ((a ∙ (q ∙ r)) ∙ s) q' r'
        ∙ ap (_∙ r')
            (pcom (sym (yon-composite (a ∙ (q ∙ r)) s q'))
              (yon-composite a (q ∙ r) (yon s _ q'))
              (ap (yon a _) (yon-composite q r (yon s _ q'))))

      c₃ : ∀ y' (q' : z ≡ y') z' (r' : y' ≡ z')
        → emb (a ∙ ((q ∙ r) ∙ s)) y' q' z' r' ≡ E₄ y' q' z' r'
      c₃ y' q' z' r' =
        pcom.lsplit (a ∙ ((q ∙ r) ∙ s)) q' r'
        ∙ ap (_∙ r') (yon-composite a ((q ∙ r) ∙ s) q'
                       ∙ ap (yon a _) (yon-composite (q ∙ r) s q'
                                        ∙ yon-composite q r (yon s _ q')))

      c₄ : ∀ y' (q' : z ≡ y') z' (r' : y' ≡ z')
        → emb ((a ∙ q) ∙ (r ∙ s)) y' q' z' r' ≡ E₄ y' q' z' r'
      c₄ y' q' z' r' =
        pcom.lsplit ((a ∙ q) ∙ (r ∙ s)) q' r'
        ∙ ap (_∙ r')
            (pcom (sym (yon-composite (a ∙ q) (r ∙ s) q'))
              (yon-composite a q (yon (r ∙ s) _ q'))
              (ap (yon a _)
                (ap (yon q _) (yon-composite r s q'))))

      c₅ : ∀ y' (q' : z ≡ y') z' (r' : y' ≡ z')
        → emb (a ∙ (q ∙ (r ∙ s))) y' q' z' r' ≡ E₄ y' q' z' r'
      c₅ y' q' z' r' =
        pcom.lsplit (a ∙ (q ∙ (r ∙ s))) q' r'
        ∙ ap (_∙ r') (yon-composite a (q ∙ (r ∙ s)) q'
                       ∙ ap (yon a _) (yon-composite q (r ∙ s) q'
                                        ∙ ap (yon q _) (yon-composite r s q')))

    pt₁ pt₂ pt₃ pt₄ pt₅ : fiber emb E₄
    pt₁ = ((a ∙ q) ∙ r) ∙ s , funext⁴ c₁
    pt₂ = (a ∙ (q ∙ r)) ∙ s , funext⁴ c₂
    pt₃ = a ∙ ((q ∙ r) ∙ s) , funext⁴ c₃
    pt₄ = (a ∙ q) ∙ (r ∙ s) , funext⁴ c₄
    pt₅ = a ∙ (q ∙ (r ∙ s)) , funext⁴ c₅

    σ₁₂ σ₁₄ σ₂₃ σ₃₅ σ₄₅ : _
    σ₁₂ = is-contr→is-prop E₄c pt₁ pt₂
    σ₁₄ = is-contr→is-prop E₄c pt₁ pt₄
    σ₂₃ = is-contr→is-prop E₄c pt₂ pt₃
    σ₃₅ = is-contr→is-prop E₄c pt₃ pt₅
    σ₄₅ = is-contr→is-prop E₄c pt₄ pt₅

    α₁₂ : ((a ∙ q) ∙ r) ∙ s ≡ (a ∙ (q ∙ r)) ∙ s
    α₁₂ = ap fst σ₁₂

    α₁₄ : ((a ∙ q) ∙ r) ∙ s ≡ (a ∙ q) ∙ (r ∙ s)
    α₁₄ = ap fst σ₁₄

    α₂₃ : (a ∙ (q ∙ r)) ∙ s ≡ a ∙ ((q ∙ r) ∙ s)
    α₂₃ = ap fst σ₂₃

    α₃₅ : a ∙ ((q ∙ r) ∙ s) ≡ a ∙ (q ∙ (r ∙ s))
    α₃₅ = ap fst σ₃₅

    α₄₅ : (a ∙ q) ∙ (r ∙ s) ≡ a ∙ (q ∙ (r ∙ s))
    α₄₅ = ap fst σ₄₅

    private
      fiber-identity : σ₁₄ ∙ σ₄₅ ≡ pcom (sym σ₁₂) σ₂₃ σ₃₅
      fiber-identity = is-contr→is-set E₄c pt₁ pt₅ _ _

    path
      : α₁₄ ∙ α₄₅ ≡ pcom (sym α₁₂) α₂₃ α₃₅
    path = pcom
      (pcom.ap (λ _ → fst) refl σ₁₄ σ₄₅)
      (ap (ap fst) fiber-identity)
      (pcom.ap (λ _ → fst) (sym σ₁₂) σ₂₃ σ₃₅)

    -- Face identifications connect each αᵢⱼ to sym (assoc ...).
    -- Strategy: construct a "core" path in E₄ whose fst traces
    -- assoc-σ, using E₃-contr snd extended by the appropriate
    -- bridge. Then contr-face identifies ap fst σᵢⱼ with ap fst core.

    face₁₄ : α₁₄ ≡ sym (assoc (a ∙ q) r s)
    face₁₄ = {!!}

    face₄₅ : α₄₅ ≡ sym (assoc a q (r ∙ s))
    face₄₅ = {!!}

    face₁₂ : α₁₂ ≡ ap (_∙ s) (sym (assoc a q r))
    face₁₂ = {!!}

    -- face₂₃ : α₂₃ ≡ sym (assoc a (q ∙ r) s)
    -- face₂₃ = contr-face E₄c σ₂₃ w₂₃ core₂₃ v₂₃
    --   where
    --     br : ∀ y' (q' : z ≡ y') z' (r' : y' ≡ z')
    --       → E₃ a (q ∙ r) s y' q' z' r'
    --       ≡ E₄ y' q' z' r'
    --     br y' q' z' r' =
    --       ap (_∙ r')
    --         (ap (yon a _)
    --           (yon-composite q r (yon s _ q')))

    --     core₂₃ : _
    --     core₂₃ i =
    --       assoc-σ a (q ∙ r) s i .fst
    --       , funext⁴ λ y' q' z' r' →
    --           assoc-σ a (q ∙ r) s i .snd
    --             y' q' z' r'
    --           ∙ br y' q' z' r'

    --     w₂₃ : snd pt₂ ≡ core₂₃ i0 .snd
    --     w₂₃ = {!!}

    --     v₂₃ : core₂₃ i1 .snd ≡ snd pt₃
    --     v₂₃ = {!!}

    face₃₅ : α₃₅ ≡ ap (a ∙_) (sym (assoc q r s))
    face₃₅ = {!!}

```

## Named pentagon

The standard Mac Lane pentagon using `assoc` from
`Core.Groupoid`. Both sides go from `a ∙ (q ∙ (r ∙ s))`
to `((a ∙ q) ∙ r) ∙ s`.

```agda

  -- pentagon
  --   : {v w x y z : A}
  --     (a : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z)
  --   → assoc a q (r ∙ s) ∙ assoc (a ∙ q) r s
  --   ≡ ap (a ∙_) (assoc q r s)
  --     ∙ assoc a (q ∙ r) s
  --     ∙ ap (_∙ s) (assoc a q r)
  -- pentagon a q r s = {!!}
  --   where open pentagon-fibers a q r s

```
