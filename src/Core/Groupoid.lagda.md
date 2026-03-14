Representability and composition equivalences for the path groupoid.

`repr` proves that `PathP A x y` is equivalent to the ternary
representable type `(w : A i0) → w ≡ x → (z : A i1) → y ≡ z → w ≡ z`.
The composition equivalences prove that post-composition `(_∙ f)` and
pre-composition `(f ∙_)` are equivalences.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Groupoid where

open import Core.Base
open import Core.Type using (Level; Type; _₊; _∘_)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Kan
open import Core.Equiv.Base using (is-equiv; iso→equiv; eqv-fibers)

private variable
  u : Level

```

## Representability

`emb q w p z r = pcom (sym p) q r` embeds a heterogeneous path into a
ternary representable. `op-emb` is the argument-swapped variant. Both
are equivalences.

```agda

module repr where
  module _ {A : I → Type u} {x : A i0} {y : A i1} where
    emb
      : x ≡ y ∶ A → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z ∶ A
    emb q w p z r = pcom (sym p) q r

    op-emb
      : x ≡ y ∶ A → ∀ z → y ≡ z → ∀ w → w ≡ x → w ≡ z ∶ A
    op-emb q z r w p = pcom (sym p) q r

    emb-equiv : is-equiv emb
    emb-equiv = iso→equiv emb (λ f → f x refl y refl) a0 a1 .snd
      where
        a0 : (s : PathP A x y) → emb s x refl y refl ≡ s
        a0 s i j = hcom (∂ j ∨ i) λ where
          k (i = i1) → s j
          k (j = i0) → x
          k (j = i1) → y
          k (k = i0) → s j

        a1
          : (f : ((w : A i0) → w ≡ x
              → (z : A i1) → y ≡ z → PathP A w z))
          → emb (f x (λ _ → x) y (λ _ → y)) ≡ f
        a1 f i w p z r j = hcom (∂ j ∨ i) λ where
          k (i = i1) → f w p z r j
          k (j = i0) → p (~ k ∧ ~ i)
          k (j = i1) → r (k ∨ i)
          k (k = i0) →
            f (p (~ i)) (λ m → p (~ i ∨ m))
              (r i) (λ m → r (i ∧ m)) j

    op-emb-equiv : is-equiv op-emb
    op-emb-equiv =
      iso→equiv op-emb (λ f → f y refl x refl) a0 a1 .snd
      where
        a0
          : (s : PathP A x y) → op-emb s y refl x refl ≡ s
        a0 s i j = hcom (∂ j ∨ i) λ where
          k (i = i1) → s j
          k (j = i0) → x
          k (j = i1) → y
          k (k = i0) → s j

        a1
          : (f : (z : A i1) → y ≡ z
              → (w : A i0) → w ≡ x → PathP A w z)
          → op-emb (f y refl x refl) ≡ f
        a1 f i z r w p j = hcom (∂ j ∨ i) λ where
          k (i = i1) → f z r w p j
          k (j = i0) → p (~ k ∧ ~ i)
          k (j = i1) → r (i ∨ k)
          k (k = i0) →
            f (r i) (λ m → r (i ∧ m))
              (p (~ i)) (λ m → p (~ i ∨ m)) j

module yon-unbiased = repr

```

## Path composition equivalences

Post-composition `(_∙ f)` and pre-composition `(f ∙_)` are
equivalences. The contractible based path space provides the counit.

```agda

module _ {A : Type u} where
  post-comp : {x y : A} → x ≡ y → ∀ w → w ≡ x → w ≡ y
  post-comp f w b = pcom refl b f

  pre-comp : {x y : A} → x ≡ y → ∀ z → y ≡ z → x ≡ z
  pre-comp f z g = pcom refl f g

  post-comp-equiv
    : ∀ {x y : A} → is-equiv (post-comp {x} {y})
  post-comp-equiv {x} {y} =
    iso→equiv (λ f w → _∙ f) (λ g → g x refl)
      Path.unitl ε .snd
    where
      ε : (f : (w : A) → w ≡ x → w ≡ y)
        → (λ w z → pcom (λ _ → w) z
            (f x (λ _ → x))) ≡ f
      ε f i w g j = hcom (∂ j ∨ i) λ where
        k (j = i0) → w
        k (j = i1) →
          f (g (~ i)) (λ j → g (~ i ∨ j)) k
        k (i = i1) → f w g (j ∧ k)
        k (k = i0) → g (~ i ∧ j)

  pre-comp-equiv
    : ∀ {x y : A} → is-equiv (pre-comp {x} {y})
  pre-comp-equiv {x} {y} =
    iso→equiv (λ g z → g ∙_) (λ g → g y refl)
      Path.unitr ε .snd
    where
      ε : (f : (z : A) → y ≡ z → x ≡ z)
        → (λ z z₁ i → pcom (λ _ → x)
            (f y (λ _ → y)) z₁ i) ≡ f
      ε f i w g j = hcom (∂ j ∨ i) λ where
        k (j = i0) → x
        k (j = i1) → g (i ∨ k)
        k (i = i1) → f w g j
        k (k = i0) → f (g i) (λ k → g (i ∧ k)) j

```

## Commented-out work

```agda

-- Both yon-fun-equiv and yon-fun-op-equiv require parametricity (the
-- "free theorem" that polymorphic functions commute with
-- post-composition), which is independent of Cubical Type Theory
-- with univalence.
--
-- The groupoid case (post-comp-equiv above) works because the total
-- space Σ w, w ≡ x is contractible. For the functor case, the
-- analogous space Σ Y, B → Y is not contractible.
--
-- See: Cavallo 2024, "Internal and Observational Parametricity for
-- Cubical Agda" for a type theory where these would be provable.
-- See: https://homotopytypetheory.org/2016/02/24/
--   parametricity-and-excluded-middle/

-- triangle
--   : ∀ {A : Type u} {x y z : A}
--   → (p : x ≡ y) (q : y ≡ z)
--   → Path.assoc p refl q ∙ ap (_∙ q) (Path.unitr p)
--     ≡ ap (p ∙_) (Path.unitl q)
-- triangle p q = {!!}

-- pentagon
--   : ∀ {A : Type u} {v w x y z : A}
--   → (p : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z)
--   → Path.assoc p q (r ∙ s) ∙ Path.assoc (p ∙ q) r s
--     ≡ ap (p ∙_) (Path.assoc q r s)
--       ∙ Path.assoc p (q ∙ r) s
--       ∙ ap (_∙ s) (Path.assoc p q r)
-- pentagon p q r s = {!!}

```
