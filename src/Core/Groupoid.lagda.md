TODO: Higher groupoid coherences for path algebra.

The triangle and pentagon identities witnessing Mac Lane's coherence
conditions for the path-composition monoidal structure on types.
Proofs use the contractible composite condition, following the
pattern of Path.assoc in Core.Kan.

Potential refs:
-- Rijke, Exercise 5.4
-- 1lab: Cat.Bi.Instances.Discrete (coherence via contractibility)

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Groupoid where

open import Core.Base
open import Core.Type using (Level; Type; _₊; _∘_)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Kan
open import Core.Equiv.Base
open import Core.Function.Embedding
open import Core.Transport.Base
open import Core.Transport.Properties using (SinglP-contr; is-prop→SquareP)

--open import Cat.Base

private variable
  u : Level

TotalP
  : ∀ {u v} {A : Type u} {B : A → Type v} {x} (a : B x)
  → is-contr (Σ y ∶ A , Σ q ∶ (x ≡ y) , Σ b ∶ B y , PathP (λ i → B (q i)) a b)
TotalP {x} a .center = x , refl , a , refl
TotalP a .paths (y , q , b , α) i = q i , (λ j → q (i ∧ j)) , α i , λ j → α (i ∧ j)

module yon-unbiased where
  module _ {A : I → Type u} {x : A i0} {y : A i1} where
    emb
      : x ≡ y ∶ A → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z ∶ A
    emb q w p z r = pcom (sym p) q r

    op-emb : x ≡ y ∶ A → ∀ z → y ≡ z → ∀ w → w ≡ x → w ≡ z ∶ A
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
          : (f : ((w : A i0) → w ≡ x → (z : A i1) → y ≡ z → PathP A w z))
          → emb (f x (λ _ → x) y (λ _ → y)) ≡ f
        a1 f i w p z r j = hcom (∂ j ∨ i)  λ where
          k (i = i1) → f w p z r j
          k (j = i0) → p (~ k ∧ ~ i)
          k (j = i1) → r (k ∨ i)
          k (k = i0) → f (p (~ i)) (λ m → p (~ i ∨ m)) (r i) (λ m → r (i ∧ m)) j

    op-emb-equiv : is-equiv op-emb
    op-emb-equiv = iso→equiv op-emb (λ f → f y refl x refl) a0 a1 .snd
      where
        a0 : (s : PathP A x y) → op-emb s y refl x refl ≡ s
        a0 s i j = hcom (∂ j ∨ i)  λ where
          k (i = i1) → s j
          k (j = i0) → x
          k (j = i1) → y
          k (k = i0) → s j

        a1
          : (f : (z : A i1) → y ≡ z → (w : A i0) → w ≡ x → PathP A w z)
          → op-emb (f y refl x refl) ≡ f
        a1 f i z r w p j = hcom (∂ j ∨ i)  λ where
          k (i = i1) → f z r w p j
          k (j = i0) → p (~ k ∧ ~ i)
          k (j = i1) → r (i ∨ k)
          k (k = i0) → f (r i) (λ m → r (i ∧ m)) (p (~ i)) (λ m → p (~ i ∨ m)) j

-- module _ {u} (A : Type u) where
--   GPD : category u u
--   GPD .category.ob = A
--   GPD .category.hom x y = ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
--   GPD .category.yon {x} {y} f w g q z u = g q z u ∘ f x refl u
--   GPD .category.yon-equiv {x} {y}
--     = iso→equiv (λ f w g q z u → g q z u ∘ f _ refl u)
--       (λ f w p z q → f w (yon.emb p) w refl z q)
--       h0 h1 .snd
--       where
--       h0
--         : (f : (w : A) → w ≡ x → (z : A) → y ≡ z → w ≡ z)
--         → (λ w p z q i → yon.emb p w (λ _ → w) z (f x (λ _ → x) z q) i) ≡ f
--       h0 f i z r w p j = hcom (∂ j ∨ i) λ where
--         k (i = i1) → f (r (~ k)) (λ m → r (~ k ∨ m)) w p j
--         k (j = i0) → r (i ∧ ~ k)
--         k (j = i1) → f x refl w p (k ∨ i)
--         k (k = i0) → f (r (j ∨ i)) (λ m → r (j ∨ i ∨ m)) w p (i ∧ j)

--       h1
--         : (f : (w : A)
--               → ((w₁ : A) → w₁ ≡ w → (z : A) → x ≡ z → w₁ ≡ z)
--               → (w₁ : A) → w₁ ≡ w → (z : A) → y ≡ z → w₁ ≡ z)
--               → (λ w z w₁ z₁ z₂ z₃ i → z w₁ z₁ z₂ (f x (yon.emb (λ _ → x)) x (λ _ → x) z₂ z₃) i) ≡ f
--       h1 f i x1 g x0 p0 x2 py j = hcom (∂ j ∨ ∂ i) λ where
--         k (i = i0) → {!!}
--         k (i = i1) → f x1 g x0 p0 x2 py (j ∧ k) -- f x1 g x0 p0 x2 py (j ∧ k)
--         k (j = i0) → {!!}
--         k (j = i1) → {!!} -- f x1 g x0 p0 x2 py (~ i ∨ k)
--         k (k = i0) → {!!}
--           where
--             c : (w : A) → w ≡ x → (z : A) → y ≡ z → w ≡ z
--             c w p z = f x (yon.emb refl) w p z

--             c0 : x ≡ x2
--             c0 = c x refl x2 py

--             w0 : x ≡ x2 → x0 ≡ x2
--             w0 = g x0 p0 x2

--             h : (λ w p z → yon.emb p w refl z ∘ c x refl z) ≡ c
--             h = h0 c

--             h' : (λ m → {!c0 m!}) ≡ f x (yon.emb (λ _ → x)) x (λ _ → x) x2 py
--             h' i = h i x refl x2 py

--   GPD .category.yon-op-equiv = {!!}

-- module yon-based {A : I → Type u} {w x : A i0} {y : A i1} where
--   emb
--     : w ≡ x → x ≡ y ∶ A → ∀ z → y ≡ z → w ≡ z ∶ A
--   emb p q z r = pcom (sym p) q r

--   emb-is-eqv : (p : w ≡ x) → is-equiv (emb p)
--   emb-is-eqv p = iso→equiv (emb p)
--     (λ f → pcom p (f y refl) refl) inv0 inv1 .snd
--     where
--       inv0
--         : (x₁ : PathP A x y)
--         → pcom p (emb p x₁ y (λ _ → y)) (λ _ → y) ≡ x₁
--       inv0 q i j = hcom (∂ j ∨ i) λ where
--         k (i = i1) → q j
--         k (j = i0) → p (i ∨ k)
--         k (j = i1) → y
--         k (k = i0) → pcom.fill (sym p) q refl j (~ i)

--       inv1
--         : (f : (z : A i1) → y ≡ z → PathP A w z)
--         → emb p (pcom p (f y (λ _ → y)) (λ _ → y)) ≡ f
--       inv1 f i z r j = hcom (∂ j ∨ i) λ where
--         k (i = i1) → f (r k) (λ m → r (k ∧ m)) j
--         k (j = i0) → p (~ i ∧ ~ k)
--         k (j = i1) → r k
--         k (k = i0) → pcom.fill p (f y refl) refl j (~ i)

private module _ {u} {A : Type u} where
  yon-gpd : {x y : A} → x ≡ y → ∀ w → w ≡ x → w ≡ y
  yon-gpd f w = λ b → pcom refl b f

  yon-gpd-op : {x y : A} → x ≡ y → ∀ z → y ≡ z → x ≡ z
  yon-gpd-op f z g = pcom refl f g

  yon-gpd-equiv : ∀ {x y} → is-equiv (yon-gpd {x} {y})
  yon-gpd-equiv {x} {y} =
    iso→equiv (λ f w → _∙ f) (λ g → g x refl) Path.unitl ε .snd
    where
      ε : (f : (w : A) → w ≡ x → w ≡ y) → (λ w z → pcom (λ _ → w) z (f x (λ _ → x))) ≡ f
      ε f i w g j = hcom (∂ j ∨ i) λ where
        k (j = i0) → w
        k (j = i1) → f (g (~ i)) (λ j → g (~ i ∨ j)) k
        k (i = i1) → f w g (j ∧ k)
        k (k = i0) → g (~ i ∧ j)

  yon-gpd-op-equiv : ∀ {x y : A} → is-equiv (yon-gpd-op {x} {y})
  yon-gpd-op-equiv {x} {y} = iso→equiv (λ g z → g ∙_) (λ g → g y refl) Path.unitr ε .snd
    where
      ε : (y₁ : (z : A) → y ≡ z → x ≡ z) → (λ z z₁ i → pcom (λ _ → x) (y₁ y (λ _ → y)) z₁ i) ≡ y₁
      ε f i w g j = hcom (∂ j ∨ i) λ where
        k (j = i0) → x
        k (j = i1) → g (i ∨ k)
        k (i = i1) → f w g j
        k (k = i0) → f (g i) (λ k → g (i ∧ k)) j

-- ∞-groupoid : ∀ {u} (A : Type u) → category u u
-- ∞-groupoid A .category.ob = A
-- ∞-groupoid A .category.hom = _≡_
-- ∞-groupoid A .category.yon = yon-gpd
-- ∞-groupoid A .category.yon-equiv = yon-gpd-equiv
-- ∞-groupoid A .category.yon-op-equiv = yon-gpd-op-equiv

-- Both yon-fun-equiv and yon-fun-op-equiv require parametricity (the
-- "free theorem" that polymorphic functions commute with post-composition),
-- which is independent of Cubical Type Theory with univalence.
--
-- The groupoid case (yon-gpd-equiv above) works because the total space
-- Σ w, w ≡ x is contractible — the based path space has a unique center
-- of contraction (x, refl), and the counit hcom continuously deforms any
-- (w, g) to it. For the functor case, the analogous space Σ Y, B → Y is
-- not contractible, so no such deformation exists.
--
-- Concretely, the counit for yon-fun-op-equiv would assert: for every
-- h : (Y : Type) → (B → Y) → (A → Y), we have h Y g = g ∘ (h B id).
-- This is naturality of h, which follows from parametricity in System F
-- but cannot be proven or disproven in vanilla Cubical Agda.
--
-- See: Cavallo 2024, "Internal and Observational Parametricity for
-- Cubical Agda" for a type theory where these would be provable.
-- See: https://homotopytypetheory.org/2016/02/24/parametricity-and-excluded-middle/
-- for why non-parametric polymorphic functions would imply LEM.
--
-- We assume parametricity as module parameters rather than postulating
-- it — this is --safe compatible (a hypothesis, not a postulate) and
-- makes the parametricity dependency explicit.

-- module _
--   {u : Level}
--   (yon-fun-equiv
--     : ∀ {A B : Type u}
--     → is-equiv (λ (f : A → B) (X : Type u) (k : X → A) → f ∘ k))
--   (yon-fun-op-equiv
--     : ∀ {A B : Type u}
--     → is-equiv (λ (f : A → B) (Y : Type u) (g : B → Y) → g ∘ f))
--   where

--   ∞-functor : category (u ₊) u
--   ∞-functor .category.ob           = Type u
--   ∞-functor .category.hom A B      = A → B
--   ∞-functor .category.yon f X      = f ∘_
--   ∞-functor .category.yon-equiv    = yon-fun-equiv
--   ∞-functor .category.yon-op-equiv = yon-fun-op-equiv

```
## Triangle Identity

The two canonical paths from `p ∙ (refl ∙ q)` to `p ∙ q` agree:
via associativity + right unit, or directly via left unit.

```agda

-- triangle
--   : ∀ {A : Type u} {x y z : A}
--   → (p : x ≡ y) (q : y ≡ z)
--   → Path.assoc p refl q ∙ ap (_∙ q) (Path.unitr p) ≡ ap (p ∙_) (Path.unitl q)
-- triangle p q = {!!}

```
## Pentagon Identity

```agda

-- pentagon
--   : ∀ {A : Type u} {v w x y z : A}
--   → (p : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z)
--   → Path.assoc p q (r ∙ s) ∙ Path.assoc (p ∙ q) r s
--     ≡ ap (p ∙_) (Path.assoc q r s)
--       ∙ Path.assoc p (q ∙ r) s
--       ∙ ap (_∙ s) (Path.assoc p q r)
-- pentagon p q r s = {!!}

```
