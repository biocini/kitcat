Lane Biocini
October 2025

Core definitions for equivalences: contractible fibers, quasi-inverses,
and the fundamental construction `iso→equiv`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Equiv.Base where

open import Core.Transport.Base
open import Core.Transport.J
open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Sub
open import Core.Function.Retract public

record is-equiv {@0 u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    eqv-fibers : (y : B) → is-contr (fiber f y)

open is-equiv public
{-# INLINE is-equiv.constructor #-}

_≃_ Equiv
  : ∀ {@0 u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ {A = A → B} is-equiv; infix 6 _≃_
Equiv = _≃_
{-# BUILTIN EQUIV _≃_ #-}

eqvtofun : ∀ {@0 u v} {A : Type u} {B : Type v} → A ≃ B → A → B
eqvtofun e = fst e
{-# BUILTIN EQUIVFUN fst #-}

equiv-proof
  : ∀ {@0 u v} (T : Type u) (A : Type v) (w : T ≃ A) (a : A)
  → ∀ φ (p : Partial φ (fiber (w .fst) a)) → fiber (w .fst) a [ φ ↦ p ]
equiv-proof T A w a = is-contr→extend (eqv-fibers (w .snd) a)
{-# BUILTIN EQUIVPROOF equiv-proof #-}

record is-qinv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B → A
    sec : (x : A) → inv (f x) ≡ x
    retr : (y : B) → f (inv y) ≡ y

{-# INLINE is-qinv.constructor #-}

qinv
  : ∀ {u v} {A : Type u} {B : Type v}
  → (f : A → B) (g : B → A)
  → (sec : (x : A) → g (f x) ≡ x)
  → (retr : (y : B) → f (g y) ≡ y)
  → is-qinv f
qinv f g sec retr .is-qinv.inv = g
qinv f g sec retr .is-qinv.sec = sec
qinv f g sec retr .is-qinv.retr = retr


-- Credit: 1lab fiberwise-equiv module
module qinv {u v} {A : Type u} {B : Type v} {f : A → B} (e : is-qinv f) where
  private
    g = e .is-qinv.inv
    η = e .is-qinv.sec
    ε = e .is-qinv.retr

  module _ {y : B} ((x , p) : fiber f y) where
    faces0 : (i j : I) → Partial (∂ i ∨ ~ j) A
    faces0 i = λ where
      k (i = i0) → g y
      k (i = i1) → η (g y) k
      k (k = i0) → g (ε y (~ i))

    faces1 : (i j : I) → Partial (∂ i ∨ ~ j) A
    faces1 i = λ where
      k (i = i0) → g y
      k (i = i1) → η x k
      k (k = i0) → g (p (~ i))

    private
      π₀ : g y ≡ g y
      π₀ i = hcom (∂ i) (faces0 i)

      θ₀ : Square refl (ap g (sym (ε y))) (η (g y)) π₀
      θ₀ i j = hfil (∂ i) j (faces0 i)

      π₁ : g y ≡ x
      π₁ i = hcom (∂ i) (faces1 i)

      θ₁ : Square refl (ap g (sym p)) (η x)  π₁
      θ₁ i j = hfil (∂ i) j (faces1 i)

      fiber-sys : (i j : I) → Partial (∂ i ∨ ~ j) A
      fiber-sys i = λ where
        j (i = i0) → π₀ j
        j (i = i1) → π₁ j
        j (j = i0) → g y

      path : g y ≡ x
      path i = hcom (∂ i) (fiber-sys i)

      fiber-filler : Square π₀ refl π₁ path
      fiber-filler i j = hfil (∂ i) j (fiber-sys i)

      ι : Square (ap g (ε y)) (ap (λ z → g (f z)) path) (ap g p) refl
      ι i j = hcom (∂ i ∨ ∂ j) λ where
        k (i = i0) → θ₀ (~ j) (~ k)
        k (i = i1) → θ₁ (~ j) (~ k)
        k (j = i0) → η (path i) (~ k)
        k (j = i1) → g y
        k (k = i0) → fiber-filler i (~ j)

      filler : Square (ε y) (ap f path) p refl
      filler i j = hcom (∂ i ∨ ∂ j) λ where
        k (i = i0) → ε (ε y j) k
        k (i = i1) → ε (p j) k
        k (j = i0) → ε (f (path i)) k
        k (j = i1) → ε y k
        k (k = i0) → f (ι i j)

    unit : g (f x) ≡ x
    unit i = hcom (∂ i) λ where
      j (i = i0) → g (f x)
      j (i = i1) → path j
      j (j = i0) → g (p i)

    counit : f (g y) ≡ y
    counit = ε y

    private
      φ : Square refl p (sym (ε y)) (ap f (sym path))
      φ = Triangle.post (sym (ε y)) (ap f path) (sym p) (rrotate filler)

    adj : ap f unit ≡ ε (f x)
    adj i j = hcom (∂ i ∨ ∂ j) λ where
      k (i = i0) → f (cat.fill (ap g p) path j k)
      k (i = i1) → ε (p (~ k)) j
      k (j = i0) → f (g (p (i ∧ ~ k)))
      k (j = i1) → φ (~ k) (~ i)
      k (k = i0) → conn (ap (f ∘ g) p) (ε y) i j

    fiber-path : Path (fiber f y) (g y , ε y) (x , p)
    fiber-path i .fst = path i
    fiber-path i .snd = filler i

  contr : (y : B) → is-contr (fiber f y)
  contr y .center = g y , ε y
  contr y .paths = fiber-path

  to-equiv : is-equiv f
  to-equiv .eqv-fibers = contr

iso→equiv
  : ∀ {u v} {A : Type u} {B : Type v}
  → (f : A → B) (g : B → A)
  → (sec : (x : A) → g (f x) ≡ x)
  → (retr : (y : B) → f (g y) ≡ y)
  → A ≃ B
iso→equiv f g sec retr = f , qinv.to-equiv (qinv f g sec retr)

module Equiv {u v} {A : Type u} {B : Type v} (e : A ≃ B) where
  private module M = is-equiv (e .snd)
  fwd = e .fst

  c : (y : B) → fiber fwd y
  c y = M.eqv-fibers y .center

  inv : B → A
  inv y = c y .fst

  fibers : {y : B} (fb : fiber fwd y) → c y ≡ fb
  fibers {y} = M.eqv-fibers y .paths

  unit : (x : A) → inv (fwd x) ≡ x
  unit x i = fibers (x , λ _ → fwd x) i .fst

  counit : (y : B) → fwd (inv y) ≡ y
  counit y = c y .snd

eqvtoinv = Equiv.inv

id-equiv : ∀ {u} {A : Type u} → is-equiv (idfun A)
id-equiv .eqv-fibers y .center = y , refl
id-equiv .eqv-fibers y .paths (x , p) i = p (~ i) , λ j → p (~ i ∨ j)

aut : ∀ {u} {A : Type u} → A ≃ A
aut .fst = id
aut .snd = id-equiv

is-contr-equiv
  : ∀ {u v} {A : Type u} {B : Type v}
  → A ≃ B → is-contr B → is-contr A
is-contr-equiv e bcontr .center = e.inv (bcontr .center)
  where module e = Equiv e
is-contr-equiv e bcontr .paths x = ap e.inv (bcontr .paths (e.fwd x)) ∙ e.unit x
  where module e = Equiv e



```
