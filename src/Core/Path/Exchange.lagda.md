The whisker–exchange calculus on iterated loops. A pair of 2-loops
slides past itself along two definitional interval lines — the two
crossing chiralities — inducing the Eckmann–Hilton identifications
of the vertical composite with its reverse; the full twist is their
discrepancy, and it vanishes definitionally on the unit flanks. The
conjugation between whiskered and plain composites is welded by
`pcom.unique` against fillers that hold by the pointwise unit laws,
with no Kan filling minted here beyond the ternary composite's own.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Path.Exchange where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Data.Pointed
open import Core.Path.Base using (Ω; Loop)
open import Core.Equiv.Base using (_≃_; iso→equiv)

Ω² : ∀ {u} → Type* u → Type u
Ω² A = Ω (Loop A)

```

## The whiskers and the exchange

The two whiskers pad a 2-loop by the identity on one side; the
exchange cells slide one whisker past the other, the chirality
recorded in which loop advances along the diagonal. Both are pure
interval terms: every stage of the slide is a composable pair on
the nose, so the lines carry no filling.

```agda

module _ {u} {A : Type u} {a : A} where

  whisker-r : Ω² (A , a) → refl ∙ refl ≡ refl ∙ refl
  whisker-r m = ap (_∙ refl) m

  whisker-l : Ω² (A , a) → refl ∙ refl ≡ refl ∙ refl
  whisker-l n = ap (refl ∙_) n

  exchange : (m n : Ω² (A , a))
           → whisker-r m ∙ whisker-l n ≡ whisker-l n ∙ whisker-r m
  exchange m n i =
      (λ j → m (j ∧ ~ i) ∙ n (j ∧ i))
    ∙ (λ j → m (~ i ∨ j) ∙ n (i ∨ j))

  exchange-op : (m n : Ω² (A , a))
              → whisker-l n ∙ whisker-r m ≡ whisker-r m ∙ whisker-l n
  exchange-op m n i =
      (λ j → m (j ∧ i) ∙ n (j ∧ ~ i))
    ∙ (λ j → m (i ∨ j) ∙ n (~ i ∨ j))

```

## The conjugation welds

The whiskered forms read back as the plain loops after conjugation
by the unit cell at `refl`; each weld is the uniqueness cell of the
ternary composite against a filler given pointwise by the unit
laws, and the paired welds seam through the shared unit cell.

```agda

  private
    ucell : refl {x = a} ∙ refl ≡ refl
    ucell = Path.unitr refl

  whisker-r-conj : (m : Ω² (A , a)) → pcom ucell (whisker-r m) ucell ≡ m
  whisker-r-conj m =
    pcom.unique ucell (whisker-r m) ucell
      (m , λ i → Path.unitr (m i))

  whisker-l-conj : (n : Ω² (A , a)) → pcom ucell (whisker-l n) ucell ≡ n
  whisker-l-conj n =
    pcom.unique ucell (whisker-l n) ucell
      (n , λ i → Path.unitl (n i))

  whisker-rl-conj : (m n : Ω² (A , a))
    → pcom ucell (whisker-r m ∙ whisker-l n) ucell ≡ m ∙ n
  whisker-rl-conj m n =
    pcom.unique ucell (whisker-r m ∙ whisker-l n) ucell
      ( m ∙ n
      , comp-pathp₂ _≡_ (whisker-r m) (whisker-l n) m n
          (λ i → Path.unitr (m i)) (λ i → Path.unitl (n i)))

  whisker-lr-conj : (m n : Ω² (A , a))
    → pcom ucell (whisker-l n ∙ whisker-r m) ucell ≡ n ∙ m
  whisker-lr-conj m n =
    pcom.unique ucell (whisker-l n ∙ whisker-r m) ucell
      ( n ∙ m
      , comp-pathp₂ _≡_ (whisker-l n) (whisker-r m) n m
          (λ i → Path.unitl (n i)) (λ i → Path.unitr (m i)))

```

## The Eckmann–Hilton crossings and the full twist

The two crossings commute the vertical composite through the two
exchange chiralities; the full twist is their discrepancy — the
generator of the route classification, oriented so that the
`exchange` line is the positive crossing. On a unit flank the two
exchange lines are the same interval term, so the crossings agree
definitionally and the full twist collapses by inverse
cancellation alone.

```agda

  eckmann-hilton⁺ : (m n : Ω² (A , a)) → m ∙ n ≡ n ∙ m
  eckmann-hilton⁺ m n =
      sym (whisker-rl-conj m n)
    ∙ ap (λ X → pcom ucell X ucell) (exchange m n)
    ∙ whisker-lr-conj m n

  eckmann-hilton⁻ : (m n : Ω² (A , a)) → m ∙ n ≡ n ∙ m
  eckmann-hilton⁻ m n =
      sym (whisker-rl-conj m n)
    ∙ ap (λ X → pcom ucell X ucell) (sym (exchange-op m n))
    ∙ whisker-lr-conj m n

  full-twist : (m n : Ω² (A , a)) → m ∙ n ≡ m ∙ n
  full-twist m n = eckmann-hilton⁺ m n ∙ sym (eckmann-hilton⁻ m n)

  full-twist-unit-r : (m : Ω² (A , a)) → full-twist m refl ≡ refl
  full-twist-unit-r m = Path.invr (eckmann-hilton⁺ m refl)

  full-twist-unit-l : (n : Ω² (A , a)) → full-twist refl n ≡ refl
  full-twist-unit-l n = Path.invr (eckmann-hilton⁺ refl n)

```

## Translation equivalences

Composition with a fixed path is an equivalence — the free half of
the collapse a loop-space tensor instance needs, with cancellation
supplying both round trips.

```agda

∙-pre-equiv : ∀ {u} {A : Type u} {x y z : A}
            → (l : x ≡ y) → (y ≡ z) ≃ (x ≡ z)
∙-pre-equiv l = iso→equiv (l ∙_) (sym l ∙_) (Path.lc l) (Path.lc (sym l))

∙-post-equiv : ∀ {u} {A : Type u} {x y z : A}
             → (r : y ≡ z) → (x ≡ y) ≃ (x ≡ z)
∙-post-equiv r = iso→equiv (_∙ r) (_∙ sym r) (Path.rc r) (Path.rc (sym r))
```
