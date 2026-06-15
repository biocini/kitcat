Properties of the join.

-- Following 1lab, Homotopy.Join

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Join.Properties where

open import HData.Join.Type
open import HData.Join.Base

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport.Properties
  using (prop-inhabited→is-contr; is-prop-is-prop)
open import Core.Transport.Base using (is-prop→PathP)

private variable
  u v : Level
  A : Type u
  B : Type v
```


## Contractibility from one side

When `A` is contractible, `A ⋆ B` is contractible: every point
can be connected to `inl (center)`.

```agda

Join-is-contr-l
  : is-contr A → is-contr (A ⋆ B)
Join-is-contr-l h .center = inl (h .center)
Join-is-contr-l h .paths (inl x) j =
  inl (h .paths x j)
Join-is-contr-l h .paths (inr y) j =
  push (h .center) y j
Join-is-contr-l h .paths (push x y i) j =
  hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → inl (h .paths x (~ k ∨ j))
    k (i = i1) → push (h .paths x (~ k)) y j
    k (j = i0) → inl (h .paths x (~ k))
    k (j = i1) → push x y i
    k (k = i0) → push x y (i ∧ j)
```

The symmetric case: when `B` is contractible, `A ⋆ B` is
contractible.

```agda

Join-is-contr-r
  : is-contr B → is-contr (A ⋆ B)
Join-is-contr-r h .center = inr (h .center)
Join-is-contr-r h .paths (inl x) j =
  push x (h .center) (~ j)
Join-is-contr-r h .paths (inr y) j =
  inr (h .paths y j)
Join-is-contr-r h .paths (push x y i) j =
  hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → push x (h .paths y (~ k)) (~ j)
    k (i = i1) → inr (h .paths y (~ k ∨ j))
    k (j = i0) → inr (h .paths y (~ k))
    k (j = i1) → push x y i
    k (k = i0) → push x y (~ j ∨ i)
```


## Propositions are closed under joins

The proof eliminates on `A ⋆ B` into the proposition
`is-prop (A ⋆ B)`, which is itself a proposition by
`is-prop-is-prop`. This makes the `push` case automatic.

```agda

Join-is-prop
  : is-prop A → is-prop B → is-prop (A ⋆ B)
Join-is-prop {A = A} {B = B} pA pB x y =
  go x x y
  where
  go : A ⋆ B → is-prop (A ⋆ B)
  go = rec
    (λ a → is-contr→is-prop
      (Join-is-contr-l (prop-inhabited→is-contr pA a)))
    (λ b → is-contr→is-prop
      (Join-is-contr-r (prop-inhabited→is-contr pB b)))
    (λ a b → is-prop-is-prop _
      (is-contr→is-prop
        (Join-is-contr-l (prop-inhabited→is-contr pA a)))
      (is-contr→is-prop
        (Join-is-contr-r (prop-inhabited→is-contr pB b))))
```
