The rotation family and the circle's multiplication. `rot` is the
generating self-path family on the circle — `rot base = loop`, with
the loop case one `hcom` square commuting the loop past itself.
`mult` is the H-space multiplication with `rot` as its loop case;
its left unit law is definitional, the right unit law is a constant
square, and each left translation is an equivalence by a
propositional `PathP` over the loop.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Circle.Mult where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Equiv.Base using (is-equiv; id-equiv)
open import Core.Equiv.Properties using (is-equiv-is-prop)

open import HData.Circle.Type
open import HData.Circle.Base

rot : (x : Circle) → x ≡ x
rot base = loop
rot (loop i) j = hcom (∂ i ∨ ∂ j) λ where
  k (k = i0) → base
  k (i = i0) → loop (j ∨ ~ k)
  k (i = i1) → loop (j ∧ k)
  k (j = i0) → loop (i ∨ ~ k)
  k (j = i1) → loop (i ∧ k)

mult : Circle → Circle → Circle
mult base y     = y
mult (loop i) y = rot y i

mult-unit-l : (y : Circle) → mult base y ≡ y
mult-unit-l y = refl

mult-unit-r : (x : Circle) → mult x base ≡ x
mult-unit-r = ind (λ x → mult x base ≡ x) refl (λ i → refl)

mult-equiv : (x : Circle) → is-equiv (mult x)
mult-equiv = ind (λ x → is-equiv (mult x)) id-equiv
  (is-prop→PathP (λ i → is-equiv-is-prop (mult (loop i))) id-equiv id-equiv)
```
