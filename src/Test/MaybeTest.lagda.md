A path endpoint in builtin `Maybe` computes: `p i0` at a
`nothing`-loop is `nothing`, definitionally.

```agda
{-# OPTIONS --safe --erased-cubical #-}
module Test.MaybeTest where

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Maybe

private variable
  A : Set

refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
refl {x = x} i = x

test : (p : nothing {A = A} ≡ nothing) → p i0 ≡ nothing
test p = refl
```
