MiscFloor-20260720: floor measurement for the coherence modules'
`Miscellaneous` profile bucket. Same import list and section header
as `Cat.Depreciated.Displayed.Coherence`, one trivial definition — cold Total
here is the fixed pipeline overhead (deserialization, parsing,
serialization, highlighting) that a coherence module pays before
any of its own code is typed.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.MiscFloor-20260720 where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp; comp-pathp₁-ap)
open import Core.Transport.Properties using (is-prop→SquareP)
open import Core.Transport.J using (subst)
open import Cat.Depreciated.Type
open import Cat.Depreciated.Base
open import Cat.Depreciated.Coherence
open import Cat.Depreciated.Displayed
open import Cat.Depreciated.Displayed.Base

module _ {o h o' h'} {C : category o h} (D : categoryᴰ C o' h') where
  open category C
  open theory C
  open categoryᴰ D
  open theoryᴰ D

  probe : ∀ {x y} (f : hom x y) → hom x y
  probe f = f
```
