Test: function-based code for thinnings.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Test.CodeTest where

open import Core.Type
open import Core.Base using (_≡_; refl; ap; is-set; is-prop)
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type

open Core.Type using (⊤; tt)

private variable
  u : Level
  K : Type u
  iz jz : List K

data ⊥ : Type where

code : {iz jz : List K} → iz ≤ jz → iz ≤ jz → Type u
code (o' θ) (o' φ) = code θ φ
code (os θ) (os φ) = code θ φ
code oz     oz     = ⊤
code (o' _) (os _) = ⊥
code (os _) (o' _) = ⊥

refl-code : (θ : iz ≤ jz) → code θ θ
refl-code (o' θ) = refl-code θ
refl-code (os θ) = refl-code θ
refl-code oz     = tt

code-is-prop : (θ φ : iz ≤ jz) → is-prop (code θ φ)
code-is-prop (o' θ) (o' φ) = code-is-prop θ φ
code-is-prop (os θ) (os φ) = code-is-prop θ φ
code-is-prop oz     oz   tt tt = refl
code-is-prop (o' _) (os _) ()
code-is-prop (os _) (o' _) ()

```
