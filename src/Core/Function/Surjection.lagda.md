Surjections: maps with merely inhabited fibers.

A map `f : A → B` is surjective if every element of B has a preimage, at
least in the sense that the fiber is merely inhabited. This is weaker than
having a section (split surjectivity), which would require an actual choice
of preimage.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Function.Surjection where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Trunc
open Trunc
open import Core.Equiv
open import Core.Function.Embedding
open import Core.HLevel
open import Core.Transport.Properties using (prop-inhabited→is-contr)

private variable
  u v : Level
  A B : Type u
```


## Core Definitions

```agda
is-surjective : {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
is-surjective f = ∀ b → ∥ fiber f b ∥

_↠_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ↠ B = Σ f ∶ (A → B) , is-surjective f
infix 6 _↠_

is-split-surjective : {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
is-split-surjective f = ∀ b → fiber f b
```


## Conversions

```agda

equiv→surjective
  : {A : Type u} {B : Type v} {f : A → B}
  → is-equiv f → is-surjective f
equiv→surjective e b = ∣ e .eqv-fibers b .center ∣

split-surjective→surjective
  : {A : Type u} {B : Type v} {f : A → B}
  → is-split-surjective f → is-surjective f
split-surjective→surjective split b = ∣ split b ∣

surjective+embedding→equiv
  : {A : Type u} {B : Type v} {f : A → B}
  → is-surjective f → is-embedding f → is-equiv f
surjective+embedding→equiv {f = f} surj emb .eqv-fibers b =
  prop-inhabited→is-contr (emb b) (out (emb b) (surj b))
```
