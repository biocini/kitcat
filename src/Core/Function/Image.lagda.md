Image factorization: the image of a map as a subtype of the codomain.

Every function `f : A → B` factors as A → im(f) → B where:
- The first map is surjective (onto the image)
- The second map is an embedding (inclusion of a subtype)

This is the surjection-embedding factorization from homotopy type theory.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Function.Image where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Trunc
open Trunc
open import Core.Function.Embedding
open import Core.Equiv
open import Core.Function.Surjection

private variable
  u v : Level
  A B : Type u
```


## The Image

```agda

module _ {u v} {A : Type u} {B : Type v} where
  im : (A → B) → Type (u ⊔ v)
  im f = Σ b ∶ B , ∥ fiber f b ∥

  im-incl : (f : A → B) → im f → B
  im-incl f = fst

  im-incl-is-embedding : (f : A → B) → is-embedding (im-incl f)
  im-incl-is-embedding f = Σ-prop-embedding (λ _ → squash)

  im-factor : (f : A → B) → A → im f
  im-factor f a = f a , ∣ a , refl ∣

  im-factor-is-surjective : (f : A → B) → is-surjective (im-factor f)
  im-factor-is-surjective f (b , inhab) =
    map (λ { (a , p) → a , Σ-prop-path (λ _ → squash) p }) inhab

  im-triangle : (f : A → B) (a : A) → im-incl f (im-factor f a) ≡ f a
  im-triangle f a = refl
```
