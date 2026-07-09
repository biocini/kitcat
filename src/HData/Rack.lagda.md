```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Rack where

open import Core.Type
open import Core.Data.Sigma
open import Core.Base
open import Core.Kan
open import Core.Equiv
open import Core.Equiv

module _ {u} (A : Type u) where
  data Ra : Type u where
    [_] : A → Ra
    _▷_ : Ra → Ra → Ra
    _◁_ : Ra → Ra → Ra
    sec  : ∀ x y → (x ▷ y) ◁ x ≡ y
    retr  : ∀ x y → x ▷ (y ◁ x) ≡ y
    coh : ∀ x y → ap (x ▷_) (sec x y) ≡ retr x (x ▷ y)
    sdist : ∀ x y z → (x ▷ y) ▷ z ≡ (x ▷ z) ▷ (y ▷ z)

  infixr 60 _▷_
  -- (x ▷ y) ▷ (y ◁ x) ≡ (x ▷ (y ◁ x)) ▷ (y ▷ (y ◁ x))
  -- (x ▷ y) ▷ (y ◁ x) ≡ y ▷ (y ▷ (y ◁ x))

  sd : ∀ x y z → (x ▷ y) ▷ z ≡ (x ▷ z) ▷ (y ▷ z)
  sd x y [ x₁ ] = {!!}
  sd x y (z ▷ z₁) = {!!}
  sd x y (z ◁ z₁) = {!!}
  sd x y (sec z z₁ i) = {!!}
  sd x y (retr z z₁ i) = {!!}
  sd x y (coh z z₁ i i₁) = {!!}
  sd x y (sdist z z₁ z₂ i) = {!!}

  Ra-is-equiv : (X : Ra) → Ra ≃ Ra
  Ra-is-equiv X .fst = X ▷_
  Ra-is-equiv X .snd = is-half-adj→is-equiv φ where
    φ : is-half-adj (X ▷_)
    φ .is-half-adj.inv = _◁ X
    φ .is-half-adj.sec = sec X
    φ .is-half-adj.retr = retr X
    φ .is-half-adj.adj = coh X
```
