Lane Biocini
July 2026

The monoidal coherence cells as honest isomorphisms. Each
object-level coherence path — `⊗₀-assoc`, `⊗₀-unitl`, `⊗₀-unitr`,
and in the braided case `⊗₀-braid` — packages through `path→iso`
into an isomorphism whose underlying morphism is the transported
identity, and each naturality square is `hom-pathp→square` read
directly off the displaced cell: `⊗₁-assoc`, `⊗₁-unitl`,
`⊗₁-unitr`, and `⊗₁-braid` are already `PathP`s of derived
tensors over the object-level lines, so the classical squares
fall out with no intermediate naturality cell.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Iso where

open import Core.Type
open import Core.Base using (_≡_)
open import Core.Data.Sigma using (fst)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Base
open import Bb.CatsWithExplicitInterchange.Iso
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Bifunctor
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Braid

module monoidal-iso {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  open theory₁ M
  open theory C using (_⨾_)
  open iso C
  private module C = category C
```

## Coherence isomorphisms

`path→iso` sends each object-level coherence path to the
isomorphism carrying the transported identity, oriented as the
path is: the associator runs from the right-nested to the
left-nested tensor.

```agda
  ⊗-associator : (x y z : C.ob) → x ⊗₀ (y ⊗₀ z) ≅ (x ⊗₀ y) ⊗₀ z
  ⊗-associator x y z = path-iso.path→iso (⊗₀-assoc x y z)

  ⊗-unitor-l : (x : C.ob) → I ⊗₀ x ≅ x
  ⊗-unitor-l x = path-iso.path→iso (⊗₀-unitl x)

  ⊗-unitor-r : (x : C.ob) → x ⊗₀ I ≅ x
  ⊗-unitor-r x = path-iso.path→iso (⊗₀-unitr x)
```

## Naturality squares

Each displaced cell is the dependent-path form of naturality: a
`PathP` of derived tensors over the object-level coherence lines.
`hom-pathp→square` reads it off as the classical commuting square
through the underlying morphisms of the isomorphisms above — the
`.fst` of a `path→iso` is definitionally `path-iso.to` at the
same path, so each square lands on its stated boundary.

```agda
  ⊗-associator-natural
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      {z z'} (χ : C.hom z z')
    → (φ ⊗₁ (ψ ⊗₁ χ)) ⨾ ⊗-associator x' y' z' .fst
    ≡ ⊗-associator x y z .fst ⨾ ((φ ⊗₁ ψ) ⊗₁ χ)
  ⊗-associator-natural {x} {x'} φ {y} {y'} ψ {z} {z'} χ =
    hom-pathp→square (⊗₀-assoc x y z) (⊗₀-assoc x' y' z')
      (⊗₁-assoc φ ψ χ)

  ⊗-unitor-l-natural
    : ∀ {x x'} (φ : C.hom x x')
    → (C.idn I ⊗₁ φ) ⨾ ⊗-unitor-l x' .fst ≡ ⊗-unitor-l x .fst ⨾ φ
  ⊗-unitor-l-natural {x} {x'} φ = hom-pathp→square (⊗₀-unitl x) (⊗₀-unitl x') (⊗₁-unitl φ)

  ⊗-unitor-r-natural
    : ∀ {x x'} (φ : C.hom x x')
    → (φ ⊗₁ C.idn I) ⨾ ⊗-unitor-r x' .fst ≡ ⊗-unitor-r x .fst ⨾ φ
  ⊗-unitor-r-natural {x} {x'} φ = hom-pathp→square (⊗₀-unitr x) (⊗₀-unitr x') (⊗₁-unitr φ)
```

## The braiding

Over a braided structure the same two moves apply to the braid
cells `braid-theory` derives: `⊗₀-braid` packages into the
braiding isomorphism, and `⊗₁-braid` reads off as its naturality
square.

```agda
module braided-iso {o h} {C : category o h} {M : monoidal C}
  (B : braided M) where
  open monoidal M
  open theory C using (_⨾_)
  open iso C
  open braid-theory B
  private module C = category C

  ⊗-braiding : (x y : C.ob) → x ⊗₀ y ≅ y ⊗₀ x
  ⊗-braiding x y = path-iso.path→iso (⊗₀-braid x y)

  ⊗-braiding-natural
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
    → (φ ⊗₁ ψ) ⨾ ⊗-braiding x' y' .fst
    ≡ ⊗-braiding x y .fst ⨾ (ψ ⊗₁ φ)
  ⊗-braiding-natural {x} {x'} φ {y} {y'} ψ =
    hom-pathp→square (⊗₀-braid x y) (⊗₀-braid x' y') (⊗₁-braid φ ψ)
```
