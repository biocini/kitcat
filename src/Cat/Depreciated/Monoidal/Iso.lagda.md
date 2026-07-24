Lane Biocini
July 2026

The monoidal coherence cells as honest isomorphisms. Each
object-level coherence path packages through `path→iso` into an
isomorphism whose underlying morphism is the transported identity,
and each naturality square is `hom-pathp→square` read directly off
the displaced cell: the displaced cells are already `PathP`s of
derived tensors over the object-level lines, so the classical
squares fall out with no intermediate naturality cell. The
associator is insensitive to the interchange fields; the unitors
ride the choice, so their isomorphisms live in the parametrized
section, instantiated at either field. The archived single-field
form is `Cat.Depreciated.Monoidal.Legacy.Iso`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Monoidal.Iso where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma using (fst)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Base
open import Cat.Depreciated.Iso
open import Cat.Depreciated.Monoidal
open import Cat.Depreciated.Monoidal.Bifunctor

module monoidal-iso {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  open bifunctor-theory M
  open theory C using (_⨾_)
  open iso C
  private module C = category C
```

## The associator

```agda
  ⊗-associator : (x y z : C.ob) → x ⊗₀ (y ⊗₀ z) ≅ (x ⊗₀ y) ⊗₀ z
  ⊗-associator x y z = path-iso.path→iso (⊗₀-assoc x y z)

  ⊗-associator-natural
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      {z z'} (χ : C.hom z z')
    → (φ ⊗₁ (ψ ⊗₁ χ)) ⨾ ⊗-associator x' y' z' .fst
    ≡ ⊗-associator x y z .fst ⨾ ((φ ⊗₁ ψ) ⊗₁ χ)
  ⊗-associator-natural {x} {x'} φ {y} {y'} ψ {z} {z'} χ =
    hom-pathp→square (⊗₀-assoc x y z) (⊗₀-assoc x' y' z')
      (⊗₁-assoc φ ψ χ)
```

## The unitors, per interchange

```agda
  module unitor-iso
    (ι₀ : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y)
    (ι₁ : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        → PathP (λ i → ⊗₁-composite (ι₀ x y i) (ι₀ x' y' i))
                (⊗₁-emb φ ▾₁ ψ) (φ ▴₁ ⊗₁-emb ψ))
    where

    open unitors ι₀
    open unitors₁ ι₀ ι₁

    ⊗-unitor-l : (x : C.ob) → I ⊗₀ x ≅ x
    ⊗-unitor-l x = path-iso.path→iso (⊗₀-unitl x)

    ⊗-unitor-r : (x : C.ob) → x ⊗₀ I ≅ x
    ⊗-unitor-r x = path-iso.path→iso (⊗₀-unitr x)

    ⊗-unitor-l-natural
      : ∀ {x x'} (φ : C.hom x x')
      → (C.idn I ⊗₁ φ) ⨾ ⊗-unitor-l x' .fst ≡ ⊗-unitor-l x .fst ⨾ φ
    ⊗-unitor-l-natural {x} {x'} φ =
      hom-pathp→square (⊗₀-unitl x) (⊗₀-unitl x') (⊗₁-unitl φ)

    ⊗-unitor-r-natural
      : ∀ {x x'} (φ : C.hom x x')
      → (φ ⊗₁ C.idn I) ⨾ ⊗-unitor-r x' .fst ≡ ⊗-unitor-r x .fst ⨾ φ
    ⊗-unitor-r-natural {x} {x'} φ =
      hom-pathp→square (⊗₀-unitr x) (⊗₀-unitr x') (⊗₁-unitr φ)
```
