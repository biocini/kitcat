Lane Biocini
July 2026

The monoidal structure's coherence maps are honest
isomorphisms. The associator and the two unitors are the
object-level paths `⊗-assoc`, `⊗-unitl`, and `⊗-unitr`
transported through `idtoiso`. Their naturality — recorded in
`Cat.Monoidal.Bifunctor` as dependent paths of 2-cells — reads
as the classical commuting squares via `hom-PathP→square`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Iso where

open import Core.Data.Sigma using (fst)
open import Core.Base using (_≡_)

open import Cat.Monoidal.Bifunctor using (assoc-nat; unitl-nat; unitr-nat)
open import Cat.Base using (module Cat)
open import Cat.Iso using (idtoiso; hom-PathP→square)
open import Cat.Monoidal
open import Cat.Type

module _ {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  private module C = category C
  open Cat C using (_≅_)
```

## Coherence isomorphisms

`idtoiso` sends each object-level coherence path to an
isomorphism whose underlying morphism is the transported
identity.

```agda
  ⊗-associator : (x y z : C.ob) → ((x ⊗ y) ⊗ z) ≅ (x ⊗ (y ⊗ z))
  ⊗-associator x y z = idtoiso C (⊗-assoc x y z)

  ⊗-unitor-l : (x : C.ob) → (I ⊗ x) ≅ x
  ⊗-unitor-l x = idtoiso C (⊗-unitl x)

  ⊗-unitor-r : (x : C.ob) → (x ⊗ I) ≅ x
  ⊗-unitor-r x = idtoiso C (⊗-unitr x)
```

## Naturality squares

Each `Bifunctor` `PathP` naturality is the dependent-path form
of a commuting square. `hom-PathP→square` reads it off as the
classical square through the underlying maps of the coherence
isomorphisms above.

```agda
  ⊗-associator-natural
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y') {z z'} (θ : C.hom z z')
    → ((φ ⊗ₕ ψ) ⊗ₕ θ) C.⨾ ⊗-associator x' y' z' .fst
      ≡ ⊗-associator x y z .fst C.⨾ (φ ⊗ₕ (ψ ⊗ₕ θ))
  ⊗-associator-natural {x}{x'} φ {y}{y'} ψ {z}{z'} θ =
    hom-PathP→square C (⊗-assoc x y z) (⊗-assoc x' y' z') (assoc-nat M φ ψ θ)

  ⊗-unitor-l-natural
    : ∀ {x x'} (φ : C.hom x x')
    → ((C.idn I) ⊗ₕ φ) C.⨾ ⊗-unitor-l x' .fst ≡ ⊗-unitor-l x .fst C.⨾ φ
  ⊗-unitor-l-natural {x}{x'} φ =
    hom-PathP→square C (⊗-unitl x) (⊗-unitl x') (unitl-nat M φ)

  ⊗-unitor-r-natural
    : ∀ {x x'} (φ : C.hom x x')
    → (φ ⊗ₕ (C.idn I)) C.⨾ ⊗-unitor-r x' .fst ≡ ⊗-unitor-r x .fst C.⨾ φ
  ⊗-unitor-r-natural {x}{x'} φ =
    hom-PathP→square C (⊗-unitr x) (⊗-unitr x') (unitr-nat M φ)
```
