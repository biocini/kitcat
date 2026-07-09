Perturbing the interchange law of an indiscrete monoidal
structure by a unit-supported loop family `ω` conjugates the
`absorb-coh` defect. The left-hand absorption side is
transported unchanged, while the right-hand interchange side
acquires the loop `ζ = ω I x I r` as a conjugating factor.
Consequently any hypothetical `absorb-coh` witness on the
twisted structure `Mω` forces `ω I x I r ≡ refl`.

The base structure `M` and the twist `Mω` share `te`, `tu`,
`tcc`, and `tye` definitionally, so every operation not routed
through interchange (`_⊗_`, `noy`, `yon`, `tensor-emb-comp-pt`,
`tensor-noy-composite`, `tensor-yon-idpt`) reduces identically
for both. Only interchange-routed operations differ, and the
difference is exactly the loop family.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Twist where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Transport.J using (subst)
open import Core.Path.Base using (conj-cancel)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding using (equiv→lc)

open import Cat.Type
open import Cat.Monoidal
open import Cat.Monoidal.Indiscrete
```

## The two absorption coherence sides

```agda
module _ {o h} {C : category o h} where
  private module C = Virtual C
  open C using (ob)

  module _ (N : monoidal C) where
    private module N = monoidal N

    absorb-coh-lhs
      : (x r : ob) → N.noy N.I (N.noy x r) ≡ N.noy x r
    absorb-coh-lhs x r = N.absorb-l (N.noy x r)

    absorb-coh-rhs
      : (x r : ob) → N.noy N.I (N.noy x r) ≡ N.noy x r
    absorb-coh-rhs x r =
      N.tensor-interchange N.I x N.I r
      ∙ ap (λ t → N.tensor-emb x t r) (N.absorb-r N.I)
```

## The base structure and its twist

```agda
  module _
    (hom-contr : ∀ {a b} → is-contr (C.hom a b))
    (te : ob → ob → ob → ob)
    (tu : Σ i ∶ ob
        , is-equiv (λ (r : ob) → te i i r)
        × is-equiv (λ (l : ob) → te i l i))
    (tcc : (x y : ob)
         → is-contr (fiber te (λ l r → te x l (te y (tu .fst) r))))
    (tint : (x y l r : ob)
          → te x l (te y (tu .fst) r) ≡ te y (te x l (tu .fst)) r)
    (tye : (x : ob) → te x (tu .fst) (tu .fst) ≡ x)
    (ω : (x y l r : ob)
       → te y (te x l (tu .fst)) r ≡ te y (te x l (tu .fst)) r)
    where

    M : monoidal C
    M = indiscrete-monoidal hom-contr te tu tcc tint tye

    Mω : monoidal C
    Mω = indiscrete-monoidal hom-contr te tu tcc
      (λ x y l r → tint x y l r ∙ ω x y l r) tye

    private
      module M0 = monoidal M
      module Mw = monoidal Mω

      I : ob
      I = tu .fst
```

## Twist algebra

The base coherence `absorb-coh-lhs M ≡ absorb-coh-rhs M` is a
hypothesis, not a theorem: it is exactly what an `absorb-coh`
field would supply. Given a twisted coherence and the base
coherence, the loop `ω I x I r` is forced to be trivial.

```agda
    module _ (Hω : ω I I I I ≡ refl) where

      twist-tyc-III
        : Mw.tensor-yon-composite I I I
        ≡ M0.tensor-yon-composite I I I
      twist-tyc-III = ap (M0.tensor-emb-comp-pt I I I I ∙_) core
        where
          core : tint I I I I ∙ ω I I I I ≡ tint I I I I
          core =
            ap (tint I I I I ∙_) Hω
            ∙ Path.unitr (tint I I I I)

      tyc→⊗-comp : Mw.⊗-comp-eq I I ≡ M0.⊗-comp-eq I I
      tyc→⊗-comp =
        ap (λ b →
          sym (M0.tensor-yon-eval (I M0.⊗ I))
          ∙ b ∙ ap (M0.yon I) (M0.tensor-yon-eval I))
          twist-tyc-III

      ⊗-idem-eq : Mw.⊗-idem ≡ M0.⊗-idem
      ⊗-idem-eq = ap (_∙ M0.tensor-yon-idpt) tyc→⊗-comp

      module _ (x r : ob) where

        α : te I I (te x I r) ≡ te x (te I I I) r
        α = M0.tensor-interchange I x I r

        ζ : te x (te I I I) r ≡ te x (te I I I) r
        ζ = ω I x I r

        β : te x (te I I I) r ≡ te x I r
        β = ap (λ t → te x t r) (M0.absorb-r I)

        λ-noy-idem
          : Mw.noy-I-idem (M0.noy x r) ≡ M0.noy-I-idem (M0.noy x r)
        λ-noy-idem =
          ap (λ p → sym (subst
            (λ t → M0.noy t (M0.noy x r)
                 ≡ M0.noy I (M0.noy I (M0.noy x r)))
            p (M0.tensor-noy-composite I I (M0.noy x r))))
            ⊗-idem-eq

        lhs-eq : absorb-coh-lhs Mω x r ≡ absorb-coh-lhs M x r
        lhs-eq = ap (equiv→lc M0.tensor-unit-eqvl) λ-noy-idem

        ρ-yon-idem : Mw.yon-I-idem I ≡ M0.yon-I-idem I
        ρ-yon-idem =
          ap2s (λ p q → sym (subst
            (λ t → M0.yon t I ≡ M0.yon I (M0.yon I I)) p q))
            ⊗-idem-eq twist-tyc-III

        ρ : Mw.absorb-r I ≡ M0.absorb-r I
        ρ = ap (equiv→lc M0.tensor-unit-eqvr) ρ-yon-idem

        β-eq : ap (λ t → te x t r) (Mw.absorb-r I) ≡ β
        β-eq = ap (ap (λ t → te x t r)) ρ

        rhs-expand : absorb-coh-rhs Mω x r ≡ α ∙ ζ ∙ β
        rhs-expand =
          sym (Path.assoc α ζ (ap (λ t → te x t r) (Mw.absorb-r I)))
          ∙ ap (λ b → α ∙ ζ ∙ b) β-eq

        reduce
          : ((x r : ob) → absorb-coh-lhs M x r ≡ absorb-coh-rhs M x r)
          → absorb-coh-lhs Mω x r ≡ absorb-coh-rhs Mω x r
          → ω I x I r ≡ refl
        reduce cohM g =
          conj-cancel α β ζ
            (sym (cohM x r) ∙ sym lhs-eq ∙ g ∙ rhs-expand)
```

## The reduction theorem

A base coherence `cohM` and a hypothetical twisted coherence
`g` together force the unit-supported loop `ω I x I r` to be
`refl`, provided its diagonal component `ω I I I I` is already
trivial.

```agda
    twist-reduces-to-omega
      : (Hω : ω I I I I ≡ refl)
      → ((x r : ob) → absorb-coh-lhs M x r ≡ absorb-coh-rhs M x r)
      → (x r : ob)
      → absorb-coh-lhs Mω x r ≡ absorb-coh-rhs Mω x r
      → ω I x I r ≡ refl
    twist-reduces-to-omega Hω cohM x r g = reduce Hω x r cohM g
```
