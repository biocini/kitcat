Lane Biocini
July 2026

An indiscrete-monoidal builder for the two-field record. Given a
category whose hom types are all contractible, any object-level
tensor structure extends uniquely to a full `monoidal` structure:
every morphism-level obligation is a statement in a family of
contractible types, so it is discharged from `hom-contr` alone —
both displaced interchange fields identically, which is the
grading's point: at the hom level the chirality costs nothing,
and whatever separates the fields lives entirely at the object
tier the caller supplies.

The object level enters as the record itself: the builder's input
is a `monoidal-axioms₀`, its interchange fields already in the ♭
shape — the record's field, an instance's proof, and a builder's
input are one shape. The builder's own job is purely the hom
level: `⊗₁-composite` is a Π into contractible homs, hence
contractible, so the displaced interchanges and `⊗₁-unit` are
centers of `PathP`s into contractible families, the displaced pull
fiber is a Σ of contractibles, and the enrichment law is a path in
a contractible hom type. The archived single-field form is
`Cat.Depreciated.Monoidal.Legacy.Indiscrete`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Monoidal.Indiscrete where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Nat.Type using (Z)
open import Core.Kan using (is-contr→is-prop)
open import Core.HLevel.Base using (PathP-is-contr; Π-is-hlevel; Σ-is-hlevel)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Monoidal
```

## The builder

```agda
module _ {o h} {C : category o h}
  (hom-contr : ∀ {a b} → is-contr (category.hom C a b))
  (M₀ : monoidal-axioms₀ C)
  where

  open monoidal-axioms₀ M₀
  open theory₀ M₀
  open tensor-virtual₁ C I
  private module C = category C

  private
    ⊗₁-composite-contr : ∀ {F F' : ⊗₀-composite} → is-contr (⊗₁-composite F F')
    ⊗₁-composite-contr =
      Π-is-hlevel Z λ γ → Π-is-hlevel Z λ γ' → Π-is-hlevel Z λ δ →
        hom-contr

  indiscrete-axioms₁ : monoidal-axioms₁ M₀
  indiscrete-axioms₁ .monoidal-axioms₁.⊗₁-emb φ γ γ' δ = hom-contr .center
  indiscrete-axioms₁ .monoidal-axioms₁.ι⁺₁ Û V̂ =
    PathP-is-contr ⊗₁-composite-contr _ _ .center
  indiscrete-axioms₁ .monoidal-axioms₁.ι⁻₁ Û V̂ =
    PathP-is-contr ⊗₁-composite-contr _ _ .center
  indiscrete-axioms₁ .monoidal-axioms₁.⊗₁-pull-contr φ ψ =
    Σ-is-hlevel Z hom-contr λ σ →
    PathP-is-contr ⊗₁-composite-contr _ _
  indiscrete-axioms₁ .monoidal-axioms₁.⊗₁-unit φ =
    PathP-is-contr hom-contr _ _ .center
  indiscrete-axioms₁ .monoidal-axioms₁.⊗₁-emb-⨾ φ₁ φ₂ δ₁ δ₂ =
    is-contr→is-prop hom-contr _ _

  indiscrete-monoidal : monoidal C
  indiscrete-monoidal .monoidal.axioms₀ = M₀
  indiscrete-monoidal .monoidal.axioms₁ = indiscrete-axioms₁
```
