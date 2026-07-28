Lane Biocini
July 2026

An indiscrete-monoidal builder. Given a category whose hom types
are all contractible, any object-level tensor structure extends
uniquely to a full `monoidal` structure: every morphism-level
obligation is a statement in a family of contractible types, so
it is discharged from `hom-contr` alone.

The object level enters as the record itself: the builder's
input is a `monoidal-axioms₀`, its interchange field already in
the ♭ shape — the record's field, an instance's proof, and a
builder's input are one shape, and the flat form is that shape.
The builder's own job is purely the hom level: `⊗₁-composite`
is a Π into contractible homs, hence contractible, so
`⊗₁-interchange♭` and `⊗₁-unit` are centers of `PathP`s into
contractible families, `⊗₁-spine-contr` is a Σ of contractibles,
and the enrichment law is a path in a contractible hom type.

This is the carrier-agnostic scaffold for the `absorb-coh`
independence countermodel: the object tier is left entirely
open, so a later phase can plug in a specific `monoidal-axioms₀`
without touching any morphism-level reasoning.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Indiscrete where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Nat.Type using (Z)
open import Core.Kan using (is-contr→is-prop; _∙_)
open import Core.HLevel.Base using (PathP-is-contr; Π-is-hlevel; Σ-is-hlevel)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Braid
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Hexagon
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
  indiscrete-axioms₁ .monoidal-axioms₁.⊗₁-interchange♭ Û V̂ =
    PathP-is-contr ⊗₁-composite-contr _ _ .center
  indiscrete-axioms₁ .monoidal-axioms₁.⊗₁-spine-contr φ ψ =
    Σ-is-hlevel Z hom-contr λ σ →
    Σ-is-hlevel Z (PathP-is-contr ⊗₁-composite-contr _ _) λ P →
    Σ-is-hlevel Z (PathP-is-contr ⊗₁-composite-contr _ _) λ Q →
    PathP-is-contr (PathP-is-contr ⊗₁-composite-contr _ _) _ _
  indiscrete-axioms₁ .monoidal-axioms₁.⊗₁-unit φ = PathP-is-contr hom-contr _ _ .center
  indiscrete-axioms₁ .monoidal-axioms₁.⊗₁-emb-⨾ φ₁ φ₂ δ₁ δ₂ = is-contr→is-prop hom-contr _ _

  indiscrete-monoidal : monoidal C
  indiscrete-monoidal .monoidal.axioms₀ = M₀
  indiscrete-monoidal .monoidal.axioms₁ = indiscrete-axioms₁
```

## The braided builders

The same discipline one structure out: the caller's data is the
field's own shape — the object-tier flank swap, then the two
object-tier hexagons stated on the derived `⊗₀-braid♭` — and
every morphism-grade field is a center of a (nested) `PathP`
into the contractible `⊗₁-composite` family. Nothing else is
asked: the displaced flank swap rides its level-0 lines, and the
displaced hexagons are squares into contractible fibers, the
`⊗₁-spine-contr` idiom.

```agda
  module _
    (⊗₀-flank-swap♭
      : ∀ {A B : ⊗₀-composite}
      → is-⊗₀-representable A → is-⊗₀-representable B
      → A ▵₀ B ≡ B ▿₀ A)
    where

    indiscrete-braided : braided indiscrete-monoidal
    indiscrete-braided .braided.⊗₀-flank-swap♭ = ⊗₀-flank-swap♭
    indiscrete-braided .braided.⊗₁-flank-swap♭ Û V̂ = PathP-is-contr ⊗₁-composite-contr _ _ .center

    open braided indiscrete-braided using (⊗₀-braid♭)

    module _
      (⊗₀-hexagon-r♭
        : ∀ {F G H : ⊗₀-composite}
          (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
          (W : is-⊗₀-representable H)
        → ⊗₀-braid♭ U (V ●₀ W)
        ≡ ap (λ X → X ▿₀ H) (⊗₀-braid♭ U V)
          ∙ ap (λ X → G ▿₀ X) (⊗₀-braid♭ U W))
      (⊗₀-hexagon-l♭
        : ∀ {F G H : ⊗₀-composite}
          (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
          (W : is-⊗₀-representable H)
        → ⊗₀-braid♭ (U ●₀ V) W
        ≡ ap (λ X → F ▿₀ X) (⊗₀-braid♭ V W)
          ∙ ap (λ X → X ▿₀ G) (⊗₀-braid♭ U W))
      where

      indiscrete-braided-coherent : braided-coherent indiscrete-braided
      indiscrete-braided-coherent .braided-coherent.⊗₀-hexagon-r♭ = ⊗₀-hexagon-r♭
      indiscrete-braided-coherent .braided-coherent.⊗₁-hexagon-r♭ Û V̂ Ŵ =
        PathP-is-contr (PathP-is-contr ⊗₁-composite-contr _ _) _ _ .center
      indiscrete-braided-coherent .braided-coherent.⊗₀-hexagon-l♭ = ⊗₀-hexagon-l♭
      indiscrete-braided-coherent .braided-coherent.⊗₁-hexagon-l♭ Û V̂ Ŵ =
        PathP-is-contr (PathP-is-contr ⊗₁-composite-contr _ _) _ _ .center
```
