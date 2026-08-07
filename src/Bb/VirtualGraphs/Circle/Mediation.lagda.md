Mediation over the circle model. Both cuts compute to the
multiplication and both half-twists sit at the axiom, so each clause
computes to a path in the circle: the left side is the axiom, and the
right side is a word in the candidate pair against the axiom.

Every translation of the circle is an equivalence, in both hands, so
the equivalence tier holds at every pair and is contractible there.
The two right sides assemble into a shear map, which is an
equivalence over an equivalence; the type of mediating pairs is one
of its fibers, so it contracts, and the framed pairs contract with
it. At the axiom pair the mediation type and the pair identification
type each carry one winding per component. The self-referential
clauses read the same type there.

This module uses `--cubical`: it consumes `loop-nontrivial` in an
unerased position, which rides the winding equivalence `ua` builds.
The circle modules form their own import island; no `--erased-cubical`
module imports them unerased.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.VirtualGraphs.Circle.Mediation where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Empty using (⊥)
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.Equiv
open import Core.Function.Embedding
  using (is-equiv→is-embedding; is-embedding→ap-equiv)

open import HData.Circle
open Circle using (base; loop; rot; ind; mult; mult-unit-r; mult-equiv;
                   mult-r-equiv; loop-nontrivial)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Mediation
open import Bb.VirtualGraphs.Circle.Model
```

## The clauses at the circle

Left multiplication by the axiom is the identity on the nose, so each
clause computes to a path in the circle. The left side of each is the
axiom. The right side of the first is the positive component against
the axiom, and the right side of the second is `corr₁` against it.

```agda
open mediation circle.model (λ _ → base) (λ _ → base)
  circle.stable circle.C⁺ circle.C⁻

clause₀-value : (p : pair tt) → clause₀ tt p ≡ (base ≡ mult (p .snd) base)
clause₀-value _ = refl

clause₁-value : (p : pair tt)
  → clause₁ tt p
  ≡ (base ≡ mult (mult (p .fst) (mult (p .snd) (mult (p .snd) (p .snd)))) base)
clause₁-value _ = refl
```

At the axiom pair each clause is the loop space of the circle at the
axiom. The constant witness and its `rot`-shift are two witnesses,
and they separate by one winding.

```agda
m₀ m₁ : mediates₂ tt (base , base)
m₀ = refl , refl
m₁ = m₀ .fst ∙ rot base , m₀ .snd ∙ rot base

mediates₂-not-prop : is-prop (mediates₂ tt (base , base)) → ⊥
mediates₂-not-prop W =
  loop-nontrivial (sym (Path.unitl loop) ∙ sym λ i → W m₀ m₁ i .fst)
```

## The equivalence tier

Both cuts are the multiplication, and every translation of the circle
is an equivalence, so the tier holds at every pair and is
contractible there.

```agda
eqv-all : (p : pair tt) → is-eqv-pair tt p
eqv-all p =
    ((λ _ → mult-r-equiv (p .fst)) , λ _ → mult-equiv (p .fst))
  , ((λ _ → mult-r-equiv (p .snd)) , λ _ → mult-equiv (p .snd))

eqv-contr : (p : pair tt) → is-contr (is-eqv-pair tt p)
eqv-contr p = prop-inhabited→is-contr (is-eqv-pair-is-prop tt p) (eqv-all p)
```

## The contraction

`sides` collects the right side of each clause. The first coordinate
reads the positive component alone, and the second reads both
components with the negative one in the outer slot. So `sides` is an
equivalence over an equivalence: the base map is one right
multiplication and each fiber map is two.

Each clause is a path against a coordinate of `sides`, and the two
together are one path in the product. The type of mediating pairs is
therefore a fiber of `sides`, hence contractible, and the tier factor
is contractible at every pair, so the framed pairs contract with it.

```agda
shear : Circle × Circle → Circle × Circle
shear q = mult (q .fst) base
        , mult (mult (q .snd) (mult (q .fst) (mult (q .fst) (q .fst)))) base

shear-is-equiv : is-equiv shear
shear-is-equiv =
  Σ-dep-map-is-equiv {P = λ _ → Circle} {Q = λ _ → Circle}
    (mult-r-equiv base)
    (λ b → comp-equiv (mult-r-equiv (mult b (mult b b))) (mult-r-equiv base))

swap : pair tt ≃ (Circle × Circle)
swap = iso→equiv (λ p → p .snd , p .fst) (λ q → q .snd , q .fst)
                 (λ _ → refl) (λ _ → refl)

×-equiv : ∀ {u v w z} {A : Type u} {B : Type v} {C : Type w} {D : Type z}
        → A ≃ C → B ≃ D → (A × B) ≃ (C × D)
×-equiv e f = (λ (x , y) → e .fst x , f .fst y) , ×-is-equiv (e .snd) (f .snd)

sides : pair tt → Circle × Circle
sides p = shear (p .snd , p .fst)

sides-is-equiv : is-equiv sides
sides-is-equiv = comp-equiv (swap .snd) shear-is-equiv

clause-pair : (p : pair tt) → mediates₂ tt p ≃ (sides p ≡ (base , base))
clause-pair p = ×-equiv path-sym-equiv path-sym-equiv ∙e esym ×-path-equiv

mediation₂-contr : is-contr (Σ p ∶ pair tt , mediates₂ tt p)
mediation₂-contr =
  is-contr-equiv (Σ-equiv-snd clause-pair)
                 (sides-is-equiv .eqv-fibers (base , base))

framed-contr : (x : ⊤) → is-contr (framed x)
framed-contr _ =
  is-contr-equiv (Σ-equiv-snd λ p → Σ-contr-fst (eqv-contr p))
                 mediation₂-contr

has-framing-is-prop : is-prop (∀ x → framed x)
has-framing-is-prop = framed-is-prop framed-contr
```

## Recognition at a fixed pair

`sides` is an equivalence, so its action on paths is one too. It
fixes the axiom pair, so the identifications of a pair with the axiom
pair match the paths between the two sides. Both types carry two
windings at the axiom pair, one winding per component.

```agda
recognition₂ : (p : pair tt) → mediates₂ tt p ≃ (p ≡ (base , base))
recognition₂ p =
    clause-pair p
  ∙e esym ( ap sides
          , is-embedding→ap-equiv (is-equiv→is-embedding sides-is-equiv) )

pair-path-not-prop
  : is-prop (_≡_ {A = pair tt} (base , base) (base , base)) → ⊥
pair-path-not-prop W =
  loop-nontrivial (sym λ i → ap fst (W refl (λ j → loop j , loop j) i))
```

## The self-referential clauses

Both half-twists of the model are the axiom, so at the axiom pair the
substitution changes nothing: the two clause forms are one type
there, and the witnesses and the freedom carry across.

```agda
module self-form where

  open self circle.model (λ _ → base) (λ _ → base)
    circle.stable circle.C⁺ circle.C⁻
    using (selfclause₀; selfclause₁; selfmediates₂) public

  agree₀ : selfclause₀ tt (base , base) ≡ clause₀ tt (base , base)
  agree₀ = refl

  agree₁ : selfclause₁ tt (base , base) ≡ clause₁ tt (base , base)
  agree₁ = refl

  mediates-base : selfmediates₂ tt (base , base)
  mediates-base = refl , refl

  selfmediates₂-not-prop : is-prop (selfmediates₂ tt (base , base)) → ⊥
  selfmediates₂-not-prop = mediates₂-not-prop
```
