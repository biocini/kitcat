The circle contrapositive for the unitor-agreement boundary: the
winding of the derived unitor discrepancy in `Bb.CatsWithExplicitInterchange.Gist.CircleTensor`.
The record's unitors are relative to the choice of interchange
field, and `unitr-agreement` states their coincidence; in the
circle instance the two fields differ by a global rotation, so the
discrepancy of the two right unitors at `base` is a concrete loop
whose winding the instance computes — the unitor σ-lines unfold
and the whole fiber apparatus normalizes to an integer.

**The discrepancy winds −1**: the right-unitor chain spends the
deformation exactly once, the ι⁺-side unitor carrying the positive
rotation relative to the planar side. Both boundary statements
therefore fail together in this instance — `unitr-agreement` is
refuted by the winding, and `ω-vanish-l` was already refuted by
`routes-differ` — so the circle is consistent with the converse of
the flank-boundary implication (agreement forcing vanishing) and
provides no counterexample to it. A refutation of the converse
would need an instance with agreeing unitors over genuinely
distinct fields; here the disagreement is exactly the surviving
rotation.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.CatsWithExplicitInterchange.Gist.CircleUnitorTwist where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Kan
open import Core.Data.Empty using (⊥)
open import Core.Data.Nat.Type using (Z; S)
open import Core.Data.Int using (Int; pos; negsuc)
open import Core.Transport.Base using (transport-refl)
open import Core.Transport.J using (subst)

open import Bb.CatsWithExplicitInterchange.Monoidal
open import Bb.CatsWithExplicitInterchange.Monoidal.Properties using (ω-vanish-l)

open import HData.Circle
open Circle

open import Bb.CatsWithExplicitInterchange.Gist.CircleTensor using (Circle-tensor; routes-differ)

private
  module M = monoidal-axioms₀ Circle-tensor
  module T = theory₀ Circle-tensor
  module U⁺ = T.unitors M.ι⁺-pt
  module U⁻ = T.unitors M.ι⁻-pt
```

## The discrepancy loop and its winding

```agda
θ-unitr : base ≡ base
θ-unitr = sym (U⁺.⊗₀-unitr base) ∙ U⁻.⊗₀-unitr base

opaque
  unfolding U⁺.unitr-σ●₀

  θ-winding : winding θ-unitr ≡ negsuc Z
  θ-winding = refl
```

## The agreement type is refuted

Agreement at `base` would collapse the discrepancy to `refl`,
whose winding is zero.

```agda
private
  is-negsuc : Int → Type
  is-negsuc (pos n)    = ⊥
  is-negsuc (negsuc n) = ⊤

unitr-disagreement : T.unitr-agreement → ⊥
unitr-disagreement e = subst is-negsuc contra tt
  where
  θ-refl : θ-unitr ≡ refl
  θ-refl =
      ap (λ p → sym p ∙ U⁻.⊗₀-unitr base) (e base)
    ∙ Path.invl (U⁻.⊗₀-unitr base)

  contra : negsuc Z ≡ pos Z
  contra = sym θ-winding ∙ ap winding θ-refl ∙ transport-refl (pos Z)
```

## The flank does not vanish

`ω-vanish-l` at `base` would identify the two fields at the
detection point, which `routes-differ` excludes — the two
refutations together are the instance-level contrapositive of
`flank-vanish→unitr-agreement`.

```agda
flank-not-vanish : ω-vanish-l Circle-tensor → ⊥
flank-not-vanish v = routes-differ fields-agree
  where
  P⁺ = M.ι⁺-pt base base
  P⁻ = M.ι⁻-pt base base

  fields-agree : P⁺ ≡ P⁻
  fields-agree =
      sym (Path.unitr P⁺)
    ∙ ap (P⁺ ∙_) (sym (Path.invl P⁻))
    ∙ Path.assoc P⁺ (sym P⁻) P⁻
    ∙ ap (_∙ P⁻) (v base)
    ∙ Path.unitl P⁻
```
