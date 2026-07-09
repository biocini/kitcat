An indiscrete-monoidal builder. Given a category whose hom
types are all contractible, any object-tier tensor structure
extends uniquely to a full `monoidal` structure: every
morphism-tier obligation is a statement about a contractible
hom type, so it is discharged from `hom-contr` alone.

The object-tier data — the ternary tensor `te`, its unit `tu`,
the composition fiber `tcc`, the interchange law `tint`, and
the yon-evaluation `tye` — are passed straight through to the
corresponding `monoidal` fields. The six morphism-tier fields
(`htensor-*`) are filled uniformly: `htensor-emb` is the unique
inhabitant of its hom type, the coherence laws are paths and
`PathP`s in contractible hom families (hence themselves
contractible, independent of which object-level path indexes
them), and `htensor-unit` is a pair of maps between
contractible hom types.

This is the carrier-agnostic scaffold for the `absorb-coh`
independence countermodel: the choice of `te`/`tu`/etc. is left
entirely open, so a later phase can plug in a specific object
tier without touching any morphism-level reasoning.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Indiscrete where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Data.Nat.Type using (Z)
open import Core.Kan using (is-contr→is-prop)
open import Core.Equiv.Base using (is-equiv)
open import Core.Equiv.Properties using (contr→contr→is-equiv)
open import Core.HLevel.Base using (PathP-is-contr; Σ-is-hlevel)

open import Cat.Type
open import Cat.Monoidal
```

## The builder

```agda
module _ {o h} {C : category o h} where
  private module C = Virtual C

  indiscrete-monoidal
    : (hom-contr : ∀ {a b} → is-contr (C.hom a b))
    → (te : C.ob → C.ob → C.ob → C.ob)
    → (tu : Σ i ∶ C.ob
          , is-equiv (λ (r : C.ob) → te i i r)
          × is-equiv (λ (l : C.ob) → te i l i))
    → (tcc : (x y : C.ob)
           → is-contr (fiber te (λ l r → te x l (te y (tu .fst) r))))
    → (tint : (x y l r : C.ob)
            → te x l (te y (tu .fst) r) ≡ te y (te x l (tu .fst)) r)
    → (tye : (x : C.ob) → te x (tu .fst) (tu .fst) ≡ x)
    → monoidal C
  indiscrete-monoidal hom-contr te tu tcc tint tye = mono
    where
    mono : monoidal C
    mono .monoidal.tensor-emb = te
    mono .monoidal.tensor-unit = tu
    mono .monoidal.tensor-compose-contr = tcc
    mono .monoidal.tensor-interchange = tint
    mono .monoidal.tensor-yon-eval = tye
    mono .monoidal.htensor-emb φ ψ χ = hom-contr .center
    mono .monoidal.htensor-unit =
      (λ {m} {m'} → contr→contr→is-equiv hom-contr hom-contr _)
      , (λ {l} {l'} → contr→contr→is-equiv hom-contr hom-contr _)
    mono .monoidal.htensor-compose-contr φ ψ =
      Σ-is-hlevel Z hom-contr λ σ →
        Contr
          (λ α β → PathP-is-contr hom-contr _ _ .center)
          (λ p j α β →
            PathP-is-contr hom-contr _ _ .paths (p α β) j)
    mono .monoidal.htensor-interchange φ ψ α β =
      PathP-is-contr hom-contr _ _ .center
    mono .monoidal.htensor-yon-eval φ =
      PathP-is-contr hom-contr _ _ .center
    mono .monoidal.htensor-bifunctor φ₁ φ₂ α₁ α₂ β₁ β₂ =
      is-contr→is-prop hom-contr _ _
```
