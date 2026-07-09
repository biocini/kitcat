Lane Biocini
July 2026

The irreducible coherence layer for the braided monoidal
structure. The associator is free and the braiding is free
(`Cat.Monoidal.Braid`), but the hexagon is not: it relates the
braid to the associator across two distinct contractible fibers,
and the identification of the two braid traversals of the triple
composite is a genuine axiom. This is the `hexagon-emb` field.

The object-level hexagon `⊗-hexagon` derives from `hexagon-emb`
by the same contractible-fiber projection that gives `⊗-pentagon`
in `Cat.Monoidal.Coherence`. Six vertices sit in a single fiber
over `tensor-E₃ y z x` that the base axioms make contractible;
the two traversals agree by `is-contr→is-set`, with the field
supplying the one move — `pt₁-L ≡ pt₁-R` — that contractibility
alone would leave a possibly nontrivial loop on the object.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Hexagon where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp)
open import Cat.Type
open import Cat.Monoidal
open import Cat.Monoidal.Braid
```

## The braided-coherent record

The single field `hexagon-emb` identifies the two pointwise braid
traversals of the triple tensor. Both sides start at
`tensor-emb x l (noy y (noy z r))` and end at
`tensor-emb y l (noy z (noy x r))`: the left side braids `x` past
the composite `y ⊗ z` in one step, the right side braids `x` past
`y` and then past `z` separately.

```agda
record braided-coherent {o h} {C : category o h} {M : monoidal C}
  (B : braided M) : Type (o ⊔ h) where
  open monoidal M
  open braided B
  open category C using (ob)

  field
    hexagon-emb
      : (x y z l r : ob)
      →   ( ap (tensor-emb x l) (sym (tensor-noy-composite y z r))
          ∙ tensor-braid x (y ⊗ z) l r
          ∙ tensor-emb-comp-pt y z l (noy x r) )
      ≡   ( tensor-braid x y l (noy z r)
          ∙ ap (tensor-emb y l) (tensor-braid x z I r) )

  braid-traversal-L
    : (x y z : ob)
    → tensor-E₃ x y z ≡ tensor-E₃ y z x
  braid-traversal-L x y z =
    tensor-emb-ext λ l r →
        ap (tensor-emb x l) (sym (tensor-noy-composite y z r))
      ∙ tensor-braid x (y ⊗ z) l r
      ∙ tensor-emb-comp-pt y z l (noy x r)

  braid-traversal-R
    : (x y z : ob)
    → tensor-E₃ x y z ≡ tensor-E₃ y z x
  braid-traversal-R x y z =
    tensor-emb-ext λ l r →
        tensor-braid x y l (noy z r)
      ∙ ap (tensor-emb y l) (tensor-braid x z I r)

  hexagon-emb-ext
    : (x y z : ob)
    → braid-traversal-L x y z ≡ braid-traversal-R x y z
  hexagon-emb-ext x y z =
    ap tensor-emb-ext (funext λ l → funext λ r → hexagon-emb x y z l r)
```

## The hexagon fiber

The two hexagon traversals both land in the single fiber over
`tensor-E₃ y z x`. Six vertices are placed there; the two
three-step paths agree by `is-contr→is-set`, with the field's
move `μ : pt₁-L ≡ pt₁-R` inserted so that its `ap fst` is `refl`.

```agda
module ⊗-Braided-Cat
  {o h} {C : category o h} {M : monoidal C}
  {B : braided M} (BC : braided-coherent B) where
  open monoidal M
  open braided B
  open braided-coherent BC
  open category C using (ob)

  private
    assoc-σ
      : (a b c : ob)
      → tensor-E₃-contr-ext a b c .center
      ≡ ( a ⊗ (b ⊗ c)
        , tensor-emb-composite a (b ⊗ c)
        ∙ tensor-emb-ext λ l r →
            ap (tensor-emb a l) (tensor-noy-composite b c r))
    assoc-σ a b c =
      is-contr→is-prop (tensor-E₃-contr-ext a b c) _ _

    pcom→∙
      : ∀ {u} {A : Type u} {a b c d : A}
        (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
      → pcom (sym p) q r ≡ p ∙ q ∙ r
    pcom→∙ p q r = pcom.unique
      (sym p) q r
      (p ∙ q ∙ r , cat.lcoh p q r)

  module hexagon-fibers (x y z : ob) where
    private
      C₃ = tensor-E₃-contr-ext y z x

      NB : (λ l r → tensor-emb (y ⊗ z) l (noy x r)) ≡ tensor-E₃ y z x
      NB = tensor-emb-ext λ l r → tensor-emb-comp-pt y z l (noy x r)

      NL : tensor-E₃ x y z ≡ tensor-E₃ y x z
      NL = tensor-emb-ext λ l r → tensor-braid x y l (noy z r)

      NR : tensor-E₃ y x z ≡ tensor-E₃ y z x
      NR = tensor-emb-ext λ l r → ap (tensor-emb y l) (tensor-braid x z I r)

      pt₁-L : fiber tensor-emb (tensor-E₃ y z x)
      pt₁-L = (x ⊗ y) ⊗ z
           , tensor-emb-nest-ext x y z ∙ braid-traversal-L x y z

      pt₁-R : fiber tensor-emb (tensor-E₃ y z x)
      pt₁-R = (x ⊗ y) ⊗ z
           , tensor-emb-nest-ext x y z ∙ braid-traversal-R x y z

      pt₂ : fiber tensor-emb (tensor-E₃ y z x)
      pt₂ = x ⊗ (y ⊗ z)
          , (tensor-emb-composite x (y ⊗ z) ∙ tensor-braid-ext x (y ⊗ z))
          ∙ NB

      pt₃ : fiber tensor-emb (tensor-E₃ y z x)
      pt₃ = (y ⊗ z) ⊗ x
          , tensor-emb-composite (y ⊗ z) x ∙ NB

      pt₄ : fiber tensor-emb (tensor-E₃ y z x)
      pt₄ = y ⊗ (z ⊗ x)
          , tensor-emb-composite y (z ⊗ x)
          ∙ tensor-emb-ext λ l r →
              ap (tensor-emb y l) (tensor-noy-composite z x r)

      pt₅ : fiber tensor-emb (tensor-E₃ y z x)
      pt₅ = (y ⊗ x) ⊗ z
          , tensor-emb-nest-ext y x z ∙ NR

      pt₆ : fiber tensor-emb (tensor-E₃ y z x)
      pt₆ = y ⊗ (x ⊗ z)
          , ( tensor-emb-composite y (x ⊗ z)
            ∙ tensor-emb-ext λ l r →
                ap (tensor-emb y l) (tensor-noy-composite x z r) )
          ∙ NR

    σ₁₂ : pt₁-L ≡ pt₂
    σ₁₂ = is-contr→is-prop C₃ pt₁-L pt₂

    σ₂₃ : pt₂ ≡ pt₃
    σ₂₃ = is-contr→is-prop C₃ pt₂ pt₃

    σ₃₄ : pt₃ ≡ pt₄
    σ₃₄ = is-contr→is-prop C₃ pt₃ pt₄

    σ₁₅ : pt₁-R ≡ pt₅
    σ₁₅ = is-contr→is-prop C₃ pt₁-R pt₅

    σ₅₆ : pt₅ ≡ pt₆
    σ₅₆ = is-contr→is-prop C₃ pt₅ pt₆

    σ₆₄ : pt₆ ≡ pt₄
    σ₆₄ = is-contr→is-prop C₃ pt₆ pt₄

    α₁₂ : (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    α₁₂ = ap fst σ₁₂

    α₂₃ : x ⊗ (y ⊗ z) ≡ (y ⊗ z) ⊗ x
    α₂₃ = ap fst σ₂₃

    α₃₄ : (y ⊗ z) ⊗ x ≡ y ⊗ (z ⊗ x)
    α₃₄ = ap fst σ₃₄

    α₁₅ : (x ⊗ y) ⊗ z ≡ (y ⊗ x) ⊗ z
    α₁₅ = ap fst σ₁₅

    α₅₆ : (y ⊗ x) ⊗ z ≡ y ⊗ (x ⊗ z)
    α₅₆ = ap fst σ₅₆

    α₆₄ : y ⊗ (x ⊗ z) ≡ y ⊗ (z ⊗ x)
    α₆₄ = ap fst σ₆₄

    μ : pt₁-L ≡ pt₁-R
    μ i = (x ⊗ y) ⊗ z
        , tensor-emb-nest-ext x y z ∙ hexagon-emb-ext x y z i

    identity
      : pcom (sym σ₁₂) σ₂₃ σ₃₄
      ≡ μ ∙ pcom (sym σ₁₅) σ₅₆ σ₆₄
    identity = is-contr→is-set C₃ pt₁-L pt₄
      (pcom (sym σ₁₂) σ₂₃ σ₃₄)
      (μ ∙ pcom (sym σ₁₅) σ₅₆ σ₆₄)

    hom-identity
      : pcom (sym α₁₂) α₂₃ α₃₄
      ≡ pcom (sym α₁₅) α₅₆ α₆₄
    hom-identity =
      pcom (pcom.ap (λ _ → fst) (sym σ₁₂) σ₂₃ σ₃₄)
        (ap (ap fst) identity)
        r-step
      where
        r-step
          : ap fst (μ ∙ pcom (sym σ₁₅) σ₅₆ σ₆₄)
          ≡ pcom (sym α₁₅) α₅₆ α₆₄
        r-step =
          ap-comp fst μ (pcom (sym σ₁₅) σ₅₆ σ₆₄)
          ∙ Path.unitl (ap fst (pcom (sym σ₁₅) σ₅₆ σ₆₄))
          ∙ pcom.ap (λ _ → fst) (sym σ₁₅) σ₅₆ σ₆₄

    face₃₄ : α₃₄ ≡ ⊗-assoc y z x
    face₃₄ = contr-face C₃ σ₃₄ w-refl (assoc-σ y z x) refl
      where
        w-refl
          : (tensor-emb-composite (y ⊗ z) x ∙ NB)
          ≡ tensor-emb-nest-ext y z x
        w-refl = refl

    face₂₃ : α₂₃ ≡ ⊗-braid x (y ⊗ z)
    face₂₃ = contr-face C₃ σ₂₃ refl core refl
      where
        σ-B
          : ( x ⊗ (y ⊗ z)
            , tensor-emb-composite x (y ⊗ z) ∙ tensor-braid-ext x (y ⊗ z))
          ≡ tensor-compose-contr (y ⊗ z) x .center
        σ-B = is-contr→is-prop (tensor-compose-contr (y ⊗ z) x) _ _

        core
          : ( x ⊗ (y ⊗ z)
            , (tensor-emb-composite x (y ⊗ z) ∙ tensor-braid-ext x (y ⊗ z))
              ∙ NB )
          ≡ ((y ⊗ z) ⊗ x , tensor-emb-composite (y ⊗ z) x ∙ NB)
        core i = σ-B i .fst , σ-B i .snd ∙ NB

    face₁₅ : α₁₅ ≡ ap (_⊗ z) (⊗-braid x y)
    face₁₅ = contr-face C₃ σ₁₅ w-recon core refl
      where
        σ-B'
          : ( x ⊗ y
            , tensor-emb-composite x y ∙ tensor-braid-ext x y)
          ≡ tensor-compose-contr y x .center
        σ-B' = is-contr→is-prop (tensor-compose-contr y x) _ _

        core
          : ( (x ⊗ y) ⊗ z
            , ( tensor-emb-composite (x ⊗ y) z
              ∙ (λ j l r → σ-B' i0 .snd j l (noy z r)) )
              ∙ NR )
          ≡ ( (y ⊗ x) ⊗ z
            , tensor-emb-nest-ext y x z ∙ NR )
        core i =
          (σ-B' i .fst) ⊗ z
          , ( tensor-emb-composite (σ-B' i .fst) z
            ∙ (λ j l r → σ-B' i .snd j l (noy z r)) )
          ∙ NR

        w-pt
          : (l r : ob)
          → ( (tensor-emb-comp-pt (x ⊗ y) z l r
              ∙ tensor-emb-comp-pt x y l (noy z r))
            ∙ ( tensor-braid x y l (noy z r)
              ∙ ap (tensor-emb y l) (tensor-braid x z I r) ) )
          ≡ ( ( tensor-emb-comp-pt (x ⊗ y) z l r
              ∙ ( tensor-emb-comp-pt x y l (noy z r)
                ∙ tensor-braid x y l (noy z r) ) )
            ∙ ap (tensor-emb y l) (tensor-braid x z I r) )
        w-pt l r =
          Path.assoc (a ∙ b) c d ∙ ap (_∙ d) (sym (Path.assoc a b c))
          where
            a = tensor-emb-comp-pt (x ⊗ y) z l r
            b = tensor-emb-comp-pt x y l (noy z r)
            c = tensor-braid x y l (noy z r)
            d = ap (tensor-emb y l) (tensor-braid x z I r)

        w-recon
          : tensor-emb-nest-ext x y z ∙ braid-traversal-R x y z
          ≡ ( tensor-emb-composite (x ⊗ y) z
            ∙ (λ j l r → σ-B' i0 .snd j l (noy z r)) )
            ∙ NR
        w-recon = ap tensor-emb-ext (funext λ l → funext λ r → w-pt l r)

    face₅₆ : α₅₆ ≡ ⊗-assoc y x z
    face₅₆ = contr-face C₃ σ₅₆ refl core refl
      where
        core
          : ((y ⊗ x) ⊗ z , tensor-emb-nest-ext y x z ∙ NR)
          ≡ ( y ⊗ (x ⊗ z)
            , ( tensor-emb-composite y (x ⊗ z)
              ∙ tensor-emb-ext λ l r →
                  ap (tensor-emb y l) (tensor-noy-composite x z r) )
              ∙ NR )
        core i = assoc-σ y x z i .fst , assoc-σ y x z i .snd ∙ NR

    face₁₂ : α₁₂ ≡ ⊗-assoc x y z
    face₁₂ = contr-face C₃ σ₁₂ refl core v-recon
      where
        core
          : ((x ⊗ y) ⊗ z , tensor-emb-nest-ext x y z ∙ braid-traversal-L x y z)
          ≡ ( x ⊗ (y ⊗ z)
            , ( tensor-emb-composite x (y ⊗ z)
              ∙ tensor-emb-ext λ l r →
                  ap (tensor-emb x l) (tensor-noy-composite y z r) )
              ∙ braid-traversal-L x y z )
        core i =
          assoc-σ x y z i .fst
          , assoc-σ x y z i .snd ∙ braid-traversal-L x y z

        v-pt
          : (l r : ob)
          → ( ( tensor-emb-comp-pt x (y ⊗ z) l r
              ∙ ap (tensor-emb x l) (tensor-noy-composite y z r) )
            ∙ ( ap (tensor-emb x l) (sym (tensor-noy-composite y z r))
              ∙ ( tensor-braid x (y ⊗ z) l r
                ∙ tensor-emb-comp-pt y z l (noy x r) ) ) )
          ≡ ( ( tensor-emb-comp-pt x (y ⊗ z) l r
              ∙ tensor-braid x (y ⊗ z) l r )
            ∙ tensor-emb-comp-pt y z l (noy x r) )
        v-pt l r =
            sym (Path.assoc p q (s ∙ (t ∙ u)))
          ∙ ap (p ∙_)
              ( Path.assoc q s (t ∙ u)
              ∙ ap (_∙ (t ∙ u)) (Path.invr q)
              ∙ Path.unitl (t ∙ u) )
          ∙ Path.assoc p t u
          where
            p = tensor-emb-comp-pt x (y ⊗ z) l r
            q = ap (tensor-emb x l) (tensor-noy-composite y z r)
            s = ap (tensor-emb x l) (sym (tensor-noy-composite y z r))
            t = tensor-braid x (y ⊗ z) l r
            u = tensor-emb-comp-pt y z l (noy x r)

        v-recon
          : ( tensor-emb-composite x (y ⊗ z)
            ∙ tensor-emb-ext (λ l r →
                ap (tensor-emb x l) (tensor-noy-composite y z r)) )
            ∙ braid-traversal-L x y z
          ≡ (tensor-emb-composite x (y ⊗ z) ∙ tensor-braid-ext x (y ⊗ z))
            ∙ NB
        v-recon = ap tensor-emb-ext (funext λ l → funext λ r → v-pt l r)

    face₆₄ : α₆₄ ≡ ap (y ⊗_) (⊗-braid x z)
    face₆₄ = contr-face C₃ σ₆₄ w-recon core refl
      where
        σ-B''
          : ( x ⊗ z
            , tensor-emb-composite x z ∙ tensor-braid-ext x z)
          ≡ tensor-compose-contr z x .center
        σ-B'' = is-contr→is-prop (tensor-compose-contr z x) _ _

        core
          : ( y ⊗ (x ⊗ z)
            , tensor-emb-composite y (x ⊗ z)
              ∙ (λ j l r → tensor-emb y l (σ-B'' i0 .snd j I r)) )
          ≡ ( y ⊗ (z ⊗ x)
            , tensor-emb-composite y (z ⊗ x)
              ∙ tensor-emb-ext λ l r →
                  ap (tensor-emb y l) (tensor-noy-composite z x r) )
        core i =
          y ⊗ (σ-B'' i .fst)
          , tensor-emb-composite y (σ-B'' i .fst)
          ∙ (λ j l r → tensor-emb y l (σ-B'' i .snd j I r))

        w-pt
          : (l r : ob)
          → ( ( tensor-emb-comp-pt y (x ⊗ z) l r
              ∙ ap (tensor-emb y l) (tensor-noy-composite x z r) )
            ∙ ap (tensor-emb y l) (tensor-braid x z I r) )
          ≡ ( tensor-emb-comp-pt y (x ⊗ z) l r
            ∙ ap (tensor-emb y l)
                (tensor-noy-composite x z r ∙ tensor-braid x z I r) )
        w-pt l r =
            sym (Path.assoc p m n)
          ∙ ap (p ∙_) (sym (ap-comp f mm nn))
          where
            f = tensor-emb y l
            p = tensor-emb-comp-pt y (x ⊗ z) l r
            mm = tensor-noy-composite x z r
            nn = tensor-braid x z I r
            m = ap f mm
            n = ap f nn

        w-recon
          : ( tensor-emb-composite y (x ⊗ z)
            ∙ tensor-emb-ext (λ l r →
                ap (tensor-emb y l) (tensor-noy-composite x z r)) )
            ∙ NR
          ≡ tensor-emb-composite y (x ⊗ z)
            ∙ (λ j l r → tensor-emb y l (σ-B'' i0 .snd j I r))
        w-recon = ap tensor-emb-ext (funext λ l → funext λ r → w-pt l r)
```

## The object hexagon

The two boundary paths of the hexagon assemble by translating
each `α_ij` to its named associator or braid via the faces,
splicing through `hom-identity`, and converting the ternary
`pcom` composites to `_∙_` chains with `pcom→∙`.

```agda
  ⊗-hexagon
    : (x y z : ob)
    → ⊗-assoc x y z ∙ ⊗-braid x (y ⊗ z) ∙ ⊗-assoc y z x
    ≡ ap (_⊗ z) (⊗-braid x y)
      ∙ ⊗-assoc y x z
      ∙ ap (y ⊗_) (⊗-braid x z)
  ⊗-hexagon x y z =
      sym (pcom→∙ (⊗-assoc x y z) (⊗-braid x (y ⊗ z)) (⊗-assoc y z x))
    ∙ (λ i → pcom (sym (face₁₂ (~ i))) (face₂₃ (~ i)) (face₃₄ (~ i)))
    ∙ hom-identity
    ∙ (λ i → pcom (sym (face₁₅ i)) (face₅₆ i) (face₆₄ i))
    ∙ pcom→∙ (ap (_⊗ z) (⊗-braid x y)) (⊗-assoc y x z)
        (ap (y ⊗_) (⊗-braid x z))
    where open hexagon-fibers x y z
```

## Deferred

Only the first hexagon is discharged here. `hexagon-emb` and
`⊗-hexagon` cover H1: the braiding of `x` past the composite
`y ⊗ z`, `⊗-braid x (y ⊗ z)`. The second hexagon H2 — the
braiding of the composite `x ⊗ y` past `z`, `⊗-braid (x ⊗ y) z`
— is neither a field nor a theorem yet.

Whether H2 derives from H1 by symmetry (the object-path
formulation `⊗-braid-inv = sym ⊗-braid`) or requires a second
field `hexagon-emb-2` is open. Both hexagons together give the
full braided coherence; until H2 is settled, `braided-coherent`
records only H1.

