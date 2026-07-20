Lane Biocini
July 2026

The displayed pentagon: `Cat.Coherence`'s `pentagon` tree, displaced
leaf-for-leaf into a `categoryᴰ`. The base `∙`-tree was named so a
displaced pentagon could glue over each leaf separately, and every
leaf displaces by construction: the `A`-whiskers are `assoc●ᴰ-nrm`
slides over their base mates, the `ap-comp` shuffles are
`comp-pathp₁-ap` squares — the hom component of a `●ᴰ-∙` glue *is*
the `comp-pathp₁` at the reindexed witness family, so each shuffle
square's two ends are two readings of the same composite — and the
core leaf is `pentagon●ᴰ`, the fiber pentagon's displaced image.
`comp-pathp₁` at the family of pentagon fillers glues the displaced
leaves along exactly the base tree, so every interface between
consecutive leaves is definitional.

This is `Cat.Monoidal.Coherence`'s `pentagon₁` with the two-sided
`⊗₁-wit` calculus replaced by the one-sided displayed witness
calculus of `Cat.Displayed.Base`: `comp-pathp₂` becomes
`comp-pathp₁`, `⊗₁-wit-∙` becomes `●ᴰ-∙`, and each shuffle costs
one coherence cube instead of two.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Displayed.Coherence where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp; comp-pathp₁-ap)
open import Core.Transport.Properties using (is-prop→SquareP)
open import Core.Transport.J using (subst)

open import Cat.Type
open import Cat.Base
open import Cat.Coherence
open import Cat.Displayed
open import Cat.Displayed.Base

module _ {o h o' h'} {C : category o h} (D : categoryᴰ C o' h') where
  open category C
  open theory C
  open categoryᴰ D
  open theoryᴰ D
```

## The displaced fiber pentagon

The five bracketings of a fourfold `●ᴰ` displace the base
witnesses `p₁`–`p₅`, the five edges displace the `σ`s —
`assoc-σ●ᴰ` lines, `●ᴰ`-whiskered on the same side as at the
base — and the square between the glued edge composites fills by
`is-prop→SquareP`: the displayed witness spaces are contractible
pointwise over the whole of `fiber-pentagon`, one transported
`repr-contrᴰ` per point.

The hom shadow projects through `fst`. Because the edges are
glued by `●ᴰ-∙`, their hom components are the `comp-pathp₁`
composites of the whiskered `assoc●ᴰ` lines by construction, so
`pentagon●ᴰ` is a genuine identification of displayed associator
composites over the fiber square's shadow, the displaced image of
`pentagon●`'s core.

```agda
  module pentagon●ᴰ {x y z w v} {x' y' z' w' v'}
    {F : composite x y} {G : composite y z}
    {H : composite z w} {K : composite w v}
    {U : is-representable F} {V : is-representable G}
    {W : is-representable H} {X : is-representable K}
    {F' : composite[ F ] x' y'} {G' : composite[ G ] y' z'}
    {H' : composite[ H ] z' w'} {K' : composite[ K ] w' v'}
    (U' : is-representable[ U ] F') (V' : is-representable[ V ] G')
    (W' : is-representable[ W ] H') (X' : is-representable[ X ] K')
    where

    private module P = pentagon● C U V W X

    -- the displayed homs the witnesses lift
    φ = U' .fst ; ψ = V' .fst ; χ = W' .fst ; ω = X' .fst

    T' : composite[ P.T ] x' v'
    T' = F' ▿ᴰ G' ▿ᴰ H' ▿ᴰ K'

    p̂₁ : is-representable[ P.p₁ ] T' ; p̂₁ = ((U' ●ᴰ V') ●ᴰ W') ●ᴰ X'
    p̂₂ : is-representable[ P.p₂ ] T' ; p̂₂ = (U' ●ᴰ (V' ●ᴰ W')) ●ᴰ X'
    p̂₃ : is-representable[ P.p₃ ] T' ; p̂₃ = U' ●ᴰ ((V' ●ᴰ W') ●ᴰ X')
    p̂₄ : is-representable[ P.p₄ ] T' ; p̂₄ = (U' ●ᴰ V') ●ᴰ (W' ●ᴰ X')
    p̂₅ : is-representable[ P.p₅ ] T' ; p̂₅ = U' ●ᴰ (V' ●ᴰ (W' ●ᴰ X'))

    σ̂₂₁ : PathP (λ i → is-representable[ P.σ₂₁ i ] T') p̂₂ p̂₁
    σ̂₂₁ i = assoc-σ●ᴰ U' V' W' i ●ᴰ X'

    σ̂₃₂ : PathP (λ i → is-representable[ P.σ₃₂ i ] T') p̂₃ p̂₂
    σ̂₃₂ = assoc-σ●ᴰ U' (V' ●ᴰ W') X'

    σ̂₅₃ : PathP (λ i → is-representable[ P.σ₅₃ i ] T') p̂₅ p̂₃
    σ̂₅₃ i = U' ●ᴰ assoc-σ●ᴰ V' W' X' i

    σ̂₄₁ : PathP (λ i → is-representable[ P.σ₄₁ i ] T') p̂₄ p̂₁
    σ̂₄₁ = assoc-σ●ᴰ (U' ●ᴰ V') W' X'

    σ̂₅₄ : PathP (λ i → is-representable[ P.σ₅₄ i ] T') p̂₅ p̂₄
    σ̂₅₄ = assoc-σ●ᴰ U' V' (W' ●ᴰ X')

    top̂ : PathP (λ i → is-representable[ (P.σ₅₃ ∙ P.σ₃₂ ∙ P.σ₂₁) i ] T')
                p̂₅ p̂₁
    top̂ = ●ᴰ-∙ P.σ₅₃ (P.σ₃₂ ∙ P.σ₂₁)
            σ̂₅₃ (●ᴰ-∙ P.σ₃₂ P.σ₂₁ σ̂₃₂ σ̂₂₁)

    bot̂ : PathP (λ i → is-representable[ (P.σ₅₄ ∙ P.σ₄₁) i ] T') p̂₅ p̂₁
    bot̂ = ●ᴰ-∙ P.σ₅₄ P.σ₄₁ σ̂₅₄ σ̂₄₁

    wit-prop
      : (j i : I)
      → is-prop (is-representable[ P.fiber-pentagon j i ] T')
    wit-prop j i =
      is-contr→is-prop
        (subst is-contr
          (λ k → is-representable[ P.fiber-pentagon (j ∧ k) (i ∧ k) ] T')
          (repr-contrᴰ p̂₅))

    fiber-pentagonᴰ
      : PathP (λ j → PathP (λ i → is-representable[ P.fiber-pentagon j i ] T')
                     p̂₅ p̂₁)
              top̂ bot̂
    fiber-pentagonᴰ = is-prop→SquareP wit-prop top̂ refl bot̂ refl

    pentagon●ᴰ
      : PathP (λ j → PathP (λ i → hom[ P.fiber-pentagon j i .fst ] x' v')
                     (φ ⨾ᴰ (ψ ⨾ᴰ (χ ⨾ᴰ ω)))
                     (((φ ⨾ᴰ ψ) ⨾ᴰ χ) ⨾ᴰ ω))
              (λ i → top̂ i .fst) (λ i → bot̂ i .fst)
    pentagon●ᴰ j i = fiber-pentagonᴰ j i .fst
```

## The displaced nrm-slide

A displayed witness slid back along its own characterization: at
`m = i0` the slide is the witness itself (path eta), at `m = i1`
the normal form `nrm[_]` at its hom — both definitional, exactly
as at the base, so `assoc●ᴰ-nrm` is a strict-endpoint square over
`assoc●-nrm` connecting the compound-witness associator line to
`assocᴰ` at the represented homs. The connection collapses any
compound characterization to `refl` at `m = i1` regardless of
shape, on both levels at once.

```agda
  nrm-slideᴰ
    : ∀ {x y} {A : composite x y} {x' y'} {U : is-representable A}
        {A' : composite[ A ] x' y'}
      (U' : is-representable[ U ] A') (m : I)
    → is-representable[ nrm-slide C U m ] (U' .snd (~ m))
  nrm-slideᴰ U' m = U' .fst , λ k → U' .snd (k ∧ ~ m)

  assoc●ᴰ-nrm
    : ∀ {w x y z} {A : composite w x} {B : composite x y}
        {E : composite y z} {w' x' y' z'}
        {U : is-representable A} {V : is-representable B}
        {W : is-representable E}
        {A' : composite[ A ] w' x'} {B' : composite[ B ] x' y'}
        {E' : composite[ E ] y' z'}
      (U' : is-representable[ U ] A') (V' : is-representable[ V ] B')
      (W' : is-representable[ W ] E')
    → PathP (λ m → PathP (λ i → hom[ assoc●-nrm C U V W m i ] w' z')
                   (U' .fst ⨾ᴰ (V' .fst ⨾ᴰ W' .fst))
                   ((U' .fst ⨾ᴰ V' .fst) ⨾ᴰ W' .fst))
            (assoc●ᴰ U' V' W')
            (assocᴰ (U' .fst) (V' .fst) (W' .fst))
  assoc●ᴰ-nrm U' V' W' m =
    assoc●ᴰ (nrm-slideᴰ U' m) (nrm-slideᴰ V' m) (nrm-slideᴰ W' m)
```

## The canonical displayed pentagon

The pentagon over `Cat.Coherence`'s `pentagon` itself: a square
of displayed hom-lines whose edges are the `comp-pathp₁`
composites of the whiskered `assocᴰ` lines. One displaced leaf
per base leaf: the whiskers ride the `assoc●ᴰ-nrm` slides, the
shuffles are `comp-pathp₁-ap` squares — reversed where the base
leaf is a `sym` — and the core is `pentagon●ᴰ` verbatim. Every
stated endpoint is the definitional value of its neighbour's
boundary.

```agda
  module pentagonᴰ {x y z w v} {f : hom x y} {g : hom y z}
    {h : hom z w} {k : hom w v} {x' y' z' w' v'}
    (φ : hom[ f ] x' y') (ψ : hom[ g ] y' z')
    (χ : hom[ h ] z' w') (ω : hom[ k ] w' v')
    where

    private
      module Q  = pentagon C f g h k
      module Pᴰ = pentagon●ᴰ nrm[ φ ] nrm[ ψ ] nrm[ χ ] nrm[ ω ]

      Hom : hom x v → Type h'
      Hom t = hom[ t ] x' v'

      Fam : f ⨾ g ⨾ h ⨾ k ≡ ((f ⨾ g) ⨾ h) ⨾ k → Type h'
      Fam p = PathP (λ i → Hom (p i))
                    (φ ⨾ᴰ ψ ⨾ᴰ χ ⨾ᴰ ω) (((φ ⨾ᴰ ψ) ⨾ᴰ χ) ⨾ᴰ ω)

      -- the displaced A-whiskers: assoc●ᴰ-nrm at the same
      -- compound witnesses A₁–A₃ straighten
      Â₁ = assoc●ᴰ-nrm (nrm[ φ ] ●ᴰ nrm[ ψ ]) nrm[ χ ] nrm[ ω ]
      Â₂ = assoc●ᴰ-nrm nrm[ φ ] nrm[ ψ ] (nrm[ χ ] ●ᴰ nrm[ ω ])
      Â₃ = assoc●ᴰ-nrm nrm[ φ ] (nrm[ ψ ] ●ᴰ nrm[ χ ]) nrm[ ω ]

      -- the inner witness glue of top̂, shared by both shuffle legs
      ẑ = ●ᴰ-∙ Q.σ₃₂ Q.σ₂₁ Pᴰ.σ̂₃₂ Pᴰ.σ̂₂₁
```

The chain of edges: the stated top edge, the σ-projection
composites in their three degrees of splitting, the hom shadows
of `top̂`/`bot̂`, the half-straightened composites, and the stated
bottom edge.

```agda
    topᴰ : Fam (ap (f ⨾_) (assoc g h k)
                ∙ assoc f (g ⨾ h) k ∙ ap (_⨾ k) (assoc f g h))
    topᴰ =
      comp-pathp₁ Hom
        (ap (f ⨾_) (assoc g h k))
        (assoc f (g ⨾ h) k ∙ ap (_⨾ k) (assoc f g h))
        (λ i → φ ⨾ᴰ assocᴰ ψ χ ω i)
        (comp-pathp₁ Hom
          (assoc f (g ⨾ h) k) (ap (_⨾ k) (assoc f g h))
          (assocᴰ φ (ψ ⨾ᴰ χ) ω)
          (λ i → assocᴰ φ ψ χ i ⨾ᴰ ω))

    botᴰ : Fam (assoc f g (h ⨾ k) ∙ assoc (f ⨾ g) h k)
    botᴰ =
      comp-pathp₁ Hom
        (assoc f g (h ⨾ k)) (assoc (f ⨾ g) h k)
        (assocᴰ φ ψ (χ ⨾ᴰ ω)) (assocᴰ (φ ⨾ᴰ ψ) χ ω)

    private
      E₁ = comp-pathp₁ Hom
             (ap fst Q.σ₅₃) (ap fst Q.σ₃₂ ∙ ap fst Q.σ₂₁)
             (λ i → Pᴰ.σ̂₅₃ i .fst)
             (comp-pathp₁ Hom
               (ap fst Q.σ₃₂) (ap fst Q.σ₂₁)
               (λ i → Pᴰ.σ̂₃₂ i .fst) (λ i → Pᴰ.σ̂₂₁ i .fst))

      E₂ = comp-pathp₁ Hom
             (ap fst Q.σ₅₃) (ap fst (Q.σ₃₂ ∙ Q.σ₂₁))
             (λ i → Pᴰ.σ̂₅₃ i .fst) (λ i → ẑ i .fst)

      E₃ : Fam (ap fst (Q.σ₅₃ ∙ Q.σ₃₂ ∙ Q.σ₂₁))
      E₃ i = Pᴰ.top̂ i .fst

      E₄ : Fam (ap fst (Q.σ₅₄ ∙ Q.σ₄₁))
      E₄ i = Pᴰ.bot̂ i .fst

      E₅ = comp-pathp₁ Hom
             (ap fst Q.σ₅₄) (ap fst Q.σ₄₁)
             (λ i → Pᴰ.σ̂₅₄ i .fst) (λ i → Pᴰ.σ̂₄₁ i .fst)

      E₆ = comp-pathp₁ Hom
             (assoc f g (h ⨾ k)) (ap fst Q.σ₄₁)
             (assocᴰ φ ψ (χ ⨾ᴰ ω)) (λ i → Pᴰ.σ̂₄₁ i .fst)

      whisker̂₃ : PathP (λ m → Fam (Q.whisker₃ m)) topᴰ E₁
      whisker̂₃ m =
        comp-pathp₁ Hom
          (ap fst Q.σ₅₃) (Q.A₃ (~ m) ∙ ap fst Q.σ₂₁)
          (λ i → Pᴰ.σ̂₅₃ i .fst)
          (comp-pathp₁ Hom
            (Q.A₃ (~ m)) (ap fst Q.σ₂₁)
            (Â₃ (~ m)) (λ i → Pᴰ.σ̂₂₁ i .fst))

      step̂₁ : PathP (λ m → Fam (Q.step₁ m)) E₁ E₂
      step̂₁ m =
        comp-pathp₁ Hom
          (ap fst Q.σ₅₃) (ap-comp fst Q.σ₃₂ Q.σ₂₁ (~ m))
          (λ i → Pᴰ.σ̂₅₃ i .fst)
          (comp-pathp₁-ap Hom fst Q.σ₃₂ Q.σ₂₁
            (λ i → Pᴰ.σ̂₃₂ i .fst) (λ i → Pᴰ.σ̂₂₁ i .fst) (~ m))

      step̂₂ : PathP (λ m → Fam (Q.step₂ m)) E₂ E₃
      step̂₂ m =
        comp-pathp₁-ap Hom fst
          Q.σ₅₃ (Q.σ₃₂ ∙ Q.σ₂₁)
          (λ i → Pᴰ.σ̂₅₃ i .fst) (λ i → ẑ i .fst) (~ m)

      step̂₄ : PathP (λ m → Fam (Q.step₄ m)) E₄ E₅
      step̂₄ =
        comp-pathp₁-ap Hom fst Q.σ₅₄ Q.σ₄₁
          (λ i → Pᴰ.σ̂₅₄ i .fst) (λ i → Pᴰ.σ̂₄₁ i .fst)

      whisker̂₂ : PathP (λ m → Fam (Q.whisker₂ m)) E₅ E₆
      whisker̂₂ m =
        comp-pathp₁ Hom
          (Q.A₂ m) (ap fst Q.σ₄₁)
          (Â₂ m) (λ i → Pᴰ.σ̂₄₁ i .fst)

      whisker̂₁ : PathP (λ m → Fam (Q.whisker₁ m)) E₆ botᴰ
      whisker̂₁ m =
        comp-pathp₁ Hom
          (assoc f g (h ⨾ k)) (Q.A₁ m)
          (assocᴰ φ ψ (χ ⨾ᴰ ω)) (Â₁ m)

      pentagon̂● : PathP (λ m → Fam (Q.pentagon● m)) E₁ E₅
      pentagon̂● =
        comp-pathp₁ Fam Q.step₁ (Q.step₂ ∙ Q.step₃ ∙ Q.step₄)
          step̂₁
          (comp-pathp₁ Fam Q.step₂ (Q.step₃ ∙ Q.step₄)
            step̂₂
            (comp-pathp₁ Fam Q.step₃ Q.step₄
              Pᴰ.pentagon●ᴰ step̂₄))

    pentagonᴰ
      : PathP (λ m → PathP (λ i → hom[ Q.pentagon m i ] x' v')
                     (φ ⨾ᴰ ψ ⨾ᴰ χ ⨾ᴰ ω) (((φ ⨾ᴰ ψ) ⨾ᴰ χ) ⨾ᴰ ω))
              topᴰ botᴰ
    pentagonᴰ =
      comp-pathp₁ Fam
        Q.whisker₃ (Q.pentagon● ∙ Q.whisker₂ ∙ Q.whisker₁)
        whisker̂₃
        (comp-pathp₁ Fam
          Q.pentagon● (Q.whisker₂ ∙ Q.whisker₁)
          pentagon̂●
          (comp-pathp₁ Fam Q.whisker₂ Q.whisker₁
            whisker̂₂ whisker̂₁))
```
