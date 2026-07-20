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

The displayed triangle follows the same discipline over
`Cat.Coherence`'s σ-square tree — `triangle₁` under the same
dictionary, with `↝̂-fill` becoming `↝ᴰ-fill` and the displaced
coherence square supplied by `is-2-coherentᴰ`'s `is-cohᴰ`.

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

## The displayed 2-coherence

The coherence law one level up: over the base `is-coh` square, a
square of displayed composites relating the `▿ᴰ`-whiskers of
`▾-idnᴰ` and `emb-idn-absorbᴰ` — the displaced mates of the two
unit absorptions at the middle-unit composite. The hypothesis is
displayed over the base one: a `categoryᴰ` answers for its own
square over whatever square the base affirms, exactly as
`is-coh₁` rides `is-coh₀` in `is-monoidal-2-coherent`.

```agda
  record is-2-coherentᴰ (mid : is-2-coherent C)
    : Type (o ⊔ h ⊔ o' ⊔ h') where
    no-eta-equality

    open is-2-coherent mid

    field
      is-cohᴰ
        : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
          (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
        → PathP (λ j → PathP (λ i → composite[ is-coh f g j i ] x' z')
                       ((emb[ f' ] ▾ᴰ idn[ y' ]) ▿ᴰ emb[ g' ])
                       (emb[ f' ] ▿ᴰ emb[ g' ]))
                (λ i → ▾-idnᴰ (emb[ f' ]) i ▿ᴰ emb[ g' ])
                (λ i → emb[ f' ] ▿ᴰ emb-idn-absorbᴰ g' i)
```

## The displayed triangle

The triangle over `Cat.Coherence`'s `triangle`: a square of
displayed hom-lines whose top edge is the `comp-pathp₁`-composite
of `assocᴰ` and the whiskered `unitrᴰ`, bottom edge the whiskered
`unitlᴰ`. Every base cell was built as a wit-calculus projection,
so every leaf displaces by the same construction one level up:
the witnesses by `●ᴰ`/`↝ᴰ` at normal witnesses, the `ρ`-lines by
`↝ᴰ-fill`, each face square by `is-prop→SquareP` at the pointwise
contractible displayed witness family over its base mate — the
associator face riding `is-cohᴰ` exactly as its base rides
`is-coh` — the shuffle by `comp-pathp₁-ap`, and the fiber
triangle by the `●ᴰ-∙` glue of the `σ̂`-lines against the direct
one. Every interface between consecutive leaves is definitional.

The loop closes with `is-cohᴰ`: over `loop-sq`, the displaced
transports are joined by the `↝ᴰ`-image of the coherence square,
and `is-prop→SquareP` at the displayed witness family projects
the displaced `loop-refl` — the hom shadow of the base argument,
riding the same fiber square.

```agda
  module triangleᴰ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
    (φ : hom[ f ] x' y') (ψ : hom[ g ] y' z')
    where

    private module T = triangle C f g

    ι' : hom[ idn y ] y' y'
    ι' = idn[ y' ]

    N' : composite[ T.A ▿ T.E ▿ T.B ] x' z'
    N' = emb[ φ ] ▿ᴰ emb[ ι' ] ▿ᴰ emb[ ψ ]

    ê₁ : PathP (λ i → composite[ T.e₁ i ] x' z') N' (emb[ φ ] ▿ᴰ emb[ ψ ])
    ê₁ i = emb[ φ ] ▿ᴰ emb-idn-absorbᴰ ψ i

    ê₂ : PathP (λ i → composite[ T.e₂ i ] x' z') N' (emb[ φ ] ▿ᴰ emb[ ψ ])
    ê₂ i = ▾-idnᴰ (emb[ φ ]) i ▿ᴰ emb[ ψ ]

    r̂₁ : is-representable[ T.r₁ ] N'
    r̂₁ = nrm[ φ ] ●ᴰ (nrm[ ι' ] ●ᴰ nrm[ ψ ])

    r̂₂ : is-representable[ T.r₂ ] N'
    r̂₂ = (nrm[ φ ] ●ᴰ nrm[ ι' ]) ●ᴰ nrm[ ψ ]

    r̂₀¹ : is-representable[ T.r₀¹ ] N'
    r̂₀¹ = (nrm[ φ ] ●ᴰ nrm[ ψ ]) ↝ᴰ (λ i → ê₁ (~ i))

    r̂₀² : is-representable[ T.r₀² ] N'
    r̂₀² = (nrm[ φ ] ●ᴰ nrm[ ψ ]) ↝ᴰ (λ i → ê₂ (~ i))

    -- the displaced loop σ-line: repr-σᴰ[_] at the sealed base
    -- line; the displaced loop is its fst-shadow
    σ̂-loop : PathP (λ i → is-representable[ T.σ-loop i ] N') r̂₀¹ r̂₀²
    σ̂-loop = repr-σᴰ[ T.σ-loop ] r̂₀¹ r̂₀²

    loopᴰ : PathP (λ i → hom[ T.loop i ] x' z') (φ ⨾ᴰ ψ) (φ ⨾ᴰ ψ)
    loopᴰ i = σ̂-loop i .fst

    -- the displaced unitor witnesses: the endpoints of
    -- unitr-σ●ᴰ/unitl-σ●ᴰ, the very pairs the unitors project
    Ûf : is-representable[ T.Uf ] (emb[ φ ])
    Ûf = (nrm[ φ ] ●ᴰ nrm[ ι' ]) ↝ᴰ ▾-idnᴰ (emb[ φ ])

    V̂g : is-representable[ T.Vg ] (emb[ ψ ])
    V̂g = (nrm[ ι' ] ●ᴰ nrm[ ψ ]) ↝ᴰ emb-idn-absorbᴰ ψ

    ŝ₀ : is-representable[ T.s₀ ] (emb[ φ ] ▿ᴰ emb[ ψ ])
    ŝ₀ = nrm[ φ ] ●ᴰ nrm[ ψ ]

    ŝl : is-representable[ T.sl ] (emb[ φ ] ▿ᴰ emb[ ψ ])
    ŝl = nrm[ φ ] ●ᴰ V̂g

    ŝr : is-representable[ T.sr ] (emb[ φ ] ▿ᴰ emb[ ψ ])
    ŝr = Ûf ●ᴰ nrm[ ψ ]

    -- the displaced σ-lines: repr-σᴰ[_] instances at the sealed
    -- base lines — the seals are consumed as neutral families, no
    -- unfolding
    σ̂ₗᵣ : PathP (λ i → is-representable[ T.σₗᵣ i ]
                         (emb[ φ ] ▿ᴰ emb[ ψ ]))
                ŝl ŝr
    σ̂ₗᵣ = repr-σᴰ[ T.σₗᵣ ] ŝl ŝr

    σ̂ᵣ₀ : PathP (λ i → is-representable[ T.σᵣ₀ i ]
                         (emb[ φ ] ▿ᴰ emb[ ψ ]))
                ŝr ŝ₀
    σ̂ᵣ₀ = repr-σᴰ[ T.σᵣ₀ ] ŝr ŝ₀

    σ̂ₗ₀ : PathP (λ i → is-representable[ T.σₗ₀ i ]
                         (emb[ φ ] ▿ᴰ emb[ ψ ]))
                ŝl ŝ₀
    σ̂ₗ₀ = repr-σᴰ[ T.σₗ₀ ] ŝl ŝ₀

    -- the displaced ρ-lines: ↝ᴰ-fill slides, ●ᴰ-whiskered as at
    -- the base, over exactly the base slides
    ρ̂r : (m : I) → is-representable[ T.ρr m ] (ê₂ m)
    ρ̂r m = ↝ᴰ-fill (nrm[ φ ] ●ᴰ nrm[ ι' ]) (▾-idnᴰ (emb[ φ ])) m ●ᴰ nrm[ ψ ]

    ρ̂l : (m : I) → is-representable[ T.ρl m ] (ê₁ m)
    ρ̂l m = nrm[ φ ] ●ᴰ ↝ᴰ-fill (nrm[ ι' ] ●ᴰ nrm[ ψ ]) (emb-idn-absorbᴰ ψ) m

    face-rᴰ
      : PathP (λ i → hom[ ap fst T.σᵣ₀ i ] x' z')
              ((φ ⨾ᴰ ι') ⨾ᴰ ψ) (φ ⨾ᴰ ψ)
    face-rᴰ i = σ̂ᵣ₀ i .fst

    face-lᴰ
      : PathP (λ i → hom[ ap fst T.σₗ₀ i ] x' z')
              (φ ⨾ᴰ ι' ⨾ᴰ ψ) (φ ⨾ᴰ ψ)
    face-lᴰ i = σ̂ₗ₀ i .fst
```

The displaced unitor faces: `is-prop→SquareP` at the pointwise
contractible witness family over the base square, sides constant,
bottom the `●ᴰ`-whisker of the `unitr-σ●ᴰ` resp. `unitl-σ●ᴰ`
line — the `fst`-shadow's bottom edge is the whiskered `unitrᴰ`
resp. `unitlᴰ` definitionally.

```agda
    private
      wit-prop-r
        : (m i : I)
        → is-prop (is-representable[ T.face-σr m i ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
      wit-prop-r m i =
        is-contr→is-prop
          (subst is-contr
            (λ k → is-representable[ T.face-σr (m ∧ k) (i ∧ k) ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
            (repr-contrᴰ ŝr))

      wit-prop-l
        : (m i : I)
        → is-prop (is-representable[ T.face-σl m i ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
      wit-prop-l m i =
        is-contr→is-prop
          (subst is-contr
            (λ k → is-representable[ T.face-σl (m ∧ k) (i ∧ k) ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
            (repr-contrᴰ ŝl))

    -- the face bottoms, named: an inline face is elaborated in the
    -- ascription and again in the fill, and the two elaborations
    -- are compared term-by-term; a named face is checked once and
    -- compared by name (measured 14× on this square)
    whisker-σ̂r
      : PathP (λ i → is-representable[ unitr-σ● f i ● nrm g ]
                       (emb[ φ ] ▿ᴰ emb[ ψ ]))
              ŝr ŝ₀
    whisker-σ̂r i = unitr-σ●ᴰ φ i ●ᴰ nrm[ ψ ]

    whisker-σ̂l
      : PathP (λ i → is-representable[ nrm f ● unitl-σ● g i ]
                       (emb[ φ ] ▿ᴰ emb[ ψ ]))
              ŝl ŝ₀
    whisker-σ̂l i = nrm[ φ ] ●ᴰ unitl-σ●ᴰ ψ i

    assoc-σ̂
      : PathP (λ i → is-representable[ assoc-σ● (nrm f) (nrm (idn y))
                                                (nrm g) i ]
                       N')
              r̂₁ r̂₂
    assoc-σ̂ = assoc-σ●ᴰ nrm[ φ ] nrm[ ι' ] nrm[ ψ ]

    face-σ̂r
      : PathP (λ m → PathP (λ i → is-representable[ T.face-σr m i ]
                                    (emb[ φ ] ▿ᴰ emb[ ψ ]))
                     ŝr ŝ₀)
              σ̂ᵣ₀ whisker-σ̂r
    face-σ̂r = is-prop→SquareP wit-prop-r σ̂ᵣ₀ refl whisker-σ̂r refl

    face-r̂
      : PathP (λ m → PathP (λ i → hom[ T.face-r m i ] x' z')
                     ((φ ⨾ᴰ ι') ⨾ᴰ ψ) (φ ⨾ᴰ ψ))
              face-rᴰ (λ i → unitrᴰ φ i ⨾ᴰ ψ)
    face-r̂ m i = face-σ̂r m i .fst

    face-σ̂l
      : PathP (λ m → PathP (λ i → is-representable[ T.face-σl m i ]
                                    (emb[ φ ] ▿ᴰ emb[ ψ ]))
                     ŝl ŝ₀)
              σ̂ₗ₀ whisker-σ̂l
    face-σ̂l = is-prop→SquareP wit-prop-l σ̂ₗ₀ refl whisker-σ̂l refl

    face-l̂
      : PathP (λ m → PathP (λ i → hom[ T.face-l m i ] x' z')
                     (φ ⨾ᴰ ι' ⨾ᴰ ψ) (φ ⨾ᴰ ψ))
              face-lᴰ (λ i → φ ⨾ᴰ unitlᴰ ψ i)
    face-l̂ m i = face-σ̂l m i .fst
```

The displaced fiber triangle: the `●ᴰ-∙` glue of the two
`σ̂`-lines against the direct one, over `fiber-triangle` — the
glued edge's hom component is the `comp-pathp₁` of the
`repr-uniqueᴰ` shadows by construction.

```agda
    top̂ : PathP (λ i → is-representable[ (T.σₗᵣ ∙ T.σᵣ₀) i ]
                         (emb[ φ ] ▿ᴰ emb[ ψ ]))
                ŝl ŝ₀
    top̂ = ●ᴰ-∙ T.σₗᵣ T.σᵣ₀ σ̂ₗᵣ σ̂ᵣ₀

    private
      wit-prop-t
        : (m i : I)
        → is-prop (is-representable[ T.fiber-triangle m i ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
      wit-prop-t m i =
        is-contr→is-prop
          (subst is-contr
            (λ k → is-representable[ T.fiber-triangle (m ∧ k) (i ∧ k) ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
            (repr-contrᴰ ŝl))

    fiber-triangleᴰ
      : PathP (λ m → PathP (λ i → is-representable[ T.fiber-triangle m i ]
                                    (emb[ φ ] ▿ᴰ emb[ ψ ]))
                     ŝl ŝ₀)
              top̂ σ̂ₗ₀
    fiber-triangleᴰ = is-prop→SquareP wit-prop-t top̂ refl σ̂ₗ₀ refl
```

The chain of edges and the displaced leaves, glued along exactly
the base tree; the associator face and the whiskers that consume
it live under the coherence hypotheses, the rest is absolute.

```agda
    private
      Hom : hom x z → Type h'
      Hom t = hom[ t ] x' z'

      Fam : f ⨾ idn y ⨾ g ≡ f ⨾ g → Type h'
      Fam p = PathP (λ i → Hom (p i)) (φ ⨾ᴰ ι' ⨾ᴰ ψ) (φ ⨾ᴰ ψ)

    topᴰ : Fam (assoc f (idn y) g ∙ ap (_⨾ g) (unitr f))
    topᴰ =
      comp-pathp₁ Hom
        (assoc f (idn y) g) (ap (_⨾ g) (unitr f))
        (assocᴰ φ ι' ψ) (λ i → unitrᴰ φ i ⨾ᴰ ψ)

    botᴰ : Fam (ap (f ⨾_) (unitl g))
    botᴰ i = φ ⨾ᴰ unitlᴰ ψ i

    private
      E₁ = comp-pathp₁ Hom
             (ap fst T.σₗᵣ) (ap (_⨾ g) (unitr f))
             (λ i → σ̂ₗᵣ i .fst) (λ i → unitrᴰ φ i ⨾ᴰ ψ)

      E₂ = comp-pathp₁ Hom
             (ap fst T.σₗᵣ) (ap fst T.σᵣ₀)
             (λ i → σ̂ₗᵣ i .fst) face-rᴰ

      E₃ : Fam (ap fst (T.σₗᵣ ∙ T.σᵣ₀))
      E₃ i = top̂ i .fst

    step̂₁ : PathP (λ m → Fam (T.step₁ m)) E₂ E₃
    step̂₁ m =
      comp-pathp₁-ap Hom fst T.σₗᵣ T.σᵣ₀
        (λ i → σ̂ₗᵣ i .fst) face-rᴰ (~ m)

    step̂₂ : PathP (λ m → Fam (T.step₂ m)) E₃ face-lᴰ
    step̂₂ m i = fiber-triangleᴰ m i .fst

    whisker-r̂ : PathP (λ m → Fam (T.whisker-r m)) E₁ E₂
    whisker-r̂ m =
      comp-pathp₁ Hom
        (ap fst T.σₗᵣ) (T.face-r (~ m))
        (λ i → σ̂ₗᵣ i .fst) (face-r̂ (~ m))

    triangle-weak̂
      : PathP (λ m → Fam (T.triangle-weak m)) E₁ botᴰ
    triangle-weak̂ =
      comp-pathp₁ Fam T.whisker-r (T.step₁ ∙ T.step₂ ∙ T.face-l)
        whisker-r̂
        (comp-pathp₁ Fam T.step₁ (T.step₂ ∙ T.face-l)
          step̂₁
          (comp-pathp₁ Fam T.step₂ T.face-l
            step̂₂ face-l̂))

    module _ (mid : is-2-coherent C) (midᴰ : is-2-coherentᴰ mid) where
      private
        wit-prop-a
          : (m i : I)
          → is-prop (is-representable[ T.face-σa mid m i ]
                       (midᴰ .is-2-coherentᴰ.is-cohᴰ φ ψ (~ i) (~ m)))
        wit-prop-a m i =
          is-contr→is-prop
            (subst is-contr
              (λ k → is-representable[ T.face-σa mid (m ∧ k) (i ∧ k) ]
                       (midᴰ .is-2-coherentᴰ.is-cohᴰ φ ψ
                         (~ (i ∧ k)) (~ (m ∧ k))))
              (repr-contrᴰ ŝl))

      face-σ̂a
        : PathP (λ m → PathP (λ i → is-representable[ T.face-σa mid m i ]
                                      (midᴰ .is-2-coherentᴰ.is-cohᴰ φ ψ
                                        (~ i) (~ m)))
                       (ρ̂l (~ m)) (ρ̂r (~ m)))
                σ̂ₗᵣ assoc-σ̂
      face-σ̂a =
        is-prop→SquareP wit-prop-a
          σ̂ₗᵣ (λ m → ρ̂l (~ m))
          assoc-σ̂
          (λ m → ρ̂r (~ m))

      face-â
        : PathP (λ m → PathP (λ i → hom[ T.face-a mid m i ] x' z')
                       (φ ⨾ᴰ ι' ⨾ᴰ ψ) ((φ ⨾ᴰ ι') ⨾ᴰ ψ))
                (λ i → σ̂ₗᵣ i .fst) (assocᴰ φ ι' ψ)
      face-â m i = face-σ̂a m i .fst

      whisker-â
        : PathP (λ m → Fam (T.whisker-a mid m)) topᴰ E₁
      whisker-â m =
        comp-pathp₁ Hom
          (T.face-a mid (~ m)) (ap (_⨾ g) (unitr f))
          (face-â (~ m)) (λ i → unitrᴰ φ i ⨾ᴰ ψ)

      triangleᴰ
        : PathP (λ m → PathP (λ i → hom[ T.triangle mid m i ] x' z')
                       (φ ⨾ᴰ ι' ⨾ᴰ ψ) (φ ⨾ᴰ ψ))
                topᴰ botᴰ
      triangleᴰ =
        comp-pathp₁ Fam
          (T.whisker-a mid) T.triangle-weak
          whisker-â triangle-weak̂

      private
        K = T.loop-sq mid

        wprop : (k i : I) → is-prop (is-representable[ K k i ] N')
        wprop k i =
          is-contr→is-prop
            (subst is-contr
              (λ t → is-representable[ K (k ∧ t) (i ∧ t) ] N')
              (repr-contrᴰ r̂₀¹))

        -- the ↝ᴰ-image of the coherence square: the displaced
        -- is-coh-transport line joining the two loop witnesses
        ĉ : PathP (λ i → is-representable[ K i1 i ] N') r̂₀¹ r̂₀²
        ĉ i =
          (nrm[ φ ] ●ᴰ nrm[ ψ ])
          ↝ᴰ (λ t → midᴰ .is-2-coherentᴰ.is-cohᴰ φ ψ (~ i) (~ t))

        Ŝ : PathP (λ k → PathP (λ i → is-representable[ K k i ] N')
                         r̂₀¹ r̂₀²)
                  σ̂-loop ĉ
        Ŝ = is-prop→SquareP wprop σ̂-loop refl ĉ refl

      loopᴰ-refl
        : PathP (λ k → PathP (λ i → hom[ T.loop-refl mid k i ] x' z')
                       (φ ⨾ᴰ ψ) (φ ⨾ᴰ ψ))
                loopᴰ refl
      loopᴰ-refl k i = Ŝ k i .fst
```
