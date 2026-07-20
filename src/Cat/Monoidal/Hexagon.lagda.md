Lane Biocini
July 2026

The irreducible coherence layer for the braided monoidal
structure. The associator is free and the braiding is free
(`Cat.Monoidal.Braid`), but the hexagon is not: the two braid
traversals of a triple composite — braiding past the composite
in one step, and braiding past each factor separately — are two
genuinely distinct paths between the same ternary operations,
and their identification is an axiom. Strict associativity of
the ternary orders collapses the old formulation's re-nesting
entirely: the field is one 2-path between a braid and a
composite of whiskered braids, at witness arguments, with its
morphism-grade displacement over it.

The object-level hexagon derives by the fiber projection idiom:
six witnesses in the one propositional fiber over the braided
target, the σ-lines between them shadowing the named associators
and braidings, the field entering as a `fst`-constant move — the
one link contractibility alone would leave a possibly nontrivial
loop on the object — and `is-contr→is-set` closing the tree.

Only the first hexagon H1 is recorded here: the braiding of `x`
past the composite `y ⊗₀ z`. The second hexagon H2 — braiding
the composite past one object — is neither a field nor a theorem
yet; whether it derives from H1 by symmetry or requires its own
field is open, and its interchange side is where the displaced
`ι-mult`/`⊗₁-interchange-natural` cells of
`Cat.Monoidal.Coherence` will be consumed.

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
open import Cat.Monoidal.Bifunctor
open import Cat.Monoidal.Coherence
open import Cat.Monoidal.Braid
```

## The braided-coherent record

One field per grade. At the object grade the two traversals of
`F ▿₀ G ▿₀ H` agree: the one-step braid past the pairing
`V ●₀ W` equals the `▿₀`-whiskers of the two single braids,
composable and parallel by strict associativity of the ternary
orders. The morphism grade is the same square one level up, the
`comp-pathp₂`-composite of the whiskered `⊗₁-braid♭` lines over
the object-grade sides.

```agda
record braided-coherent {o h} {C : category o h} {M : monoidal C}
  (B : braided M) : Type (o ⊔ h) where
  open monoidal M
  open theory₁ M
  open braided B
  private module C = category C

  field
    ⊗₀-hexagon♭
      : ∀ {F G H : ⊗₀-composite}
        (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
        (W : is-⊗₀-representable H)
      → ⊗₀-braid♭ U (V ●₀ W)
      ≡ ap (λ X → X ▿₀ H) (⊗₀-braid♭ U V)
        ∙ ap (λ X → G ▿₀ X) (⊗₀-braid♭ U W)

    ⊗₁-hexagon♭
      : ∀ {F F' G G' H H' : ⊗₀-composite}
          {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
          {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
          {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
          {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
          {θ : ⊗₁-composite H H'}
        (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
      → PathP (λ k → PathP (λ i → ⊗₁-composite
                                    (⊗₀-hexagon♭ U V W k i)
                                    (⊗₀-hexagon♭ U' V' W' k i))
                     (η ▿₁ ζ ▿₁ θ) (ζ ▿₁ θ ▿₁ η))
              (⊗₁-braid♭ Û (V̂ ●₁ Ŵ))
              (comp-pathp₂ ⊗₁-composite
                (ap (λ X → X ▿₀ H) (⊗₀-braid♭ U V))
                (ap (λ X → G ▿₀ X) (⊗₀-braid♭ U W))
                (ap (λ X → X ▿₀ H') (⊗₀-braid♭ U' V'))
                (ap (λ X → G' ▿₀ X) (⊗₀-braid♭ U' W'))
                (λ i → ⊗₁-braid♭ Û V̂ i ▿₁ θ)
                (λ i → ζ ▿₁ ⊗₁-braid♭ Û Ŵ i))
```

## The derived theory

```agda
module hexagon-theory {o h} {C : category o h} {M : monoidal C}
  {B : braided M} (BC : braided-coherent B) where
  open monoidal M
  open theory₁ M
  open coherence M
  open braided B
  open braid-theory B
  open braided-coherent BC
  private module C = category C
```

The braid straightener: `braid●₀` at slid witnesses, the
`nrm-slide₀` trick of `assoc●₀-nrm` — `fst` is preserved, so the
line connects the compound-witness braid to its `⊗₀-braid`
normal form with strict endpoints.

```agda
  braid●₀-nrm
    : ∀ {F G : ⊗₀-composite}
      (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
    → braid●₀ U V ≡ ⊗₀-braid (U .fst) (V .fst)
  braid●₀-nrm U V m =
    braid●₀ (nrm-slide₀ U m) (nrm-slide₀ V m)
```

## The hexagon fiber

All the work happens in the one propositional fiber over the
braided target `G ▿₀ H ▿₀ F`. The left traversal is three
σ-lines — the `↝`-whisker of the associator line along the
one-step braid, the braid σ-line at the pairing, the associator
line back. The right traversal is the same shape run through the
two-step base path, with two `fst`-constant links: `μ` rebends
the transport along the coherence field and splits it — the one
place the field enters — and `ρ` reconciles the `↝` along a
whiskered base line with the `●₀`-whisker of the transported
pairing, pure `∙`/`ap` algebra on the characterization.

```agda
  module hexagon₀ (x y z : C.ob) where
    F = ⊗₀-emb x
    G = ⊗₀-emb y
    H = ⊗₀-emb z

    βc : F ▿₀ G ▿₀ H ≡ G ▿₀ H ▿₀ F
    βc = ⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm y ●₀ ⊗₀-nrm z)

    β₁ : F ▿₀ G ▿₀ H ≡ G ▿₀ F ▿₀ H
    β₁ = ap (λ X → X ▿₀ H) (⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm y))

    β₂ : G ▿₀ F ▿₀ H ≡ G ▿₀ H ▿₀ F
    β₂ = ap (λ X → G ▿₀ X) (⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm z))

    n₁ n₂ : is-⊗₀-representable (F ▿₀ G ▿₀ H)
    n₁ = (⊗₀-nrm x ●₀ ⊗₀-nrm y) ●₀ ⊗₀-nrm z
    n₂ = ⊗₀-nrm x ●₀ (⊗₀-nrm y ●₀ ⊗₀-nrm z)

    -- the stations: left traversal down the a-line, right
    -- traversal down the c-line, meeting at a₄
    a₁ a₂ a₃ a₄ : is-⊗₀-representable (G ▿₀ H ▿₀ F)
    a₁ = n₁ ↝ βc
    a₂ = n₂ ↝ βc
    a₃ = (⊗₀-nrm y ●₀ ⊗₀-nrm z) ●₀ ⊗₀-nrm x
    a₄ = ⊗₀-nrm y ●₀ (⊗₀-nrm z ●₀ ⊗₀-nrm x)

    c₁ c₅ c₆ c₇ : is-⊗₀-representable (G ▿₀ H ▿₀ F)
    c₁ = (((⊗₀-nrm x ●₀ ⊗₀-nrm y) ↝ ⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm y))
           ●₀ ⊗₀-nrm z) ↝ β₂
    c₅ = ((⊗₀-nrm y ●₀ ⊗₀-nrm x) ●₀ ⊗₀-nrm z) ↝ β₂
    c₆ = (⊗₀-nrm y ●₀ (⊗₀-nrm x ●₀ ⊗₀-nrm z)) ↝ β₂
    c₇ = ⊗₀-nrm y ●₀ ((⊗₀-nrm x ●₀ ⊗₀-nrm z)
           ↝ ⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm z))

    T-contr : is-contr (is-⊗₀-representable (G ▿₀ H ▿₀ F))
    T-contr .center = a₃
    T-contr .paths  = is-⊗₀-representable-prop _ a₃
```

The left traversal's σ-lines. Every shadow is definitional: `↝`
and the pairings preserve `fst` by Σ-eta, so the associator
whiskers shadow to `sym ⊗₀-assoc` and the braid line to the
compound `braid●₀`.

```agda
    ℓ-assoc₁ : a₁ ≡ a₂
    ℓ-assoc₁ i = assoc-σ●₀ (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z) (~ i) ↝ βc

    ℓ-braid : a₂ ≡ a₃
    ℓ-braid = braid-σ●₀ (⊗₀-nrm x) (⊗₀-nrm y ●₀ ⊗₀-nrm z)

    ℓ-assoc₂ : a₃ ≡ a₄
    ℓ-assoc₂ = sym (assoc-σ●₀ (⊗₀-nrm y) (⊗₀-nrm z) (⊗₀-nrm x))
```

The right traversal. `μ` carries the field: the transport of
`n₁` along the one-step braid is rebent along `⊗₀-hexagon♭` to
the two-step composite, the transport split across the `∙` and
the whisker pushed inside the pairing — all on the
characterization side, `fst` constant throughout.

```agda
    μ : a₁ ≡ c₁
    μ i = (x ⊗₀ y) ⊗₀ z , κ i
      where
        B₀ = ⊗₀-nrm x ●₀ ⊗₀-nrm y
        bxy = ⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm y)
        E = ⊗₀-emb-comp (x ⊗₀ y) z
        f = λ X → X ▿₀ H

        inner : n₁ .snd ∙ β₁ ≡ E ∙ ap f (B₀ .snd ∙ bxy)
        inner =
            sym (Path.assoc E (ap f (B₀ .snd)) (ap f bxy))
          ∙ ap (E ∙_) (sym (ap-comp f (B₀ .snd) bxy))

        κ : n₁ .snd ∙ βc ≡ c₁ .snd
        κ = ap (n₁ .snd ∙_)
               (⊗₀-hexagon♭ (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z))
          ∙ Path.assoc (n₁ .snd) β₁ β₂
          ∙ ap (_∙ β₂) inner

    r-braid₁ : c₁ ≡ c₅
    r-braid₁ i = (braid-σ●₀ (⊗₀-nrm x) (⊗₀-nrm y) i ●₀ ⊗₀-nrm z) ↝ β₂

    r-assoc : c₅ ≡ c₆
    r-assoc i = assoc-σ●₀ (⊗₀-nrm y) (⊗₀-nrm x) (⊗₀-nrm z) (~ i) ↝ β₂

    ρ : c₆ ≡ c₇
    ρ i = y ⊗₀ (x ⊗₀ z) , θ i
      where
        XZ = ⊗₀-nrm x ●₀ ⊗₀-nrm z
        bxz = ⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm z)
        E' = ⊗₀-emb-comp y (x ⊗₀ z)
        g = λ X → G ▿₀ X

        θ : c₆ .snd ≡ c₇ .snd
        θ = sym (Path.assoc E' (ap g (XZ .snd)) (ap g bxz))
          ∙ ap (E' ∙_) (sym (ap-comp g (XZ .snd) bxz))

    r-braid₂ : c₇ ≡ a₄
    r-braid₂ i = ⊗₀-nrm y ●₀ braid-σ●₀ (⊗₀-nrm x) (⊗₀-nrm z) i
```

The fiber hexagon: the two traversals are parallel paths in a
contractible fiber. Opaque like `fiber-pentagon`: consumers only
project its slices, and the boundary reduces by the type-directed
rule.

```agda
    opaque
      fiber-hexagon
        : ℓ-assoc₁ ∙ ℓ-braid ∙ ℓ-assoc₂
        ≡ μ ∙ r-braid₁ ∙ r-assoc ∙ ρ ∙ r-braid₂
      fiber-hexagon =
        is-contr→is-set T-contr a₁ a₄
          (ℓ-assoc₁ ∙ ℓ-braid ∙ ℓ-assoc₂)
          (μ ∙ r-braid₁ ∙ r-assoc ∙ ρ ∙ r-braid₂)
```

## The object hexagon

The shadow tree: `ap-comp` splits each side's composite, the
σ-line shadows land on the named associators and braidings
definitionally, the `fst`-constant links shadow to `refl` and
discharge by `Path.unitl`, and the compound braid straightens by
`braid●₀-nrm`.

```agda
    step-l₁
      : ap fst (ℓ-assoc₁ ∙ ℓ-braid ∙ ℓ-assoc₂)
      ≡ sym (⊗₀-assoc x y z)
        ∙ braid●₀ (⊗₀-nrm x) (⊗₀-nrm y ●₀ ⊗₀-nrm z)
        ∙ sym (⊗₀-assoc y z x)
    step-l₁ =
        ap-comp fst ℓ-assoc₁ (ℓ-braid ∙ ℓ-assoc₂)
      ∙ ap (sym (⊗₀-assoc x y z) ∙_) (ap-comp fst ℓ-braid ℓ-assoc₂)

    step-l₂
      : sym (⊗₀-assoc x y z)
        ∙ braid●₀ (⊗₀-nrm x) (⊗₀-nrm y ●₀ ⊗₀-nrm z)
        ∙ sym (⊗₀-assoc y z x)
      ≡ sym (⊗₀-assoc x y z)
        ∙ ⊗₀-braid x (y ⊗₀ z)
        ∙ sym (⊗₀-assoc y z x)
    step-l₂ =
      ap (λ t → sym (⊗₀-assoc x y z) ∙ t ∙ sym (⊗₀-assoc y z x))
         (braid●₀-nrm (⊗₀-nrm x) (⊗₀-nrm y ●₀ ⊗₀-nrm z))

    step-r₁
      : ap fst (μ ∙ r-braid₁ ∙ r-assoc ∙ ρ ∙ r-braid₂)
      ≡ ap fst (r-braid₁ ∙ r-assoc ∙ ρ ∙ r-braid₂)
    step-r₁ =
        ap-comp fst μ (r-braid₁ ∙ r-assoc ∙ ρ ∙ r-braid₂)
      ∙ Path.unitl (ap fst (r-braid₁ ∙ r-assoc ∙ ρ ∙ r-braid₂))

    step-r₂
      : ap fst (r-braid₁ ∙ r-assoc ∙ ρ ∙ r-braid₂)
      ≡ ap (_⊗₀ z) (⊗₀-braid x y)
        ∙ sym (⊗₀-assoc y x z)
        ∙ ap (y ⊗₀_) (⊗₀-braid x z)
    step-r₂ =
        ap-comp fst r-braid₁ (r-assoc ∙ ρ ∙ r-braid₂)
      ∙ ap (ap (_⊗₀ z) (⊗₀-braid x y) ∙_)
          ( ap-comp fst r-assoc (ρ ∙ r-braid₂)
          ∙ ap (sym (⊗₀-assoc y x z) ∙_)
              ( ap-comp fst ρ r-braid₂
              ∙ Path.unitl (ap fst r-braid₂) ) )

    ⊗₀-hexagon
      : sym (⊗₀-assoc x y z)
        ∙ ⊗₀-braid x (y ⊗₀ z)
        ∙ sym (⊗₀-assoc y z x)
      ≡ ap (_⊗₀ z) (⊗₀-braid x y)
        ∙ sym (⊗₀-assoc y x z)
        ∙ ap (y ⊗₀_) (⊗₀-braid x z)
    ⊗₀-hexagon =
        sym (step-l₁ ∙ step-l₂)
      ∙ ap (ap fst) fiber-hexagon
      ∙ step-r₁ ∙ step-r₂
```
