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
entirely: each field is one 2-path between a braid and a
composite of whiskered braids, at witness arguments, with its
morphism-grade displacement over it.

Each object-level hexagon derives by the fiber projection idiom:
six witnesses in the one propositional fiber over the braided
target, the σ-lines between them shadowing the named associators
and braidings, the field entering as a `fst`-constant move — the
one link contractibility alone would leave a possibly nontrivial
loop on the object — and `is-contr→is-set` closing the tree.

Both hexagons are fields, mirror images at both grades, named by
the slot carrying the pairing as `ι-mult-r₀`/`ι-mult-l₀` are:
`-r` braids one object past the pairing in the braid's right
slot, `-l` braids the pairing in its left slot past one object.
Neither derives from the other: on a skeletal strict model the
two are multiplicativity of the braiding in its right and left
slots separately, and braidings multiplicative in one slot only
exist. The identification of braid orientations that would make
one hexagon imply the other is the symmetric axiom — a future
layer, not this record. Nor does the `-l` field shrink to its
swap-half with the ι-half discharged through the interchange
coherences: a `▿₀`-block in a `▵₀`-flank moves only along
interchange lines — there is no strict redistribution into
single-factor flanks — so the swap-half form carries six
interchange conjugators, and the braid statement is the minimal
clean datum.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Hexagon where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using
  (ap-comp; ap-merge; comp-pathp₂-ap; comp-pathp₂-merge-map)
open import Core.Transport.Properties using (is-prop→SquareP)
open import Core.Transport.J using (subst)

open import Cat.Type
open import Cat.Monoidal
open import Cat.Monoidal.Bifunctor
open import Cat.Monoidal.Coherence
open import Cat.Monoidal.Braid
```

## The braided-coherent record

Two mirror fields per grade. At the object grade the two
traversals of the triple agree: the one-step braid past the
pairing equals the `▿₀`-whiskers of the two single braids — the
pairing in the braid's right slot for `-r`, in its left for
`-l` — composable and parallel by strict associativity of the
ternary orders. The morphism grade is the same square one level
up, the `comp-pathp₂`-composite of the whiskered `⊗₁-braid♭`
lines over the object-grade sides.

```agda
record braided-coherent {o h} {C : category o h} {M : monoidal C}
  (B : braided M) : Type (o ⊔ h) where
  open monoidal M
  open theory₁ M
  open braided B
  private module C = category C

  field
    ⊗₀-hexagon-r♭
      : ∀ {F G H : ⊗₀-composite}
        (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
        (W : is-⊗₀-representable H)
      → ⊗₀-braid♭ U (V ●₀ W)
      ≡ ap (λ X → X ▿₀ H) (⊗₀-braid♭ U V)
        ∙ ap (λ X → G ▿₀ X) (⊗₀-braid♭ U W)

    ⊗₁-hexagon-r♭
      : ∀ {F F' G G' H H' : ⊗₀-composite}
          {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
          {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
          {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
          {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
          {θ : ⊗₁-composite H H'}
        (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
      → PathP (λ k → PathP (λ i → ⊗₁-composite
                                    (⊗₀-hexagon-r♭ U V W k i)
                                    (⊗₀-hexagon-r♭ U' V' W' k i))
                     (η ▿₁ ζ ▿₁ θ) (ζ ▿₁ θ ▿₁ η))
              (⊗₁-braid♭ Û (V̂ ●₁ Ŵ))
              (comp-pathp₂ ⊗₁-composite
                (ap (λ X → X ▿₀ H) (⊗₀-braid♭ U V))
                (ap (λ X → G ▿₀ X) (⊗₀-braid♭ U W))
                (ap (λ X → X ▿₀ H') (⊗₀-braid♭ U' V'))
                (ap (λ X → G' ▿₀ X) (⊗₀-braid♭ U' W'))
                (λ i → ⊗₁-braid♭ Û V̂ i ▿₁ θ)
                (λ i → ζ ▿₁ ⊗₁-braid♭ Û Ŵ i))

    ⊗₀-hexagon-l♭
      : ∀ {F G H : ⊗₀-composite}
        (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
        (W : is-⊗₀-representable H)
      → ⊗₀-braid♭ (U ●₀ V) W
      ≡ ap (λ X → F ▿₀ X) (⊗₀-braid♭ V W)
        ∙ ap (λ X → X ▿₀ G) (⊗₀-braid♭ U W)

    ⊗₁-hexagon-l♭
      : ∀ {F F' G G' H H' : ⊗₀-composite}
          {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
          {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
          {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
          {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
          {θ : ⊗₁-composite H H'}
        (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
      → PathP (λ k → PathP (λ i → ⊗₁-composite
                                    (⊗₀-hexagon-l♭ U V W k i)
                                    (⊗₀-hexagon-l♭ U' V' W' k i))
                     (η ▿₁ ζ ▿₁ θ) (θ ▿₁ η ▿₁ ζ))
              (⊗₁-braid♭ (Û ●₁ V̂) Ŵ)
              (comp-pathp₂ ⊗₁-composite
                (ap (λ X → F ▿₀ X) (⊗₀-braid♭ V W))
                (ap (λ X → X ▿₀ G) (⊗₀-braid♭ U W))
                (ap (λ X → F' ▿₀ X) (⊗₀-braid♭ V' W'))
                (ap (λ X → X ▿₀ G') (⊗₀-braid♭ U' W'))
                (λ i → η ▿₁ ⊗₁-braid♭ V̂ Ŵ i)
                (λ i → ⊗₁-braid♭ Û Ŵ i ▿₁ ζ))
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

  braid●₁-nrm
    : ∀ {F F' G G' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
        {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
      (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ)
    → PathP (λ m → PathP (λ i → C.hom (braid●₀-nrm U V m i)
                                      (braid●₀-nrm U' V' m i))
                   (Û .fst ⊗₁ V̂ .fst) (V̂ .fst ⊗₁ Û .fst))
            (braid●₁ Û V̂) (⊗₁-braid (Û .fst) (V̂ .fst))
  braid●₁-nrm Û V̂ m =
    braid●₁ (nrm-slide₁ Û m) (nrm-slide₁ V̂ m)
```

## The hexagon-r fiber

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
  module hexagon-r₀ (x y z : C.ob) where
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
`n₁` along the one-step braid is rebent along `⊗₀-hexagon-r♭`
to the two-step composite, the transport split across the `∙`
and the whisker pushed inside the pairing — all on the
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
        inner = ap-merge f E (B₀ .snd) bxy

        κ : n₁ .snd ∙ βc ≡ c₁ .snd
        κ = ap (n₁ .snd ∙_)
               (⊗₀-hexagon-r♭ (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z))
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
        θ = ap-merge g E' (XZ .snd) bxz

    r-braid₂ : c₇ ≡ a₄
    r-braid₂ i = ⊗₀-nrm y ●₀ braid-σ●₀ (⊗₀-nrm x) (⊗₀-nrm z) i
```

The fiber hexagon: the two traversals are parallel paths in a
contractible fiber. Opaque like `fiber-pentagon`: consumers only
project its slices, and the boundary reduces by the type-directed
rule.

```agda
    ℓt : a₂ ≡ a₄
    ℓt = ℓ-braid ∙ ℓ-assoc₂

    ℓc : a₁ ≡ a₄
    ℓc = ℓ-assoc₁ ∙ ℓt

    rt₃ : c₆ ≡ a₄
    rt₃ = ρ ∙ r-braid₂

    rt₂ : c₅ ≡ a₄
    rt₂ = r-assoc ∙ rt₃

    rt₁ : c₁ ≡ a₄
    rt₁ = r-braid₁ ∙ rt₂

    rc : a₁ ≡ a₄
    rc = μ ∙ rt₁

    opaque
      fiber-hexagon : ℓc ≡ rc
      fiber-hexagon = is-contr→is-set T-contr a₁ a₄ ℓc rc
```

## The object hexagon-r

The shadow tree: `ap-comp` splits each side's composite, the
σ-line shadows land on the named associators and braidings
definitionally, the `fst`-constant links shadow to `refl` and
discharge by `Path.unitl`, and the compound braid straightens by
`braid●₀-nrm`.

```agda
    step-l₁
      : ap fst (ℓc)
      ≡ sym (⊗₀-assoc x y z)
        ∙ braid●₀ (⊗₀-nrm x) (⊗₀-nrm y ●₀ ⊗₀-nrm z)
        ∙ sym (⊗₀-assoc y z x)
    step-l₁ =
        ap-comp fst ℓ-assoc₁ (ℓt)
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
      : ap fst (rc)
      ≡ ap fst (rt₁)
    step-r₁ =
        ap-comp fst μ (rt₁)
      ∙ Path.unitl (ap fst (rt₁))

    step-r₂
      : ap fst (rt₁)
      ≡ ap (_⊗₀ z) (⊗₀-braid x y)
        ∙ sym (⊗₀-assoc y x z)
        ∙ ap (y ⊗₀_) (⊗₀-braid x z)
    step-r₂ =
        ap-comp fst r-braid₁ (rt₂)
      ∙ ap (ap (_⊗₀ z) (⊗₀-braid x y) ∙_)
          ( ap-comp fst r-assoc (rt₃)
          ∙ ap (sym (⊗₀-assoc y x z) ∙_)
              ( ap-comp fst ρ r-braid₂
              ∙ Path.unitl (ap fst r-braid₂) ) )

    sl = step-l₁ ∙ step-l₂
    sr = step-r₁ ∙ step-r₂

    ⊗₀-hexagon-r
      : sym (⊗₀-assoc x y z)
        ∙ ⊗₀-braid x (y ⊗₀ z)
        ∙ sym (⊗₀-assoc y z x)
      ≡ ap (_⊗₀ z) (⊗₀-braid x y)
        ∙ sym (⊗₀-assoc y x z)
        ∙ ap (y ⊗₀_) (⊗₀-braid x z)
    ⊗₀-hexagon-r =
        sym (sl)
      ∙ ap (ap fst) fiber-hexagon
      ∙ sr
```

## The hexagon-l fiber

The mirror, in the one propositional fiber over the braided
target `H ▿₀ F ▿₀ G`. Every link is the slot-mirror of its `-r`
mate: the left traversal runs the associator forward to the
compound-first bracketing, the braid σ-line at the compound
pairing, and the associator again on the braided side; on the
right, `μ` rebends the transport along `⊗₀-hexagon-l♭` with the
whisker pushed into the pairing's *second* slot, and `ρ`
reconciles on the first.

```agda
  module hexagon-l₀ (x y z : C.ob) where
    F = ⊗₀-emb x
    G = ⊗₀-emb y
    H = ⊗₀-emb z

    βc : F ▿₀ G ▿₀ H ≡ H ▿₀ F ▿₀ G
    βc = ⊗₀-braid♭ (⊗₀-nrm x ●₀ ⊗₀-nrm y) (⊗₀-nrm z)

    β₁ : F ▿₀ G ▿₀ H ≡ F ▿₀ H ▿₀ G
    β₁ = ap (λ X → F ▿₀ X) (⊗₀-braid♭ (⊗₀-nrm y) (⊗₀-nrm z))

    β₂ : F ▿₀ H ▿₀ G ≡ H ▿₀ F ▿₀ G
    β₂ = ap (λ X → X ▿₀ G) (⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm z))

    n₁ n₂ : is-⊗₀-representable (F ▿₀ G ▿₀ H)
    n₁ = (⊗₀-nrm x ●₀ ⊗₀-nrm y) ●₀ ⊗₀-nrm z
    n₂ = ⊗₀-nrm x ●₀ (⊗₀-nrm y ●₀ ⊗₀-nrm z)

    -- the stations: left traversal down the a-line, right
    -- traversal down the c-line, meeting at a₄
    a₁ a₂ a₃ a₄ : is-⊗₀-representable (H ▿₀ F ▿₀ G)
    a₁ = n₂ ↝ βc
    a₂ = n₁ ↝ βc
    a₃ = ⊗₀-nrm z ●₀ (⊗₀-nrm x ●₀ ⊗₀-nrm y)
    a₄ = (⊗₀-nrm z ●₀ ⊗₀-nrm x) ●₀ ⊗₀-nrm y

    c₁ c₅ c₆ c₇ : is-⊗₀-representable (H ▿₀ F ▿₀ G)
    c₁ = (⊗₀-nrm x ●₀ ((⊗₀-nrm y ●₀ ⊗₀-nrm z)
           ↝ ⊗₀-braid♭ (⊗₀-nrm y) (⊗₀-nrm z))) ↝ β₂
    c₅ = (⊗₀-nrm x ●₀ (⊗₀-nrm z ●₀ ⊗₀-nrm y)) ↝ β₂
    c₆ = ((⊗₀-nrm x ●₀ ⊗₀-nrm z) ●₀ ⊗₀-nrm y) ↝ β₂
    c₇ = ((⊗₀-nrm x ●₀ ⊗₀-nrm z)
           ↝ ⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm z)) ●₀ ⊗₀-nrm y

    T-contr : is-contr (is-⊗₀-representable (H ▿₀ F ▿₀ G))
    T-contr .center = a₃
    T-contr .paths  = is-⊗₀-representable-prop _ a₃
```

The left traversal's σ-lines, shadows definitional as in `-r`:
the associators land forward, the braid line on the compound
`braid●₀`.

```agda
    ℓ-assoc₁ : a₁ ≡ a₂
    ℓ-assoc₁ i = assoc-σ●₀ (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z) i ↝ βc

    ℓ-braid : a₂ ≡ a₃
    ℓ-braid = braid-σ●₀ (⊗₀-nrm x ●₀ ⊗₀-nrm y) (⊗₀-nrm z)

    ℓ-assoc₂ : a₃ ≡ a₄
    ℓ-assoc₂ = assoc-σ●₀ (⊗₀-nrm z) (⊗₀-nrm x) (⊗₀-nrm y)
```

The right traversal. `μ` carries the field: the transport of
`n₂` along the one-step braid is rebent along `⊗₀-hexagon-l♭`
to the two-step composite, the transport split across the `∙`
and the whisker pushed inside the pairing — all on the
characterization side, `fst` constant throughout.

```agda
    μ : a₁ ≡ c₁
    μ i = x ⊗₀ (y ⊗₀ z) , κ i
      where
        B₀ = ⊗₀-nrm y ●₀ ⊗₀-nrm z
        byz = ⊗₀-braid♭ (⊗₀-nrm y) (⊗₀-nrm z)
        E = ⊗₀-emb-comp x (y ⊗₀ z)
        g = λ X → F ▿₀ X

        inner : n₂ .snd ∙ β₁ ≡ E ∙ ap g (B₀ .snd ∙ byz)
        inner = ap-merge g E (B₀ .snd) byz

        κ : n₂ .snd ∙ βc ≡ c₁ .snd
        κ = ap (n₂ .snd ∙_)
               (⊗₀-hexagon-l♭ (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z))
          ∙ Path.assoc (n₂ .snd) β₁ β₂
          ∙ ap (_∙ β₂) inner

    r-braid₁ : c₁ ≡ c₅
    r-braid₁ i = (⊗₀-nrm x ●₀ braid-σ●₀ (⊗₀-nrm y) (⊗₀-nrm z) i) ↝ β₂

    r-assoc : c₅ ≡ c₆
    r-assoc i = assoc-σ●₀ (⊗₀-nrm x) (⊗₀-nrm z) (⊗₀-nrm y) i ↝ β₂

    ρ : c₆ ≡ c₇
    ρ i = (x ⊗₀ z) ⊗₀ y , θ i
      where
        XZ = ⊗₀-nrm x ●₀ ⊗₀-nrm z
        bxz = ⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm z)
        E' = ⊗₀-emb-comp (x ⊗₀ z) y
        f = λ X → X ▿₀ G

        θ : c₆ .snd ≡ c₇ .snd
        θ = ap-merge f E' (XZ .snd) bxz

    r-braid₂ : c₇ ≡ a₄
    r-braid₂ i = braid-σ●₀ (⊗₀-nrm x) (⊗₀-nrm z) i ●₀ ⊗₀-nrm y
```

The fiber hexagon, opaque as in `-r`.

```agda
    ℓt : a₂ ≡ a₄
    ℓt = ℓ-braid ∙ ℓ-assoc₂

    ℓc : a₁ ≡ a₄
    ℓc = ℓ-assoc₁ ∙ ℓt

    rt₃ : c₆ ≡ a₄
    rt₃ = ρ ∙ r-braid₂

    rt₂ : c₅ ≡ a₄
    rt₂ = r-assoc ∙ rt₃

    rt₁ : c₁ ≡ a₄
    rt₁ = r-braid₁ ∙ rt₂

    rc : a₁ ≡ a₄
    rc = μ ∙ rt₁

    opaque
      fiber-hexagon : ℓc ≡ rc
      fiber-hexagon = is-contr→is-set T-contr a₁ a₄ ℓc rc
```

## The object hexagon-l

The same shadow tree as `⊗₀-hexagon-r`'s, with plain associators
where the right hexagon had `sym`s — the mirror runs the other
way round the triple.

```agda
    step-l₁
      : ap fst (ℓc)
      ≡ ⊗₀-assoc x y z
        ∙ braid●₀ (⊗₀-nrm x ●₀ ⊗₀-nrm y) (⊗₀-nrm z)
        ∙ ⊗₀-assoc z x y
    step-l₁ =
        ap-comp fst ℓ-assoc₁ (ℓt)
      ∙ ap (⊗₀-assoc x y z ∙_) (ap-comp fst ℓ-braid ℓ-assoc₂)

    step-l₂
      : ⊗₀-assoc x y z
        ∙ braid●₀ (⊗₀-nrm x ●₀ ⊗₀-nrm y) (⊗₀-nrm z)
        ∙ ⊗₀-assoc z x y
      ≡ ⊗₀-assoc x y z
        ∙ ⊗₀-braid (x ⊗₀ y) z
        ∙ ⊗₀-assoc z x y
    step-l₂ =
      ap (λ t → ⊗₀-assoc x y z ∙ t ∙ ⊗₀-assoc z x y)
         (braid●₀-nrm (⊗₀-nrm x ●₀ ⊗₀-nrm y) (⊗₀-nrm z))

    step-r₁
      : ap fst (rc)
      ≡ ap fst (rt₁)
    step-r₁ =
        ap-comp fst μ (rt₁)
      ∙ Path.unitl (ap fst (rt₁))

    step-r₂
      : ap fst (rt₁)
      ≡ ap (x ⊗₀_) (⊗₀-braid y z)
        ∙ ⊗₀-assoc x z y
        ∙ ap (_⊗₀ y) (⊗₀-braid x z)
    step-r₂ =
        ap-comp fst r-braid₁ (rt₂)
      ∙ ap (ap (x ⊗₀_) (⊗₀-braid y z) ∙_)
          ( ap-comp fst r-assoc (rt₃)
          ∙ ap (⊗₀-assoc x z y ∙_)
              ( ap-comp fst ρ r-braid₂
              ∙ Path.unitl (ap fst r-braid₂) ) )

    sl = step-l₁ ∙ step-l₂
    sr = step-r₁ ∙ step-r₂

    ⊗₀-hexagon-l
      : ⊗₀-assoc x y z
        ∙ ⊗₀-braid (x ⊗₀ y) z
        ∙ ⊗₀-assoc z x y
      ≡ ap (x ⊗₀_) (⊗₀-braid y z)
        ∙ ⊗₀-assoc x z y
        ∙ ap (_⊗₀ y) (⊗₀-braid x z)
    ⊗₀-hexagon-l =
        sym (sl)
      ∙ ap (ap fst) fiber-hexagon
      ∙ sr
```

## The displaced hexagon-r

The `pentagon₁` layout over a pair of level-0 instances at
`⊗₁-wit-nrm` witnesses. The stations displace by `●₁`/`↝̂` over
their level-0 mates, the σ̂-lines are `assoc-σ●₁`/`braid-σ●₁`
instances — `↝̂`-slid and `●₁`-whiskered on the level-0 sides —
and the two `fst`-constant links are pair-paths with
definitionally-refl hom, the level-1 mirror of the level-0
same-`fst` discipline: an opaque `⊗₁-wit-σ[_,_]` line cannot feed
the tree's `Path.unitl` leaves, and in the wild setting no
set-fill discharges a constant-hom characterization square. Their
characterization squares are genuine constructions, glued by
`comp-pathp₂` at the family of `⊗₁-composite`-lines along the
`κ`/`θ` base trees — the field whisker (`⊗₁-hexagon-r♭` entering
as the second line), `comp-pathp₂-assoc`, and the whisker-image
merge `comp-pathp₂-merge-map`, one displaced cell per base leaf,
every interface definitional: the stations' characterizations
are themselves `comp-pathp₂` glues, so consecutive leaves meet
slot-for-slot.

```agda
  module hexagon-r₁ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
                    {z z'} (χ : C.hom z z')
    where

    private
      module Q  = hexagon-r₀ x  y  z
      module Q' = hexagon-r₀ x' y' z'

      Û = ⊗₁-wit-nrm φ
      V̂ = ⊗₁-wit-nrm ψ
      Ŵ = ⊗₁-wit-nrm χ

    N₁ : ⊗₁-composite (Q.G ▿₀ Q.H ▿₀ Q.F) (Q'.G ▿₀ Q'.H ▿₀ Q'.F)
    N₁ = ⊗₁-emb ψ ▿₁ ⊗₁-emb χ ▿₁ ⊗₁-emb φ

    β̂c : PathP (λ i → ⊗₁-composite (Q.βc i) (Q'.βc i))
               (⊗₁-emb φ ▿₁ ⊗₁-emb ψ ▿₁ ⊗₁-emb χ) N₁
    β̂c = ⊗₁-braid♭ Û (V̂ ●₁ Ŵ)

    β̂₁ : PathP (λ i → ⊗₁-composite (Q.β₁ i) (Q'.β₁ i))
               (⊗₁-emb φ ▿₁ ⊗₁-emb ψ ▿₁ ⊗₁-emb χ)
               (⊗₁-emb ψ ▿₁ ⊗₁-emb φ ▿₁ ⊗₁-emb χ)
    β̂₁ i = ⊗₁-braid♭ Û V̂ i ▿₁ ⊗₁-emb χ

    β̂₂ : PathP (λ i → ⊗₁-composite (Q.β₂ i) (Q'.β₂ i))
               (⊗₁-emb ψ ▿₁ ⊗₁-emb φ ▿₁ ⊗₁-emb χ) N₁
    β̂₂ i = ⊗₁-emb ψ ▿₁ ⊗₁-braid♭ Û Ŵ i

    n̂₁ : ⊗₁-wit Q.n₁ Q'.n₁ (⊗₁-emb φ ▿₁ ⊗₁-emb ψ ▿₁ ⊗₁-emb χ)
    n̂₁ = (Û ●₁ V̂) ●₁ Ŵ

    n̂₂ : ⊗₁-wit Q.n₂ Q'.n₂ (⊗₁-emb φ ▿₁ ⊗₁-emb ψ ▿₁ ⊗₁-emb χ)
    n̂₂ = Û ●₁ (V̂ ●₁ Ŵ)

    â₁ : ⊗₁-wit Q.a₁ Q'.a₁ N₁ ; â₁ = n̂₁ ↝̂ β̂c
    â₂ : ⊗₁-wit Q.a₂ Q'.a₂ N₁ ; â₂ = n̂₂ ↝̂ β̂c
    â₃ : ⊗₁-wit Q.a₃ Q'.a₃ N₁ ; â₃ = (V̂ ●₁ Ŵ) ●₁ Û
    â₄ : ⊗₁-wit Q.a₄ Q'.a₄ N₁ ; â₄ = V̂ ●₁ (Ŵ ●₁ Û)

    ĉ₁ : ⊗₁-wit Q.c₁ Q'.c₁ N₁
    ĉ₁ = (((Û ●₁ V̂) ↝̂ ⊗₁-braid♭ Û V̂) ●₁ Ŵ) ↝̂ β̂₂

    ĉ₅ : ⊗₁-wit Q.c₅ Q'.c₅ N₁ ; ĉ₅ = ((V̂ ●₁ Û) ●₁ Ŵ) ↝̂ β̂₂
    ĉ₆ : ⊗₁-wit Q.c₆ Q'.c₆ N₁ ; ĉ₆ = (V̂ ●₁ (Û ●₁ Ŵ)) ↝̂ β̂₂

    ĉ₇ : ⊗₁-wit Q.c₇ Q'.c₇ N₁
    ĉ₇ = V̂ ●₁ ((Û ●₁ Ŵ) ↝̂ ⊗₁-braid♭ Û Ŵ)
```

The σ̂-lines, over exactly the sealed level-0 lines.

```agda
    ℓ̂-assoc₁ : PathP (λ i → ⊗₁-wit (Q.ℓ-assoc₁ i) (Q'.ℓ-assoc₁ i) N₁) â₁ â₂
    ℓ̂-assoc₁ i = assoc-σ●₁ Û V̂ Ŵ (~ i) ↝̂ β̂c

    ℓ̂-braid : PathP (λ i → ⊗₁-wit (Q.ℓ-braid i) (Q'.ℓ-braid i) N₁) â₂ â₃
    ℓ̂-braid = braid-σ●₁ Û (V̂ ●₁ Ŵ)

    ℓ̂-assoc₂ : PathP (λ i → ⊗₁-wit (Q.ℓ-assoc₂ i) (Q'.ℓ-assoc₂ i) N₁) â₃ â₄
    ℓ̂-assoc₂ i = assoc-σ●₁ V̂ Ŵ Û (~ i)

    r̂-braid₁ : PathP (λ i → ⊗₁-wit (Q.r-braid₁ i) (Q'.r-braid₁ i) N₁) ĉ₁ ĉ₅
    r̂-braid₁ i = (braid-σ●₁ Û V̂ i ●₁ Ŵ) ↝̂ β̂₂

    r̂-assoc : PathP (λ i → ⊗₁-wit (Q.r-assoc i) (Q'.r-assoc i) N₁) ĉ₅ ĉ₆
    r̂-assoc i = assoc-σ●₁ V̂ Û Ŵ (~ i) ↝̂ β̂₂

    r̂-braid₂ : PathP (λ i → ⊗₁-wit (Q.r-braid₂ i) (Q'.r-braid₂ i) N₁) ĉ₇ â₄
    r̂-braid₂ i = V̂ ●₁ braid-σ●₁ Û Ŵ i
```

The μ̂-link: the pair-path at the constant hom, its
characterization square glued leaf-for-leaf along the `κ` base
tree — the field whisker, the displaced assoc, and the
`β₂`-whisker of the whisker-image merge.

```agda
    μ̂ : PathP (λ i → ⊗₁-wit (Q.μ i) (Q'.μ i) N₁) â₁ ĉ₁
    μ̂ i = (φ ⊗₁ ψ) ⊗₁ χ , Θ i
      where
        B₀  = ⊗₀-nrm x  ●₀ ⊗₀-nrm y
        B₀' = ⊗₀-nrm x' ●₀ ⊗₀-nrm y'
        bxy  = ⊗₀-braid♭ (⊗₀-nrm x)  (⊗₀-nrm y)
        bxy' = ⊗₀-braid♭ (⊗₀-nrm x') (⊗₀-nrm y')
        E  = ⊗₀-emb-comp (x ⊗₀ y) z
        E' = ⊗₀-emb-comp (x' ⊗₀ y') z'
        f  = λ X → X ▿₀ Q.H
        f' = λ X → X ▿₀ Q'.H
        H♭  = ⊗₀-hexagon-r♭ (⊗₀-nrm x)  (⊗₀-nrm y)  (⊗₀-nrm z)
        H♭' = ⊗₀-hexagon-r♭ (⊗₀-nrm x') (⊗₀-nrm y') (⊗₀-nrm z')

        inner  = ap-merge f  E  (B₀ .snd)  bxy
        inner' = ap-merge f' E' (B₀' .snd) bxy'

        ω : {A B : ⊗₀-composite} → ⊗₁-composite A B → ⊗₁-composite (f A) (f' B)
        ω ξ = ξ ▿₁ ⊗₁-emb χ

        Famc : ⊗₀-emb ((x ⊗₀ y) ⊗₀ z) ≡ Q.G ▿₀ Q.H ▿₀ Q.F
             → ⊗₀-emb ((x' ⊗₀ y') ⊗₀ z') ≡ Q'.G ▿₀ Q'.H ▿₀ Q'.F
             → Type _
        Famc p p' = PathP (λ t → ⊗₁-composite (p t) (p' t))
                          (⊗₁-emb ((φ ⊗₁ ψ) ⊗₁ χ)) N₁

        mid₁ : Famc (Q.n₁ .snd ∙ Q.β₁ ∙ Q.β₂) (Q'.n₁ .snd ∙ Q'.β₁ ∙ Q'.β₂)
        mid₁ =
          comp-pathp₂ ⊗₁-composite
            (Q.n₁ .snd) (Q.β₁ ∙ Q.β₂) (Q'.n₁ .snd) (Q'.β₁ ∙ Q'.β₂)
            (n̂₁ .snd)
            (comp-pathp₂ ⊗₁-composite Q.β₁ Q.β₂ Q'.β₁ Q'.β₂ β̂₁ β̂₂)

        mid₂ : Famc ((Q.n₁ .snd ∙ Q.β₁) ∙ Q.β₂) ((Q'.n₁ .snd ∙ Q'.β₁) ∙ Q'.β₂)
        mid₂ =
          comp-pathp₂ ⊗₁-composite
            (Q.n₁ .snd ∙ Q.β₁) Q.β₂ (Q'.n₁ .snd ∙ Q'.β₁) Q'.β₂
            (comp-pathp₂ ⊗₁-composite
              (Q.n₁ .snd) Q.β₁ (Q'.n₁ .snd) Q'.β₁ (n̂₁ .snd) β̂₁)
            β̂₂

        Θ-field
          : PathP (λ m → Famc (ap (Q.n₁ .snd ∙_) H♭ m)
                              (ap (Q'.n₁ .snd ∙_) H♭' m))
              (â₁ .snd) mid₁
        Θ-field m =
          comp-pathp₂ ⊗₁-composite
            (Q.n₁ .snd) (H♭ m) (Q'.n₁ .snd) (H♭' m)
            (n̂₁ .snd) (⊗₁-hexagon-r♭ Û V̂ Ŵ m)

        Θ-assoc
          : PathP (λ m → Famc (Path.assoc (Q.n₁ .snd) Q.β₁ Q.β₂ m)
                              (Path.assoc (Q'.n₁ .snd) Q'.β₁ Q'.β₂ m))
              mid₁ mid₂
        Θ-assoc =
          comp-pathp₂-assoc ⊗₁-composite (Q.n₁ .snd) Q.β₁ Q.β₂
            (Q'.n₁ .snd) Q'.β₁ Q'.β₂ (n̂₁ .snd) β̂₁ β̂₂

        Θ-merge
          : PathP (λ m → Famc (ap (_∙ Q.β₂) inner m)
                              (ap (_∙ Q'.β₂) inner' m))
              mid₂ (ĉ₁ .snd)
        Θ-merge m =
          comp-pathp₂ ⊗₁-composite (inner m) Q.β₂ (inner' m) Q'.β₂
            (comp-pathp₂-merge-map ⊗₁-composite ⊗₁-composite f f' ω
              E (B₀ .snd) bxy E' (B₀' .snd) bxy'
              (⊗₁-emb-comp (φ ⊗₁ ψ) χ) ((Û ●₁ V̂) .snd) (⊗₁-braid♭ Û V̂) m)
            β̂₂

        Θ : PathP (λ i → Famc (Q.μ i .snd) (Q'.μ i .snd)) (â₁ .snd) (ĉ₁ .snd)
        Θ = comp-pathp₂ Famc
              (ap (Q.n₁ .snd ∙_) H♭)
              (Path.assoc (Q.n₁ .snd) Q.β₁ Q.β₂ ∙ ap (_∙ Q.β₂) inner)
              (ap (Q'.n₁ .snd ∙_) H♭')
              (Path.assoc (Q'.n₁ .snd) Q'.β₁ Q'.β₂ ∙ ap (_∙ Q'.β₂) inner')
              Θ-field
              (comp-pathp₂ Famc
                (Path.assoc (Q.n₁ .snd) Q.β₁ Q.β₂) (ap (_∙ Q.β₂) inner)
                (Path.assoc (Q'.n₁ .snd) Q'.β₁ Q'.β₂) (ap (_∙ Q'.β₂) inner')
                Θ-assoc Θ-merge)
```

The ρ̂-link: the base tree is one `ap-merge` leaf, so the
characterization square is the bare whisker-image merge.

```agda
    ρ̂ : PathP (λ i → ⊗₁-wit (Q.ρ i) (Q'.ρ i) N₁) ĉ₆ ĉ₇
    ρ̂ i = ψ ⊗₁ (φ ⊗₁ χ) , θ̂ i
      where
        g  = λ X → Q.G ▿₀ X
        g' = λ X → Q'.G ▿₀ X

        ω : {A B : ⊗₀-composite} → ⊗₁-composite A B → ⊗₁-composite (g A) (g' B)
        ω ξ = ⊗₁-emb ψ ▿₁ ξ

        θ̂ : PathP (λ i → PathP (λ t → ⊗₁-composite (Q.ρ i .snd t)
                                                    (Q'.ρ i .snd t))
                         (⊗₁-emb (ψ ⊗₁ (φ ⊗₁ χ))) N₁)
              (ĉ₆ .snd) (ĉ₇ .snd)
        θ̂ = comp-pathp₂-merge-map ⊗₁-composite ⊗₁-composite g g' ω
              (⊗₀-emb-comp y (x ⊗₀ z)) ((⊗₀-nrm x ●₀ ⊗₀-nrm z) .snd)
              (⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm z))
              (⊗₀-emb-comp y' (x' ⊗₀ z')) ((⊗₀-nrm x' ●₀ ⊗₀-nrm z') .snd)
              (⊗₀-braid♭ (⊗₀-nrm x') (⊗₀-nrm z'))
              (⊗₁-emb-comp ψ (φ ⊗₁ χ)) ((Û ●₁ Ŵ) .snd) (⊗₁-braid♭ Û Ŵ)
```

The traversal glues and the fiber square — the `pentagon●₁`
closing move.

```agda
    private
      ℓt  = Q.ℓt
      ℓt' = Q'.ℓt
      ℓc  = Q.ℓc
      ℓc' = Q'.ℓc
      rt₃  = Q.rt₃
      rt₃' = Q'.rt₃
      rt₂  = Q.rt₂
      rt₂' = Q'.rt₂
      rt₁  = Q.rt₁
      rt₁' = Q'.rt₁
      rc  = Q.rc
      rc' = Q'.rc
      sl  = Q.sl
      sl' = Q'.sl
      sr  = Q.sr
      sr' = Q'.sr

      ẑ : PathP (λ i → ⊗₁-wit ((ℓt) i)
                              ((ℓt') i) N₁)
                â₂ â₄
      ẑ = ⊗₁-wit-∙ Q.ℓ-braid Q.ℓ-assoc₂ Q'.ℓ-braid Q'.ℓ-assoc₂
            ℓ̂-braid ℓ̂-assoc₂

      ŵ₃ : PathP (λ i → ⊗₁-wit ((rt₃) i)
                               ((rt₃') i) N₁)
                 ĉ₆ â₄
      ŵ₃ = ⊗₁-wit-∙ Q.ρ Q.r-braid₂ Q'.ρ Q'.r-braid₂ ρ̂ r̂-braid₂

      ŵ₂ : PathP (λ i → ⊗₁-wit ((rt₂) i)
                               ((rt₂') i) N₁)
                 ĉ₅ â₄
      ŵ₂ = ⊗₁-wit-∙ Q.r-assoc (rt₃)
             Q'.r-assoc (rt₃') r̂-assoc ŵ₃

      ŵ₁ : PathP (λ i → ⊗₁-wit ((rt₁) i)
                               ((rt₁') i)
                               N₁)
                 ĉ₁ â₄
      ŵ₁ = ⊗₁-wit-∙ Q.r-braid₁ (rt₂)
             Q'.r-braid₁ (rt₂') r̂-braid₁ ŵ₂

    top̂ : PathP (λ i → ⊗₁-wit ((ℓc) i)
                              ((ℓc') i) N₁)
                â₁ â₄
    top̂ = ⊗₁-wit-∙ Q.ℓ-assoc₁ (ℓt)
                   Q'.ℓ-assoc₁ (ℓt')
            ℓ̂-assoc₁ ẑ

    bot̂ : PathP (λ i → ⊗₁-wit ((rc) i)
                              ((rc') i)
                              N₁)
                â₁ â₄
    bot̂ = ⊗₁-wit-∙ Q.μ (rt₁)
                   Q'.μ (rt₁')
            μ̂ ŵ₁

    wit-prop
      : (j i : Core.Base.I)
      → is-prop (⊗₁-wit (Q.fiber-hexagon j i) (Q'.fiber-hexagon j i) N₁)
    wit-prop j i =
      is-contr→is-prop
        (subst is-contr
          (λ k → ⊗₁-wit (Q.fiber-hexagon (j ∧ k) (i ∧ k))
                        (Q'.fiber-hexagon (j ∧ k) (i ∧ k)) N₁)
          (⊗₁-wit-contr â₁))

    fiber-hexagon₁
      : PathP (λ j → PathP (λ i → ⊗₁-wit (Q.fiber-hexagon j i)
                                         (Q'.fiber-hexagon j i) N₁)
                     â₁ â₄)
              top̂ bot̂
    fiber-hexagon₁ = is-prop→SquareP wit-prop top̂ refl bot̂ refl
```

## The canonical displaced hexagon-r

The hexagon over `⊗₀-hexagon-r` itself. Every leaf of the base
tree displaces by construction: the `ap-comp` shuffles are
`comp-pathp₂-ap` squares, the two `fst`-constant links discharge
by `comp-pathp₂-unitl` — the pair-path discipline makes their
hom lines literal `refl`s — the compound braid straightens by
`braid●₁-nrm`, and the core is the fiber square's `fst`-shadow.
`comp-pathp₂` at the family of hexagon fillers glues the
displaced leaves along exactly the base tree.

```agda
    private
      Fam : (x ⊗₀ y) ⊗₀ z ≡ y ⊗₀ (z ⊗₀ x)
          → (x' ⊗₀ y') ⊗₀ z' ≡ y' ⊗₀ (z' ⊗₀ x')
          → Type h
      Fam p p' = PathP (λ i → C.hom (p i) (p' i))
                       ((φ ⊗₁ ψ) ⊗₁ χ) (ψ ⊗₁ (χ ⊗₁ φ))

    top₁ : Fam (sym (⊗₀-assoc x y z)
                ∙ ⊗₀-braid x (y ⊗₀ z) ∙ sym (⊗₀-assoc y z x))
               (sym (⊗₀-assoc x' y' z')
                ∙ ⊗₀-braid x' (y' ⊗₀ z') ∙ sym (⊗₀-assoc y' z' x'))
    top₁ =
      comp-pathp₂ C.hom
        (sym (⊗₀-assoc x y z))
        (⊗₀-braid x (y ⊗₀ z) ∙ sym (⊗₀-assoc y z x))
        (sym (⊗₀-assoc x' y' z'))
        (⊗₀-braid x' (y' ⊗₀ z') ∙ sym (⊗₀-assoc y' z' x'))
        (λ i → ⊗₁-assoc φ ψ χ (~ i))
        (comp-pathp₂ C.hom
          (⊗₀-braid x (y ⊗₀ z)) (sym (⊗₀-assoc y z x))
          (⊗₀-braid x' (y' ⊗₀ z')) (sym (⊗₀-assoc y' z' x'))
          (⊗₁-braid φ (ψ ⊗₁ χ))
          (λ i → ⊗₁-assoc ψ χ φ (~ i)))

    bot₁ : Fam (ap (_⊗₀ z) (⊗₀-braid x y)
                ∙ sym (⊗₀-assoc y x z) ∙ ap (y ⊗₀_) (⊗₀-braid x z))
               (ap (_⊗₀ z') (⊗₀-braid x' y')
                ∙ sym (⊗₀-assoc y' x' z') ∙ ap (y' ⊗₀_) (⊗₀-braid x' z'))
    bot₁ =
      comp-pathp₂ C.hom
        (ap (_⊗₀ z) (⊗₀-braid x y))
        (sym (⊗₀-assoc y x z) ∙ ap (y ⊗₀_) (⊗₀-braid x z))
        (ap (_⊗₀ z') (⊗₀-braid x' y'))
        (sym (⊗₀-assoc y' x' z') ∙ ap (y' ⊗₀_) (⊗₀-braid x' z'))
        (λ i → ⊗₁-braid φ ψ i ⊗₁ χ)
        (comp-pathp₂ C.hom
          (sym (⊗₀-assoc y x z)) (ap (y ⊗₀_) (⊗₀-braid x z))
          (sym (⊗₀-assoc y' x' z')) (ap (y' ⊗₀_) (⊗₀-braid x' z'))
          (λ i → ⊗₁-assoc ψ φ χ (~ i))
          (λ i → ψ ⊗₁ ⊗₁-braid φ χ i))
```

The chain of edges: the shadows of the glued traversals, the
σ-projection composites in their degrees of splitting, and the
half-straightened forms.

```agda
    private
      E₀ : Fam (ap fst (ℓc))
               (ap fst (ℓc'))
      E₀ i = top̂ i .fst

      E₁ = comp-pathp₂ C.hom
             (ap fst Q.ℓ-assoc₁) (ap fst (ℓt))
             (ap fst Q'.ℓ-assoc₁) (ap fst (ℓt'))
             (λ i → ℓ̂-assoc₁ i .fst) (λ i → ẑ i .fst)

      E₂ = comp-pathp₂ C.hom
             (ap fst Q.ℓ-assoc₁) (ap fst Q.ℓ-braid ∙ ap fst Q.ℓ-assoc₂)
             (ap fst Q'.ℓ-assoc₁) (ap fst Q'.ℓ-braid ∙ ap fst Q'.ℓ-assoc₂)
             (λ i → ℓ̂-assoc₁ i .fst)
             (comp-pathp₂ C.hom
               (ap fst Q.ℓ-braid) (ap fst Q.ℓ-assoc₂)
               (ap fst Q'.ℓ-braid) (ap fst Q'.ℓ-assoc₂)
               (λ i → ℓ̂-braid i .fst) (λ i → ℓ̂-assoc₂ i .fst))

      R₀ : Fam (ap fst (rc))
               (ap fst (rc'))
      R₀ i = bot̂ i .fst

      R₁ = comp-pathp₂ C.hom
             (ap fst Q.μ)
             (ap fst (rt₁))
             (ap fst Q'.μ)
             (ap fst (rt₁'))
             (λ i → μ̂ i .fst) (λ i → ŵ₁ i .fst)

      R₂ : Fam (ap fst (rt₁))
               (ap fst (rt₁'))
      R₂ i = ŵ₁ i .fst

      R₃ = comp-pathp₂ C.hom
             (ap fst Q.r-braid₁) (ap fst (rt₂))
             (ap fst Q'.r-braid₁) (ap fst (rt₂'))
             (λ i → r̂-braid₁ i .fst) (λ i → ŵ₂ i .fst)
```

One displaced leaf per base leaf, glued along exactly the base
trees; the inner families fix the whisker heads as the base
whiskers do.

```agda
      split-l̂
        : PathP (λ m → Fam (ap-comp fst Q.ℓ-assoc₁ (ℓt) m)
                           (ap-comp fst Q'.ℓ-assoc₁ (ℓt') m))
                E₀ E₁
      split-l̂ m =
        comp-pathp₂-ap C.hom fst fst
          Q.ℓ-assoc₁ (ℓt)
          Q'.ℓ-assoc₁ (ℓt')
          (λ i → ℓ̂-assoc₁ i .fst) (λ i → ẑ i .fst) m

      whisk-l̂
        : PathP (λ m → Fam (ap (sym (⊗₀-assoc x y z) ∙_)
                              (ap-comp fst Q.ℓ-braid Q.ℓ-assoc₂) m)
                           (ap (sym (⊗₀-assoc x' y' z') ∙_)
                              (ap-comp fst Q'.ℓ-braid Q'.ℓ-assoc₂) m))
                E₁ E₂
      whisk-l̂ m =
        comp-pathp₂ C.hom
          (ap fst Q.ℓ-assoc₁) (ap-comp fst Q.ℓ-braid Q.ℓ-assoc₂ m)
          (ap fst Q'.ℓ-assoc₁) (ap-comp fst Q'.ℓ-braid Q'.ℓ-assoc₂ m)
          (λ i → ℓ̂-assoc₁ i .fst)
          (comp-pathp₂-ap C.hom fst fst Q.ℓ-braid Q.ℓ-assoc₂
            Q'.ℓ-braid Q'.ℓ-assoc₂
            (λ i → ℓ̂-braid i .fst) (λ i → ℓ̂-assoc₂ i .fst) m)

      step-l̂₁ : PathP (λ m → Fam (Q.step-l₁ m) (Q'.step-l₁ m)) E₀ E₂
      step-l̂₁ =
        comp-pathp₂ Fam
          (ap-comp fst Q.ℓ-assoc₁ (ℓt))
          (ap (sym (⊗₀-assoc x y z) ∙_) (ap-comp fst Q.ℓ-braid Q.ℓ-assoc₂))
          (ap-comp fst Q'.ℓ-assoc₁ (ℓt'))
          (ap (sym (⊗₀-assoc x' y' z') ∙_) (ap-comp fst Q'.ℓ-braid Q'.ℓ-assoc₂))
          split-l̂ whisk-l̂

      step-l̂₂ : PathP (λ m → Fam (Q.step-l₂ m) (Q'.step-l₂ m)) E₂ top₁
      step-l̂₂ m =
        comp-pathp₂ C.hom
          (sym (⊗₀-assoc x y z))
          (braid●₀-nrm (⊗₀-nrm x) (⊗₀-nrm y ●₀ ⊗₀-nrm z) m
            ∙ sym (⊗₀-assoc y z x))
          (sym (⊗₀-assoc x' y' z'))
          (braid●₀-nrm (⊗₀-nrm x') (⊗₀-nrm y' ●₀ ⊗₀-nrm z') m
            ∙ sym (⊗₀-assoc y' z' x'))
          (λ i → ⊗₁-assoc φ ψ χ (~ i))
          (comp-pathp₂ C.hom
            (braid●₀-nrm (⊗₀-nrm x) (⊗₀-nrm y ●₀ ⊗₀-nrm z) m)
            (sym (⊗₀-assoc y z x))
            (braid●₀-nrm (⊗₀-nrm x') (⊗₀-nrm y' ●₀ ⊗₀-nrm z') m)
            (sym (⊗₀-assoc y' z' x'))
            (braid●₁-nrm Û (V̂ ●₁ Ŵ) m)
            (λ i → ⊗₁-assoc ψ χ φ (~ i)))

      left̂ : PathP (λ m → Fam ((sl) m)
                              ((sl') m))
                   E₀ top₁
      left̂ = comp-pathp₂ Fam Q.step-l₁ Q.step-l₂ Q'.step-l₁ Q'.step-l₂
               step-l̂₁ step-l̂₂

      left̂⁻ : PathP (λ m → Fam (sym (sl) m)
                               (sym (sl') m))
                    top₁ E₀
      left̂⁻ m = left̂ (~ m)

      hex̂● : PathP (λ m → Fam (ap (ap fst) Q.fiber-hexagon m)
                              (ap (ap fst) Q'.fiber-hexagon m))
                   E₀ R₀
      hex̂● m i = fiber-hexagon₁ m i .fst

      split-r̂
        : PathP (λ m → Fam (ap-comp fst Q.μ
                              (rt₁) m)
                           (ap-comp fst Q'.μ
                              (rt₁') m))
                R₀ R₁
      split-r̂ m =
        comp-pathp₂-ap C.hom fst fst
          Q.μ (rt₁)
          Q'.μ (rt₁')
          (λ i → μ̂ i .fst) (λ i → ŵ₁ i .fst) m

      unitl̂-r
        : PathP (λ m → Fam (Path.unitl
                              (ap fst (rt₁)) m)
                           (Path.unitl
                              (ap fst (rt₁')) m))
                R₁ R₂
      unitl̂-r m =
        comp-pathp₂-unitl C.hom
          (ap fst (rt₁))
          (ap fst (rt₁'))
          (λ i → ŵ₁ i .fst) m

      step-r̂₁ : PathP (λ m → Fam (Q.step-r₁ m) (Q'.step-r₁ m)) R₀ R₂
      step-r̂₁ =
        comp-pathp₂ Fam
          (ap-comp fst Q.μ (rt₁))
          (Path.unitl (ap fst (rt₁)))
          (ap-comp fst Q'.μ (rt₁'))
          (Path.unitl (ap fst (rt₁')))
          split-r̂ unitl̂-r
```

The `step-r₂` tree, two whiskers deep; the innermost unitl leaf
lands on the ρ̂-link's literal-`refl` hom exactly as `step-r₁`'s
lands on the μ̂-link's.

```agda
      FamI : (y ⊗₀ x) ⊗₀ z ≡ y ⊗₀ (z ⊗₀ x)
           → (y' ⊗₀ x') ⊗₀ z' ≡ y' ⊗₀ (z' ⊗₀ x')
           → Type h
      FamI p p' = PathP (λ i → C.hom (p i) (p' i))
                        ((ψ ⊗₁ φ) ⊗₁ χ) (ψ ⊗₁ (χ ⊗₁ φ))

      FamII : y ⊗₀ (x ⊗₀ z) ≡ y ⊗₀ (z ⊗₀ x)
            → y' ⊗₀ (x' ⊗₀ z') ≡ y' ⊗₀ (z' ⊗₀ x')
            → Type h
      FamII p p' = PathP (λ i → C.hom (p i) (p' i))
                         (ψ ⊗₁ (φ ⊗₁ χ)) (ψ ⊗₁ (χ ⊗₁ φ))

      S₀ : FamI (ap fst (rt₂))
                (ap fst (rt₂'))
      S₀ i = ŵ₂ i .fst

      S₁ = comp-pathp₂ C.hom
             (ap fst Q.r-assoc) (ap fst (rt₃))
             (ap fst Q'.r-assoc) (ap fst (rt₃'))
             (λ i → r̂-assoc i .fst) (λ i → ŵ₃ i .fst)

      S₂ = comp-pathp₂ C.hom
             (sym (⊗₀-assoc y x z)) (ap (y ⊗₀_) (⊗₀-braid x z))
             (sym (⊗₀-assoc y' x' z')) (ap (y' ⊗₀_) (⊗₀-braid x' z'))
             (λ i → ⊗₁-assoc ψ φ χ (~ i))
             (λ i → ψ ⊗₁ ⊗₁-braid φ χ i)

      T₀ : FamII (ap fst (rt₃)) (ap fst (rt₃'))
      T₀ i = ŵ₃ i .fst

      T₁ = comp-pathp₂ C.hom
             (ap fst Q.ρ) (ap fst Q.r-braid₂)
             (ap fst Q'.ρ) (ap fst Q'.r-braid₂)
             (λ i → ρ̂ i .fst) (λ i → r̂-braid₂ i .fst)

      T₂ : FamII (ap fst Q.r-braid₂) (ap fst Q'.r-braid₂)
      T₂ i = r̂-braid₂ i .fst

      uρ  = ap-comp fst Q.ρ Q.r-braid₂ ∙ Path.unitl (ap fst Q.r-braid₂)
      uρ' = ap-comp fst Q'.ρ Q'.r-braid₂ ∙ Path.unitl (ap fst Q'.r-braid₂)

      split-ρ̂
        : PathP (λ m → FamII (ap-comp fst Q.ρ Q.r-braid₂ m)
                             (ap-comp fst Q'.ρ Q'.r-braid₂ m))
                T₀ T₁
      split-ρ̂ m =
        comp-pathp₂-ap C.hom fst fst Q.ρ Q.r-braid₂ Q'.ρ Q'.r-braid₂
          (λ i → ρ̂ i .fst) (λ i → r̂-braid₂ i .fst) m

      unitl̂-ρ
        : PathP (λ m → FamII (Path.unitl (ap fst Q.r-braid₂) m)
                             (Path.unitl (ap fst Q'.r-braid₂) m))
                T₁ T₂
      unitl̂-ρ m =
        comp-pathp₂-unitl C.hom
          (ap fst Q.r-braid₂) (ap fst Q'.r-braid₂)
          (λ i → r̂-braid₂ i .fst) m

      inner̂₂
        : PathP (λ m → FamII (uρ m) (uρ' m)) T₀ T₂
      inner̂₂ =
        comp-pathp₂ FamII
          (ap-comp fst Q.ρ Q.r-braid₂) (Path.unitl (ap fst Q.r-braid₂))
          (ap-comp fst Q'.ρ Q'.r-braid₂) (Path.unitl (ap fst Q'.r-braid₂))
          split-ρ̂ unitl̂-ρ

      split-assoĉ
        : PathP (λ m → FamI (ap-comp fst Q.r-assoc (rt₃) m)
                            (ap-comp fst Q'.r-assoc (rt₃') m))
                S₀ S₁
      split-assoĉ m =
        comp-pathp₂-ap C.hom fst fst
          Q.r-assoc (rt₃) Q'.r-assoc (rt₃')
          (λ i → r̂-assoc i .fst) (λ i → ŵ₃ i .fst) m

      vα  = ap-comp fst Q.r-assoc (rt₃)
              ∙ ap (sym (⊗₀-assoc y x z) ∙_) uρ
      vα' = ap-comp fst Q'.r-assoc (rt₃')
              ∙ ap (sym (⊗₀-assoc y' x' z') ∙_) uρ'

      whisk-r̂₂
        : PathP (λ m → FamI (ap (sym (⊗₀-assoc y x z) ∙_) uρ m)
                            (ap (sym (⊗₀-assoc y' x' z') ∙_) uρ' m))
                S₁ S₂
      whisk-r̂₂ m =
        comp-pathp₂ C.hom
          (ap fst Q.r-assoc) (uρ m)
          (ap fst Q'.r-assoc) (uρ' m)
          (λ i → r̂-assoc i .fst) (inner̂₂ m)

      inner̂₁
        : PathP (λ m → FamI (vα m) (vα' m)) S₀ S₂
      inner̂₁ =
        comp-pathp₂ FamI
          (ap-comp fst Q.r-assoc (rt₃))
          (ap (sym (⊗₀-assoc y x z) ∙_) uρ)
          (ap-comp fst Q'.r-assoc (rt₃'))
          (ap (sym (⊗₀-assoc y' x' z') ∙_) uρ')
          split-assoĉ whisk-r̂₂

      whisk-braid̂
        : PathP (λ m → Fam (ap (ap (_⊗₀ z) (⊗₀-braid x y) ∙_) vα m)
                           (ap (ap (_⊗₀ z') (⊗₀-braid x' y') ∙_) vα' m))
                R₃ bot₁
      whisk-braid̂ m =
        comp-pathp₂ C.hom
          (ap fst Q.r-braid₁) (vα m)
          (ap fst Q'.r-braid₁) (vα' m)
          (λ i → r̂-braid₁ i .fst) (inner̂₁ m)

      split-r̂₂
        : PathP (λ m → Fam (ap-comp fst Q.r-braid₁
                              (rt₂) m)
                           (ap-comp fst Q'.r-braid₁
                              (rt₂') m))
                R₂ R₃
      split-r̂₂ m =
        comp-pathp₂-ap C.hom fst fst
          Q.r-braid₁ (rt₂)
          Q'.r-braid₁ (rt₂')
          (λ i → r̂-braid₁ i .fst) (λ i → ŵ₂ i .fst) m

      step-r̂₂ : PathP (λ m → Fam (Q.step-r₂ m) (Q'.step-r₂ m)) R₂ bot₁
      step-r̂₂ =
        comp-pathp₂ Fam
          (ap-comp fst Q.r-braid₁ (rt₂))
          (ap (ap (_⊗₀ z) (⊗₀-braid x y) ∙_) vα)
          (ap-comp fst Q'.r-braid₁ (rt₂'))
          (ap (ap (_⊗₀ z') (⊗₀-braid x' y') ∙_) vα')
          split-r̂₂ whisk-braid̂

    ⊗₁-hexagon-r
      : PathP (λ m → PathP (λ i → C.hom (Q.⊗₀-hexagon-r m i)
                                        (Q'.⊗₀-hexagon-r m i))
                     ((φ ⊗₁ ψ) ⊗₁ χ) (ψ ⊗₁ (χ ⊗₁ φ)))
              top₁ bot₁
    ⊗₁-hexagon-r =
      comp-pathp₂ Fam
        (sym (sl))
        (ap (ap fst) Q.fiber-hexagon ∙ sr)
        (sym (sl'))
        (ap (ap fst) Q'.fiber-hexagon ∙ sr')
        left̂⁻
        (comp-pathp₂ Fam
          (ap (ap fst) Q.fiber-hexagon) (sr)
          (ap (ap fst) Q'.fiber-hexagon) (sr')
          hex̂●
          (comp-pathp₂ Fam Q.step-r₁ Q.step-r₂ Q'.step-r₁ Q'.step-r₂
            step-r̂₁ step-r̂₂))
```

## The displaced hexagon-l

The slot-mirror of `hexagon-r₁`, leaf for leaf: the associator
lines run forward where `-r` had `sym`s, the one-step braid sits
at the compound pairing, the μ̂-link transports `n̂₂` with the
whisker pushed into the pairing's second slot, and the ρ̂-link
reconciles on the first.

```agda
  module hexagon-l₁ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
                    {z z'} (χ : C.hom z z')
    where

    private
      module Q  = hexagon-l₀ x  y  z
      module Q' = hexagon-l₀ x' y' z'

      Û = ⊗₁-wit-nrm φ
      V̂ = ⊗₁-wit-nrm ψ
      Ŵ = ⊗₁-wit-nrm χ

    N₁ : ⊗₁-composite (Q.H ▿₀ Q.F ▿₀ Q.G) (Q'.H ▿₀ Q'.F ▿₀ Q'.G)
    N₁ = ⊗₁-emb χ ▿₁ ⊗₁-emb φ ▿₁ ⊗₁-emb ψ

    β̂c : PathP (λ i → ⊗₁-composite (Q.βc i) (Q'.βc i))
               (⊗₁-emb φ ▿₁ ⊗₁-emb ψ ▿₁ ⊗₁-emb χ) N₁
    β̂c = ⊗₁-braid♭ (Û ●₁ V̂) Ŵ

    β̂₁ : PathP (λ i → ⊗₁-composite (Q.β₁ i) (Q'.β₁ i))
               (⊗₁-emb φ ▿₁ ⊗₁-emb ψ ▿₁ ⊗₁-emb χ)
               (⊗₁-emb φ ▿₁ ⊗₁-emb χ ▿₁ ⊗₁-emb ψ)
    β̂₁ i = ⊗₁-emb φ ▿₁ ⊗₁-braid♭ V̂ Ŵ i

    β̂₂ : PathP (λ i → ⊗₁-composite (Q.β₂ i) (Q'.β₂ i))
               (⊗₁-emb φ ▿₁ ⊗₁-emb χ ▿₁ ⊗₁-emb ψ) N₁
    β̂₂ i = ⊗₁-braid♭ Û Ŵ i ▿₁ ⊗₁-emb ψ

    n̂₁ : ⊗₁-wit Q.n₁ Q'.n₁ (⊗₁-emb φ ▿₁ ⊗₁-emb ψ ▿₁ ⊗₁-emb χ)
    n̂₁ = (Û ●₁ V̂) ●₁ Ŵ

    n̂₂ : ⊗₁-wit Q.n₂ Q'.n₂ (⊗₁-emb φ ▿₁ ⊗₁-emb ψ ▿₁ ⊗₁-emb χ)
    n̂₂ = Û ●₁ (V̂ ●₁ Ŵ)

    â₁ : ⊗₁-wit Q.a₁ Q'.a₁ N₁ ; â₁ = n̂₂ ↝̂ β̂c
    â₂ : ⊗₁-wit Q.a₂ Q'.a₂ N₁ ; â₂ = n̂₁ ↝̂ β̂c
    â₃ : ⊗₁-wit Q.a₃ Q'.a₃ N₁ ; â₃ = Ŵ ●₁ (Û ●₁ V̂)
    â₄ : ⊗₁-wit Q.a₄ Q'.a₄ N₁ ; â₄ = (Ŵ ●₁ Û) ●₁ V̂

    ĉ₁ : ⊗₁-wit Q.c₁ Q'.c₁ N₁
    ĉ₁ = (Û ●₁ ((V̂ ●₁ Ŵ) ↝̂ ⊗₁-braid♭ V̂ Ŵ)) ↝̂ β̂₂

    ĉ₅ : ⊗₁-wit Q.c₅ Q'.c₅ N₁ ; ĉ₅ = (Û ●₁ (Ŵ ●₁ V̂)) ↝̂ β̂₂
    ĉ₆ : ⊗₁-wit Q.c₆ Q'.c₆ N₁ ; ĉ₆ = ((Û ●₁ Ŵ) ●₁ V̂) ↝̂ β̂₂

    ĉ₇ : ⊗₁-wit Q.c₇ Q'.c₇ N₁
    ĉ₇ = ((Û ●₁ Ŵ) ↝̂ ⊗₁-braid♭ Û Ŵ) ●₁ V̂
```

The σ̂-lines, over exactly the sealed level-0 lines.

```agda
    ℓ̂-assoc₁ : PathP (λ i → ⊗₁-wit (Q.ℓ-assoc₁ i) (Q'.ℓ-assoc₁ i) N₁) â₁ â₂
    ℓ̂-assoc₁ i = assoc-σ●₁ Û V̂ Ŵ i ↝̂ β̂c

    ℓ̂-braid : PathP (λ i → ⊗₁-wit (Q.ℓ-braid i) (Q'.ℓ-braid i) N₁) â₂ â₃
    ℓ̂-braid = braid-σ●₁ (Û ●₁ V̂) Ŵ

    ℓ̂-assoc₂ : PathP (λ i → ⊗₁-wit (Q.ℓ-assoc₂ i) (Q'.ℓ-assoc₂ i) N₁) â₃ â₄
    ℓ̂-assoc₂ = assoc-σ●₁ Ŵ Û V̂

    r̂-braid₁ : PathP (λ i → ⊗₁-wit (Q.r-braid₁ i) (Q'.r-braid₁ i) N₁) ĉ₁ ĉ₅
    r̂-braid₁ i = (Û ●₁ braid-σ●₁ V̂ Ŵ i) ↝̂ β̂₂

    r̂-assoc : PathP (λ i → ⊗₁-wit (Q.r-assoc i) (Q'.r-assoc i) N₁) ĉ₅ ĉ₆
    r̂-assoc i = assoc-σ●₁ Û Ŵ V̂ i ↝̂ β̂₂

    r̂-braid₂ : PathP (λ i → ⊗₁-wit (Q.r-braid₂ i) (Q'.r-braid₂ i) N₁) ĉ₇ â₄
    r̂-braid₂ i = braid-σ●₁ Û Ŵ i ●₁ V̂
```

The μ̂-link, transporting `n̂₂` along the one-step braid, the
whisker pushed into the pairing's second slot.

```agda
    μ̂ : PathP (λ i → ⊗₁-wit (Q.μ i) (Q'.μ i) N₁) â₁ ĉ₁
    μ̂ i = φ ⊗₁ (ψ ⊗₁ χ) , Θ i
      where
        B₀  = ⊗₀-nrm y  ●₀ ⊗₀-nrm z
        B₀' = ⊗₀-nrm y' ●₀ ⊗₀-nrm z'
        byz  = ⊗₀-braid♭ (⊗₀-nrm y)  (⊗₀-nrm z)
        byz' = ⊗₀-braid♭ (⊗₀-nrm y') (⊗₀-nrm z')
        E  = ⊗₀-emb-comp x (y ⊗₀ z)
        E' = ⊗₀-emb-comp x' (y' ⊗₀ z')
        g  = λ X → Q.F ▿₀ X
        g' = λ X → Q'.F ▿₀ X
        H♭  = ⊗₀-hexagon-l♭ (⊗₀-nrm x)  (⊗₀-nrm y)  (⊗₀-nrm z)
        H♭' = ⊗₀-hexagon-l♭ (⊗₀-nrm x') (⊗₀-nrm y') (⊗₀-nrm z')

        inner  = ap-merge g  E  (B₀ .snd)  byz
        inner' = ap-merge g' E' (B₀' .snd) byz'

        ω : {A B : ⊗₀-composite} → ⊗₁-composite A B → ⊗₁-composite (g A) (g' B)
        ω ξ = ⊗₁-emb φ ▿₁ ξ

        Famc : ⊗₀-emb (x ⊗₀ (y ⊗₀ z)) ≡ Q.H ▿₀ Q.F ▿₀ Q.G
             → ⊗₀-emb (x' ⊗₀ (y' ⊗₀ z')) ≡ Q'.H ▿₀ Q'.F ▿₀ Q'.G
             → Type _
        Famc p p' = PathP (λ t → ⊗₁-composite (p t) (p' t))
                          (⊗₁-emb (φ ⊗₁ (ψ ⊗₁ χ))) N₁

        mid₁ : Famc (Q.n₂ .snd ∙ Q.β₁ ∙ Q.β₂) (Q'.n₂ .snd ∙ Q'.β₁ ∙ Q'.β₂)
        mid₁ =
          comp-pathp₂ ⊗₁-composite
            (Q.n₂ .snd) (Q.β₁ ∙ Q.β₂) (Q'.n₂ .snd) (Q'.β₁ ∙ Q'.β₂)
            (n̂₂ .snd)
            (comp-pathp₂ ⊗₁-composite Q.β₁ Q.β₂ Q'.β₁ Q'.β₂ β̂₁ β̂₂)

        mid₂ : Famc ((Q.n₂ .snd ∙ Q.β₁) ∙ Q.β₂) ((Q'.n₂ .snd ∙ Q'.β₁) ∙ Q'.β₂)
        mid₂ =
          comp-pathp₂ ⊗₁-composite
            (Q.n₂ .snd ∙ Q.β₁) Q.β₂ (Q'.n₂ .snd ∙ Q'.β₁) Q'.β₂
            (comp-pathp₂ ⊗₁-composite
              (Q.n₂ .snd) Q.β₁ (Q'.n₂ .snd) Q'.β₁ (n̂₂ .snd) β̂₁)
            β̂₂

        Θ-field
          : PathP (λ m → Famc (ap (Q.n₂ .snd ∙_) H♭ m)
                              (ap (Q'.n₂ .snd ∙_) H♭' m))
              (â₁ .snd) mid₁
        Θ-field m =
          comp-pathp₂ ⊗₁-composite
            (Q.n₂ .snd) (H♭ m) (Q'.n₂ .snd) (H♭' m)
            (n̂₂ .snd) (⊗₁-hexagon-l♭ Û V̂ Ŵ m)

        Θ-assoc
          : PathP (λ m → Famc (Path.assoc (Q.n₂ .snd) Q.β₁ Q.β₂ m)
                              (Path.assoc (Q'.n₂ .snd) Q'.β₁ Q'.β₂ m))
              mid₁ mid₂
        Θ-assoc =
          comp-pathp₂-assoc ⊗₁-composite (Q.n₂ .snd) Q.β₁ Q.β₂
            (Q'.n₂ .snd) Q'.β₁ Q'.β₂ (n̂₂ .snd) β̂₁ β̂₂

        Θ-merge
          : PathP (λ m → Famc (ap (_∙ Q.β₂) inner m)
                              (ap (_∙ Q'.β₂) inner' m))
              mid₂ (ĉ₁ .snd)
        Θ-merge m =
          comp-pathp₂ ⊗₁-composite (inner m) Q.β₂ (inner' m) Q'.β₂
            (comp-pathp₂-merge-map ⊗₁-composite ⊗₁-composite g g' ω
              E (B₀ .snd) byz E' (B₀' .snd) byz'
              (⊗₁-emb-comp φ (ψ ⊗₁ χ)) ((V̂ ●₁ Ŵ) .snd) (⊗₁-braid♭ V̂ Ŵ) m)
            β̂₂

        Θ : PathP (λ i → Famc (Q.μ i .snd) (Q'.μ i .snd)) (â₁ .snd) (ĉ₁ .snd)
        Θ = comp-pathp₂ Famc
              (ap (Q.n₂ .snd ∙_) H♭)
              (Path.assoc (Q.n₂ .snd) Q.β₁ Q.β₂ ∙ ap (_∙ Q.β₂) inner)
              (ap (Q'.n₂ .snd ∙_) H♭')
              (Path.assoc (Q'.n₂ .snd) Q'.β₁ Q'.β₂ ∙ ap (_∙ Q'.β₂) inner')
              Θ-field
              (comp-pathp₂ Famc
                (Path.assoc (Q.n₂ .snd) Q.β₁ Q.β₂) (ap (_∙ Q.β₂) inner)
                (Path.assoc (Q'.n₂ .snd) Q'.β₁ Q'.β₂) (ap (_∙ Q'.β₂) inner')
                Θ-assoc Θ-merge)
```

The ρ̂-link, the bare whisker-image merge on the first slot.

```agda
    ρ̂ : PathP (λ i → ⊗₁-wit (Q.ρ i) (Q'.ρ i) N₁) ĉ₆ ĉ₇
    ρ̂ i = (φ ⊗₁ χ) ⊗₁ ψ , θ̂ i
      where
        f  = λ X → X ▿₀ Q.G
        f' = λ X → X ▿₀ Q'.G

        ω : {A B : ⊗₀-composite} → ⊗₁-composite A B → ⊗₁-composite (f A) (f' B)
        ω ξ = ξ ▿₁ ⊗₁-emb ψ

        θ̂ : PathP (λ i → PathP (λ t → ⊗₁-composite (Q.ρ i .snd t)
                                                    (Q'.ρ i .snd t))
                         (⊗₁-emb ((φ ⊗₁ χ) ⊗₁ ψ)) N₁)
              (ĉ₆ .snd) (ĉ₇ .snd)
        θ̂ = comp-pathp₂-merge-map ⊗₁-composite ⊗₁-composite f f' ω
              (⊗₀-emb-comp (x ⊗₀ z) y) ((⊗₀-nrm x ●₀ ⊗₀-nrm z) .snd)
              (⊗₀-braid♭ (⊗₀-nrm x) (⊗₀-nrm z))
              (⊗₀-emb-comp (x' ⊗₀ z') y') ((⊗₀-nrm x' ●₀ ⊗₀-nrm z') .snd)
              (⊗₀-braid♭ (⊗₀-nrm x') (⊗₀-nrm z'))
              (⊗₁-emb-comp (φ ⊗₁ χ) ψ) ((Û ●₁ Ŵ) .snd) (⊗₁-braid♭ Û Ŵ)
```

The traversal glues and the fiber square.

```agda
    private
      ℓt  = Q.ℓt
      ℓt' = Q'.ℓt
      ℓc  = Q.ℓc
      ℓc' = Q'.ℓc
      rt₃  = Q.rt₃
      rt₃' = Q'.rt₃
      rt₂  = Q.rt₂
      rt₂' = Q'.rt₂
      rt₁  = Q.rt₁
      rt₁' = Q'.rt₁
      rc  = Q.rc
      rc' = Q'.rc
      sl  = Q.sl
      sl' = Q'.sl
      sr  = Q.sr
      sr' = Q'.sr

      ẑ : PathP (λ i → ⊗₁-wit ((ℓt) i)
                              ((ℓt') i) N₁)
                â₂ â₄
      ẑ = ⊗₁-wit-∙ Q.ℓ-braid Q.ℓ-assoc₂ Q'.ℓ-braid Q'.ℓ-assoc₂
            ℓ̂-braid ℓ̂-assoc₂

      ŵ₃ : PathP (λ i → ⊗₁-wit ((rt₃) i)
                               ((rt₃') i) N₁)
                 ĉ₆ â₄
      ŵ₃ = ⊗₁-wit-∙ Q.ρ Q.r-braid₂ Q'.ρ Q'.r-braid₂ ρ̂ r̂-braid₂

      ŵ₂ : PathP (λ i → ⊗₁-wit ((rt₂) i)
                               ((rt₂') i) N₁)
                 ĉ₅ â₄
      ŵ₂ = ⊗₁-wit-∙ Q.r-assoc (rt₃)
             Q'.r-assoc (rt₃') r̂-assoc ŵ₃

      ŵ₁ : PathP (λ i → ⊗₁-wit ((rt₁) i)
                               ((rt₁') i)
                               N₁)
                 ĉ₁ â₄
      ŵ₁ = ⊗₁-wit-∙ Q.r-braid₁ (rt₂)
             Q'.r-braid₁ (rt₂') r̂-braid₁ ŵ₂

    top̂ : PathP (λ i → ⊗₁-wit ((ℓc) i)
                              ((ℓc') i) N₁)
                â₁ â₄
    top̂ = ⊗₁-wit-∙ Q.ℓ-assoc₁ (ℓt)
                   Q'.ℓ-assoc₁ (ℓt')
            ℓ̂-assoc₁ ẑ

    bot̂ : PathP (λ i → ⊗₁-wit ((rc) i)
                              ((rc') i)
                              N₁)
                â₁ â₄
    bot̂ = ⊗₁-wit-∙ Q.μ (rt₁)
                   Q'.μ (rt₁')
            μ̂ ŵ₁

    wit-prop
      : (j i : Core.Base.I)
      → is-prop (⊗₁-wit (Q.fiber-hexagon j i) (Q'.fiber-hexagon j i) N₁)
    wit-prop j i =
      is-contr→is-prop
        (subst is-contr
          (λ k → ⊗₁-wit (Q.fiber-hexagon (j ∧ k) (i ∧ k))
                        (Q'.fiber-hexagon (j ∧ k) (i ∧ k)) N₁)
          (⊗₁-wit-contr â₁))

    fiber-hexagon₁
      : PathP (λ j → PathP (λ i → ⊗₁-wit (Q.fiber-hexagon j i)
                                         (Q'.fiber-hexagon j i) N₁)
                     â₁ â₄)
              top̂ bot̂
    fiber-hexagon₁ = is-prop→SquareP wit-prop top̂ refl bot̂ refl
```

## The canonical displaced hexagon-l

The tree over `⊗₀-hexagon-l`, the slot-mirror of the `-r` tree
with plain associators where `-r` had `sym`s.

```agda
    private
      Fam : x ⊗₀ (y ⊗₀ z) ≡ (z ⊗₀ x) ⊗₀ y
          → x' ⊗₀ (y' ⊗₀ z') ≡ (z' ⊗₀ x') ⊗₀ y'
          → Type h
      Fam p p' = PathP (λ i → C.hom (p i) (p' i))
                       (φ ⊗₁ (ψ ⊗₁ χ)) ((χ ⊗₁ φ) ⊗₁ ψ)

    top₁ : Fam (⊗₀-assoc x y z ∙ ⊗₀-braid (x ⊗₀ y) z ∙ ⊗₀-assoc z x y)
               (⊗₀-assoc x' y' z' ∙ ⊗₀-braid (x' ⊗₀ y') z' ∙ ⊗₀-assoc z' x' y')
    top₁ =
      comp-pathp₂ C.hom
        (⊗₀-assoc x y z)
        (⊗₀-braid (x ⊗₀ y) z ∙ ⊗₀-assoc z x y)
        (⊗₀-assoc x' y' z')
        (⊗₀-braid (x' ⊗₀ y') z' ∙ ⊗₀-assoc z' x' y')
        (⊗₁-assoc φ ψ χ)
        (comp-pathp₂ C.hom
          (⊗₀-braid (x ⊗₀ y) z) (⊗₀-assoc z x y)
          (⊗₀-braid (x' ⊗₀ y') z') (⊗₀-assoc z' x' y')
          (⊗₁-braid (φ ⊗₁ ψ) χ)
          (⊗₁-assoc χ φ ψ))

    bot₁ : Fam (ap (x ⊗₀_) (⊗₀-braid y z)
                ∙ ⊗₀-assoc x z y ∙ ap (_⊗₀ y) (⊗₀-braid x z))
               (ap (x' ⊗₀_) (⊗₀-braid y' z')
                ∙ ⊗₀-assoc x' z' y' ∙ ap (_⊗₀ y') (⊗₀-braid x' z'))
    bot₁ =
      comp-pathp₂ C.hom
        (ap (x ⊗₀_) (⊗₀-braid y z))
        (⊗₀-assoc x z y ∙ ap (_⊗₀ y) (⊗₀-braid x z))
        (ap (x' ⊗₀_) (⊗₀-braid y' z'))
        (⊗₀-assoc x' z' y' ∙ ap (_⊗₀ y') (⊗₀-braid x' z'))
        (λ i → φ ⊗₁ ⊗₁-braid ψ χ i)
        (comp-pathp₂ C.hom
          (⊗₀-assoc x z y) (ap (_⊗₀ y) (⊗₀-braid x z))
          (⊗₀-assoc x' z' y') (ap (_⊗₀ y') (⊗₀-braid x' z'))
          (⊗₁-assoc φ χ ψ)
          (λ i → ⊗₁-braid φ χ i ⊗₁ ψ))
```

The chain of edges.

```agda
    private
      E₀ : Fam (ap fst (ℓc))
               (ap fst (ℓc'))
      E₀ i = top̂ i .fst

      E₁ = comp-pathp₂ C.hom
             (ap fst Q.ℓ-assoc₁) (ap fst (ℓt))
             (ap fst Q'.ℓ-assoc₁) (ap fst (ℓt'))
             (λ i → ℓ̂-assoc₁ i .fst) (λ i → ẑ i .fst)

      E₂ = comp-pathp₂ C.hom
             (ap fst Q.ℓ-assoc₁) (ap fst Q.ℓ-braid ∙ ap fst Q.ℓ-assoc₂)
             (ap fst Q'.ℓ-assoc₁) (ap fst Q'.ℓ-braid ∙ ap fst Q'.ℓ-assoc₂)
             (λ i → ℓ̂-assoc₁ i .fst)
             (comp-pathp₂ C.hom
               (ap fst Q.ℓ-braid) (ap fst Q.ℓ-assoc₂)
               (ap fst Q'.ℓ-braid) (ap fst Q'.ℓ-assoc₂)
               (λ i → ℓ̂-braid i .fst) (λ i → ℓ̂-assoc₂ i .fst))

      R₀ : Fam (ap fst (rc))
               (ap fst (rc'))
      R₀ i = bot̂ i .fst

      R₁ = comp-pathp₂ C.hom
             (ap fst Q.μ)
             (ap fst (rt₁))
             (ap fst Q'.μ)
             (ap fst (rt₁'))
             (λ i → μ̂ i .fst) (λ i → ŵ₁ i .fst)

      R₂ : Fam (ap fst (rt₁))
               (ap fst (rt₁'))
      R₂ i = ŵ₁ i .fst

      R₃ = comp-pathp₂ C.hom
             (ap fst Q.r-braid₁) (ap fst (rt₂))
             (ap fst Q'.r-braid₁) (ap fst (rt₂'))
             (λ i → r̂-braid₁ i .fst) (λ i → ŵ₂ i .fst)
```

One displaced leaf per base leaf.

```agda
      split-l̂
        : PathP (λ m → Fam (ap-comp fst Q.ℓ-assoc₁ (ℓt) m)
                           (ap-comp fst Q'.ℓ-assoc₁ (ℓt') m))
                E₀ E₁
      split-l̂ m =
        comp-pathp₂-ap C.hom fst fst
          Q.ℓ-assoc₁ (ℓt)
          Q'.ℓ-assoc₁ (ℓt')
          (λ i → ℓ̂-assoc₁ i .fst) (λ i → ẑ i .fst) m

      whisk-l̂
        : PathP (λ m → Fam (ap (⊗₀-assoc x y z ∙_)
                              (ap-comp fst Q.ℓ-braid Q.ℓ-assoc₂) m)
                           (ap (⊗₀-assoc x' y' z' ∙_)
                              (ap-comp fst Q'.ℓ-braid Q'.ℓ-assoc₂) m))
                E₁ E₂
      whisk-l̂ m =
        comp-pathp₂ C.hom
          (ap fst Q.ℓ-assoc₁) (ap-comp fst Q.ℓ-braid Q.ℓ-assoc₂ m)
          (ap fst Q'.ℓ-assoc₁) (ap-comp fst Q'.ℓ-braid Q'.ℓ-assoc₂ m)
          (λ i → ℓ̂-assoc₁ i .fst)
          (comp-pathp₂-ap C.hom fst fst Q.ℓ-braid Q.ℓ-assoc₂
            Q'.ℓ-braid Q'.ℓ-assoc₂
            (λ i → ℓ̂-braid i .fst) (λ i → ℓ̂-assoc₂ i .fst) m)

      step-l̂₁ : PathP (λ m → Fam (Q.step-l₁ m) (Q'.step-l₁ m)) E₀ E₂
      step-l̂₁ =
        comp-pathp₂ Fam
          (ap-comp fst Q.ℓ-assoc₁ (ℓt))
          (ap (⊗₀-assoc x y z ∙_) (ap-comp fst Q.ℓ-braid Q.ℓ-assoc₂))
          (ap-comp fst Q'.ℓ-assoc₁ (ℓt'))
          (ap (⊗₀-assoc x' y' z' ∙_) (ap-comp fst Q'.ℓ-braid Q'.ℓ-assoc₂))
          split-l̂ whisk-l̂

      step-l̂₂ : PathP (λ m → Fam (Q.step-l₂ m) (Q'.step-l₂ m)) E₂ top₁
      step-l̂₂ m =
        comp-pathp₂ C.hom
          (⊗₀-assoc x y z)
          (braid●₀-nrm (⊗₀-nrm x ●₀ ⊗₀-nrm y) (⊗₀-nrm z) m
            ∙ ⊗₀-assoc z x y)
          (⊗₀-assoc x' y' z')
          (braid●₀-nrm (⊗₀-nrm x' ●₀ ⊗₀-nrm y') (⊗₀-nrm z') m
            ∙ ⊗₀-assoc z' x' y')
          (⊗₁-assoc φ ψ χ)
          (comp-pathp₂ C.hom
            (braid●₀-nrm (⊗₀-nrm x ●₀ ⊗₀-nrm y) (⊗₀-nrm z) m)
            (⊗₀-assoc z x y)
            (braid●₀-nrm (⊗₀-nrm x' ●₀ ⊗₀-nrm y') (⊗₀-nrm z') m)
            (⊗₀-assoc z' x' y')
            (braid●₁-nrm (Û ●₁ V̂) Ŵ m)
            (⊗₁-assoc χ φ ψ))

      left̂ : PathP (λ m → Fam ((sl) m)
                              ((sl') m))
                   E₀ top₁
      left̂ = comp-pathp₂ Fam Q.step-l₁ Q.step-l₂ Q'.step-l₁ Q'.step-l₂
               step-l̂₁ step-l̂₂

      left̂⁻ : PathP (λ m → Fam (sym (sl) m)
                               (sym (sl') m))
                    top₁ E₀
      left̂⁻ m = left̂ (~ m)

      hex̂● : PathP (λ m → Fam (ap (ap fst) Q.fiber-hexagon m)
                              (ap (ap fst) Q'.fiber-hexagon m))
                   E₀ R₀
      hex̂● m i = fiber-hexagon₁ m i .fst

      split-r̂
        : PathP (λ m → Fam (ap-comp fst Q.μ
                              (rt₁) m)
                           (ap-comp fst Q'.μ
                              (rt₁') m))
                R₀ R₁
      split-r̂ m =
        comp-pathp₂-ap C.hom fst fst
          Q.μ (rt₁)
          Q'.μ (rt₁')
          (λ i → μ̂ i .fst) (λ i → ŵ₁ i .fst) m

      unitl̂-r
        : PathP (λ m → Fam (Path.unitl
                              (ap fst (rt₁)) m)
                           (Path.unitl
                              (ap fst (rt₁')) m))
                R₁ R₂
      unitl̂-r m =
        comp-pathp₂-unitl C.hom
          (ap fst (rt₁))
          (ap fst (rt₁'))
          (λ i → ŵ₁ i .fst) m

      step-r̂₁ : PathP (λ m → Fam (Q.step-r₁ m) (Q'.step-r₁ m)) R₀ R₂
      step-r̂₁ =
        comp-pathp₂ Fam
          (ap-comp fst Q.μ (rt₁))
          (Path.unitl (ap fst (rt₁)))
          (ap-comp fst Q'.μ (rt₁'))
          (Path.unitl (ap fst (rt₁')))
          split-r̂ unitl̂-r

      FamI : x ⊗₀ (z ⊗₀ y) ≡ (z ⊗₀ x) ⊗₀ y
           → x' ⊗₀ (z' ⊗₀ y') ≡ (z' ⊗₀ x') ⊗₀ y'
           → Type h
      FamI p p' = PathP (λ i → C.hom (p i) (p' i))
                        (φ ⊗₁ (χ ⊗₁ ψ)) ((χ ⊗₁ φ) ⊗₁ ψ)

      FamII : (x ⊗₀ z) ⊗₀ y ≡ (z ⊗₀ x) ⊗₀ y
            → (x' ⊗₀ z') ⊗₀ y' ≡ (z' ⊗₀ x') ⊗₀ y'
            → Type h
      FamII p p' = PathP (λ i → C.hom (p i) (p' i))
                         ((φ ⊗₁ χ) ⊗₁ ψ) ((χ ⊗₁ φ) ⊗₁ ψ)

      S₀ : FamI (ap fst (rt₂))
                (ap fst (rt₂'))
      S₀ i = ŵ₂ i .fst

      S₁ = comp-pathp₂ C.hom
             (ap fst Q.r-assoc) (ap fst (rt₃))
             (ap fst Q'.r-assoc) (ap fst (rt₃'))
             (λ i → r̂-assoc i .fst) (λ i → ŵ₃ i .fst)

      S₂ = comp-pathp₂ C.hom
             (⊗₀-assoc x z y) (ap (_⊗₀ y) (⊗₀-braid x z))
             (⊗₀-assoc x' z' y') (ap (_⊗₀ y') (⊗₀-braid x' z'))
             (⊗₁-assoc φ χ ψ)
             (λ i → ⊗₁-braid φ χ i ⊗₁ ψ)

      T₀ : FamII (ap fst (rt₃)) (ap fst (rt₃'))
      T₀ i = ŵ₃ i .fst

      T₁ = comp-pathp₂ C.hom
             (ap fst Q.ρ) (ap fst Q.r-braid₂)
             (ap fst Q'.ρ) (ap fst Q'.r-braid₂)
             (λ i → ρ̂ i .fst) (λ i → r̂-braid₂ i .fst)

      T₂ : FamII (ap fst Q.r-braid₂) (ap fst Q'.r-braid₂)
      T₂ i = r̂-braid₂ i .fst

      uρ  = ap-comp fst Q.ρ Q.r-braid₂ ∙ Path.unitl (ap fst Q.r-braid₂)
      uρ' = ap-comp fst Q'.ρ Q'.r-braid₂ ∙ Path.unitl (ap fst Q'.r-braid₂)

      split-ρ̂
        : PathP (λ m → FamII (ap-comp fst Q.ρ Q.r-braid₂ m)
                             (ap-comp fst Q'.ρ Q'.r-braid₂ m))
                T₀ T₁
      split-ρ̂ m =
        comp-pathp₂-ap C.hom fst fst Q.ρ Q.r-braid₂ Q'.ρ Q'.r-braid₂
          (λ i → ρ̂ i .fst) (λ i → r̂-braid₂ i .fst) m

      unitl̂-ρ
        : PathP (λ m → FamII (Path.unitl (ap fst Q.r-braid₂) m)
                             (Path.unitl (ap fst Q'.r-braid₂) m))
                T₁ T₂
      unitl̂-ρ m =
        comp-pathp₂-unitl C.hom
          (ap fst Q.r-braid₂) (ap fst Q'.r-braid₂)
          (λ i → r̂-braid₂ i .fst) m

      inner̂₂
        : PathP (λ m → FamII (uρ m) (uρ' m)) T₀ T₂
      inner̂₂ =
        comp-pathp₂ FamII
          (ap-comp fst Q.ρ Q.r-braid₂) (Path.unitl (ap fst Q.r-braid₂))
          (ap-comp fst Q'.ρ Q'.r-braid₂) (Path.unitl (ap fst Q'.r-braid₂))
          split-ρ̂ unitl̂-ρ

      split-assoĉ
        : PathP (λ m → FamI (ap-comp fst Q.r-assoc (rt₃) m)
                            (ap-comp fst Q'.r-assoc (rt₃') m))
                S₀ S₁
      split-assoĉ m =
        comp-pathp₂-ap C.hom fst fst
          Q.r-assoc (rt₃) Q'.r-assoc (rt₃')
          (λ i → r̂-assoc i .fst) (λ i → ŵ₃ i .fst) m

      vα  = ap-comp fst Q.r-assoc (rt₃)
              ∙ ap (⊗₀-assoc x z y ∙_) uρ
      vα' = ap-comp fst Q'.r-assoc (rt₃')
              ∙ ap (⊗₀-assoc x' z' y' ∙_) uρ'

      whisk-r̂₂
        : PathP (λ m → FamI (ap (⊗₀-assoc x z y ∙_) uρ m)
                            (ap (⊗₀-assoc x' z' y' ∙_) uρ' m))
                S₁ S₂
      whisk-r̂₂ m =
        comp-pathp₂ C.hom
          (ap fst Q.r-assoc) (uρ m)
          (ap fst Q'.r-assoc) (uρ' m)
          (λ i → r̂-assoc i .fst) (inner̂₂ m)

      inner̂₁
        : PathP (λ m → FamI (vα m) (vα' m)) S₀ S₂
      inner̂₁ =
        comp-pathp₂ FamI
          (ap-comp fst Q.r-assoc (rt₃))
          (ap (⊗₀-assoc x z y ∙_) uρ)
          (ap-comp fst Q'.r-assoc (rt₃'))
          (ap (⊗₀-assoc x' z' y' ∙_) uρ')
          split-assoĉ whisk-r̂₂

      whisk-braid̂
        : PathP (λ m → Fam (ap (ap (x ⊗₀_) (⊗₀-braid y z) ∙_) vα m)
                           (ap (ap (x' ⊗₀_) (⊗₀-braid y' z') ∙_) vα' m))
                R₃ bot₁
      whisk-braid̂ m =
        comp-pathp₂ C.hom
          (ap fst Q.r-braid₁) (vα m)
          (ap fst Q'.r-braid₁) (vα' m)
          (λ i → r̂-braid₁ i .fst) (inner̂₁ m)

      split-r̂₂
        : PathP (λ m → Fam (ap-comp fst Q.r-braid₁
                              (rt₂) m)
                           (ap-comp fst Q'.r-braid₁
                              (rt₂') m))
                R₂ R₃
      split-r̂₂ m =
        comp-pathp₂-ap C.hom fst fst
          Q.r-braid₁ (rt₂)
          Q'.r-braid₁ (rt₂')
          (λ i → r̂-braid₁ i .fst) (λ i → ŵ₂ i .fst) m

      step-r̂₂ : PathP (λ m → Fam (Q.step-r₂ m) (Q'.step-r₂ m)) R₂ bot₁
      step-r̂₂ =
        comp-pathp₂ Fam
          (ap-comp fst Q.r-braid₁ (rt₂))
          (ap (ap (x ⊗₀_) (⊗₀-braid y z) ∙_) vα)
          (ap-comp fst Q'.r-braid₁ (rt₂'))
          (ap (ap (x' ⊗₀_) (⊗₀-braid y' z') ∙_) vα')
          split-r̂₂ whisk-braid̂

    ⊗₁-hexagon-l
      : PathP (λ m → PathP (λ i → C.hom (Q.⊗₀-hexagon-l m i)
                                        (Q'.⊗₀-hexagon-l m i))
                     (φ ⊗₁ (ψ ⊗₁ χ)) ((χ ⊗₁ φ) ⊗₁ ψ))
              top₁ bot₁
    ⊗₁-hexagon-l =
      comp-pathp₂ Fam
        (sym (sl))
        (ap (ap fst) Q.fiber-hexagon ∙ sr)
        (sym (sl'))
        (ap (ap fst) Q'.fiber-hexagon ∙ sr')
        left̂⁻
        (comp-pathp₂ Fam
          (ap (ap fst) Q.fiber-hexagon) (sr)
          (ap (ap fst) Q'.fiber-hexagon) (sr')
          hex̂●
          (comp-pathp₂ Fam Q.step-r₁ Q.step-r₂ Q'.step-r₁ Q'.step-r₂
            step-r̂₁ step-r̂₂))
```
