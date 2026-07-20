Lane Biocini
July 2026

2-coherence of the tensor: the transcription of `Cat.Coherence`
under the dictionary hom ↦ ob, graded like the rest of the
monoidal spine. `is-monoidal-2-coherent` is the extension record
over the full `monoidal` bundle, carrying the coherence law at
both grades. `coherence` carries the derived theory: the
interchange coherence, the object-level pentagon, and the
triangle, all read off the propositional representability
fibers — the pentagon is one `is-contr→is-set` away from
`⊗₀-nrm`-strictness, and the triangle consumes the object-level
coherence field to close its loop, exactly as at the hom level.
The displaced level-1 pentagon and triangle follow the same
spine.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Coherence where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp; comp-pathp₂-ap)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (is-prop→SquareP)
open import Core.Transport.J using (subst)

open import Cat.Type
open import Cat.Base
open import Cat.Monoidal
open import Cat.Monoidal.Bifunctor
```

## 2-coherence

The coherence law identifying the two middle-unit absorptions
of a two-step composite, at both grades: the object level as in
`Cat.Coherence`'s `is-2-coherent`, and the morphism level
displaced over it — a square of hom-composites over the
object-level identification, relating the `▿₁`-whiskers of
`▾₁-idn` and `⊗₁-emb-idn-absorb`. The two levels are proved
separately by any instance, but they travel in one record over
the `monoidal` bundle: a consumer of `monoidal C` answers for
both.

```agda
record is-monoidal-2-coherent {o h} {C : category o h}
  (M : monoidal C) : Type (o ⊔ h) where
  open monoidal M
  open theory₁ M
  private module C = category C

  field
    is-coh₀
      : (x y : C.ob)
      → ap (_▿₀ ⊗₀-emb y) (▾₀-idn (⊗₀-emb x))
      ≡ ap (⊗₀-emb x ▿₀_) (⊗₀-emb-idn-absorb y)

    is-coh₁
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → PathP (λ j → PathP (λ i → ⊗₁-composite
                                    (is-coh₀ x y j i)
                                    (is-coh₀ x' y' j i))
                     ((⊗₁-emb φ ▾₁ C.idn I) ▿₁ ⊗₁-emb ψ)
                     (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
              (λ i → ▾₁-idn (⊗₁-emb φ) i ▿₁ ⊗₁-emb ψ)
              (λ i → ⊗₁-emb φ ▿₁ ⊗₁-emb-idn-absorb ψ i)
```

## The derived theory

```agda
module coherence {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  open theory₁ M
  private module C = category C
```

## Interchange coherence

The two witness pairings agree over the interchange: the fibers
are propositional, so the `●₀`/`○₀` images of the same pair are
joined by a `PathP` over `⊗₀-interchange♭`, and naturality of the
interchange in its first pair is the `Path.commutes` reading of
that square.

```agda
  ●₀-coh
    : ∀ {F G : ⊗₀-composite}
      (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
    → PathP (λ i → is-⊗₀-representable (⊗₀-interchange♭ U V i))
            (U ●₀ V) (U ○₀ V)
  ●₀-coh U V =
    is-prop→PathP
      (λ i → is-⊗₀-representable-prop (⊗₀-interchange♭ U V i))
      (U ●₀ V) (U ○₀ V)

  ⊗₀-interchange-natural
    : ∀ {F G H : ⊗₀-composite}
      (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
      (W : is-⊗₀-representable H)
    → ap (λ X → X ▿₀ H) (⊗₀-interchange♭ U V) ∙ ⊗₀-interchange♭ (U ○₀ V) W
    ≡ ⊗₀-interchange♭ (U ●₀ V) W ∙ ap (λ X → X ▵₀ H) (⊗₀-interchange♭ U V)
  ⊗₀-interchange-natural {H = H} U V W =
    Path.commutes
      (ap (λ X → X ▿₀ H) (⊗₀-interchange♭ U V)) (⊗₀-interchange♭ (U ○₀ V) W)
      (⊗₀-interchange♭ (U ●₀ V) W) (ap (λ X → X ▵₀ H) (⊗₀-interchange♭ U V))
      (λ j i → ⊗₀-interchange♭ (●₀-coh U V i) W j)
```

## The pentagon

The fully nested composite is strictly bracketing-free, so the
five bracketings of a fourfold `●₀` inhabit one propositional
fiber; the fiber pentagon is a set-level identification of edge
composites, and the object pentagon is its `ap fst` image,
straightened to `⊗₀-assoc` endpoints by `assoc●₀-nrm`.

```agda
  module pentagon●₀ {F G H K : ⊗₀-composite}
    (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
    (W : is-⊗₀-representable H) (X : is-⊗₀-representable K)
    where

    T : ⊗₀-composite
    T = F ▿₀ G ▿₀ H ▿₀ K

    p₁ p₂ p₃ p₄ p₅ : is-⊗₀-representable T
    p₁ = ((U ●₀ V) ●₀ W) ●₀ X
    p₂ = (U ●₀ (V ●₀ W)) ●₀ X
    p₃ = U ●₀ ((V ●₀ W) ●₀ X)
    p₄ = (U ●₀ V) ●₀ (W ●₀ X)
    p₅ = U ●₀ (V ●₀ (W ●₀ X))

    T-contr : is-contr (is-⊗₀-representable T)
    T-contr .center = p₁
    T-contr .paths  = is-⊗₀-representable-prop T p₁

    σ₂₁ : p₂ ≡ p₁ ; σ₂₁ i = assoc-σ●₀ U V W i ●₀ X
    σ₃₂ : p₃ ≡ p₂ ; σ₃₂   = assoc-σ●₀ U (V ●₀ W) X
    σ₅₃ : p₅ ≡ p₃ ; σ₅₃ i = U ●₀ assoc-σ●₀ V W X i
    σ₄₁ : p₄ ≡ p₁ ; σ₄₁   = assoc-σ●₀ (U ●₀ V) W X
    σ₅₄ : p₅ ≡ p₄ ; σ₅₄   = assoc-σ●₀ U V (W ●₀ X)

    -- opaque like assoc-σ●₀: level-1 families project its slices
    -- at generic interval points, and the sealed head keeps those
    -- comparisons syntactic; the boundary still reduces by the
    -- type-directed rule
    opaque
      fiber-pentagon : σ₅₃ ∙ σ₃₂ ∙ σ₂₁ ≡ σ₅₄ ∙ σ₄₁
      fiber-pentagon =
        is-contr→is-set T-contr p₅ p₁ (σ₅₃ ∙ σ₃₂ ∙ σ₂₁) (σ₅₄ ∙ σ₄₁)

    -- the ∙-tree of the fiber pentagon's hom shadow, leaf by leaf:
    -- two ap-comp shuffles into the shadow, the shadow itself, one
    -- shuffle out — named so the displaced pentagon can glue over
    -- each leaf separately
    step₁ = sym (ap (ap fst σ₅₃ ∙_) (ap-comp fst σ₃₂ σ₂₁))
    step₂ = sym (ap-comp fst σ₅₃ (σ₃₂ ∙ σ₂₁))
    step₃ = ap (ap fst) fiber-pentagon
    step₄ = ap-comp fst σ₅₄ σ₄₁

    pentagon●₀
      : ap (U .fst ⊗₀_) (assoc●₀ V W X)
        ∙ assoc●₀ U (V ●₀ W) X
        ∙ ap (_⊗₀ X .fst) (assoc●₀ U V W)
      ≡ assoc●₀ U V (W ●₀ X) ∙ assoc●₀ (U ●₀ V) W X
    pentagon●₀ = step₁ ∙ step₂ ∙ step₃ ∙ step₄

  -- a witness slid back along its own path: at m = i0 the slide is
  -- the witness itself (path eta), at m = i1 the normal form (the
  -- witness path's typed boundary) — both definitional, so any
  -- calculus projection applied along the slide is a nrm-
  -- straightening square with strict endpoints, and its displaced
  -- mate is the same slide one level up
  nrm-slide₀
    : ∀ {F : ⊗₀-composite} (U : is-⊗₀-representable F)
      (m : Core.Base.I)
    → is-⊗₀-representable (U .snd (~ m))
  nrm-slide₀ U m = U .fst , λ k → U .snd (k ∧ ~ m)

  nrm-slide₁
    : ∀ {F F' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {η : ⊗₁-composite F F'}
      (Û : ⊗₁-wit U U' η) (m : Core.Base.I)
    → ⊗₁-wit (nrm-slide₀ U m) (nrm-slide₀ U' m) (Û .snd (~ m))
  nrm-slide₁ Û m = Û .fst , λ k → Û .snd (k ∧ ~ m)

  assoc●₀-nrm
    : ∀ {F G H : ⊗₀-composite}
      (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
      (W : is-⊗₀-representable H)
    → assoc●₀ U V W ≡ ⊗₀-assoc (U .fst) (V .fst) (W .fst)
  assoc●₀-nrm U V W m =
    assoc●₀ (nrm-slide₀ U m) (nrm-slide₀ V m) (nrm-slide₀ W m)

  assoc●₁-nrm
    : ∀ {F F' G G' H H' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
        {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
        {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
        {θ : ⊗₁-composite H H'}
      (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
    → PathP (λ m → PathP (λ i → C.hom (assoc●₀-nrm U V W m i)
                                      (assoc●₀-nrm U' V' W' m i))
                   (Û .fst ⊗₁ (V̂ .fst ⊗₁ Ŵ .fst))
                   ((Û .fst ⊗₁ V̂ .fst) ⊗₁ Ŵ .fst))
            (assoc●₁ Û V̂ Ŵ) (⊗₁-assoc (Û .fst) (V̂ .fst) (Ŵ .fst))
  assoc●₁-nrm Û V̂ Ŵ m =
    assoc●₁ (nrm-slide₁ Û m) (nrm-slide₁ V̂ m) (nrm-slide₁ Ŵ m)

  module pentagon₀ (x y z w : C.ob) where
    open pentagon●₀ (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z) (⊗₀-nrm w) public

    A₁ = assoc●₀-nrm (⊗₀-nrm x ●₀ ⊗₀-nrm y) (⊗₀-nrm z) (⊗₀-nrm w)
    A₂ = assoc●₀-nrm (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z ●₀ ⊗₀-nrm w)
    A₃ = assoc●₀-nrm (⊗₀-nrm x) (⊗₀-nrm y ●₀ ⊗₀-nrm z) (⊗₀-nrm w)

    whisker₃ = ap (λ t → ap (x ⊗₀_) (⊗₀-assoc y z w)
                         ∙ (t ∙ ap (_⊗₀ w) (⊗₀-assoc x y z))) (sym A₃)
    whisker₂ = ap (λ t → t ∙ assoc●₀ (⊗₀-nrm x ●₀ ⊗₀-nrm y)
                                     (⊗₀-nrm z) (⊗₀-nrm w)) A₂
    whisker₁ = ap (⊗₀-assoc x y (z ⊗₀ w) ∙_) A₁

    ⊗₀-pentagon
      : ap (x ⊗₀_) (⊗₀-assoc y z w)
        ∙ ⊗₀-assoc x (y ⊗₀ z) w
        ∙ ap (_⊗₀ w) (⊗₀-assoc x y z)
      ≡ ⊗₀-assoc x y (z ⊗₀ w) ∙ ⊗₀-assoc (x ⊗₀ y) z w
    ⊗₀-pentagon = whisker₃ ∙ pentagon●₀ ∙ whisker₂ ∙ whisker₁
```

## The triangle

The unit composite `A ▿₀ B` carries the plain pairing `s₀` and
the two unitor-bearing pairings `sl`/`sr` — the `●₀`-whiskers of
the transported one-sided witnesses `Vg`/`Uf` — and every face of
the triangle is the `fst`-shadow of a propositional witness
square with wit-calculus edges. The unitor faces are squares in
the one fiber, sides constant; the associator face rides the
coherence field itself — its base square is `is-coh₀` transposed,
its sides the `ρ`-lines: `↝-fill` slides of the unit absorptions,
`●₀`-whiskered, connecting the bracketings `r₁`/`r₂` to `sl`/`sr`
with constant `fst`. The fiber triangle is one `is-contr→is-set`,
and the tree glues shadow-by-shadow exactly as the pentagon's, so
every leaf displaces by construction.

```agda
  module triangle₀ (x y : C.ob) where
    A = ⊗₀-emb x
    E = ⊗₀-emb I
    B = ⊗₀-emb y

    -- 1 = source of ⊗₀-assoc (right-nested), 2 = target (left-nested)
    e₁ : A ▿₀ (E ▿₀ B) ≡ A ▿₀ B ;  e₁ = ap (A ▿₀_) (⊗₀-emb-idn-absorb y)
    e₂ : (A ▿₀ E) ▿₀ B ≡ A ▿₀ B ;  e₂ = ap (_▿₀ B) (▾₀-idn A)

    r₁ r₂ r₀¹ r₀² : is-⊗₀-representable (A ▿₀ E ▿₀ B)
    r₁  = ⊗₀-nrm x ●₀ (⊗₀-nrm I ●₀ ⊗₀-nrm y)     -- fst = x ⊗₀ (I ⊗₀ y)
    r₂  = (⊗₀-nrm x ●₀ ⊗₀-nrm I) ●₀ ⊗₀-nrm y     -- fst = (x ⊗₀ I) ⊗₀ y
    r₀¹ = (⊗₀-nrm x ●₀ ⊗₀-nrm y) ↝ sym e₁
    r₀² = (⊗₀-nrm x ●₀ ⊗₀-nrm y) ↝ sym e₂

    T-contr : is-contr (is-⊗₀-representable (A ▿₀ E ▿₀ B))
    T-contr .center = r₁
    T-contr .paths  = is-⊗₀-representable-prop _ r₁

    -- the loop σ-line, sealed like the unitor σ-lines: the loop is
    -- its fst-shadow, and the fiber square behind loop-refl gets
    -- sealed faces — families over that square never expose the
    -- propositionality body
    opaque
      σ-loop : r₀¹ ≡ r₀²
      σ-loop = is-⊗₀-representable-prop _ r₀¹ r₀²

    loop : x ⊗₀ y ≡ x ⊗₀ y
    loop = ap fst σ-loop

    Uf : is-⊗₀-representable A ; Uf = (⊗₀-nrm x ●₀ ⊗₀-nrm I) ↝ ▾₀-idn A
    Vg : is-⊗₀-representable B ; Vg = (⊗₀-nrm I ●₀ ⊗₀-nrm y) ↝ ⊗₀-emb-idn-absorb y

    s₀ sl sr : is-⊗₀-representable (A ▿₀ B)
    s₀ = ⊗₀-nrm x ●₀ ⊗₀-nrm y
    sl = ⊗₀-nrm x ●₀ Vg          -- fst = x ⊗₀ (I ⊗₀ y)
    sr = Uf ●₀ ⊗₀-nrm y          -- fst = (x ⊗₀ I) ⊗₀ y

    -- opaque like assoc-σ●₀: the tree and the level-1 witness
    -- families only ever read their boundaries off the types, and
    -- the sealed heads keep the fiber comparisons syntactic; the
    -- displaced mates are ⊗₁-wit-σ[_,_] instances at these sealed
    -- lines, no unfolding
    opaque
      σₗᵣ : sl ≡ sr ; σₗᵣ = is-⊗₀-representable-prop _ sl sr
      σᵣ₀ : sr ≡ s₀ ; σᵣ₀ = is-⊗₀-representable-prop _ sr s₀
      σₗ₀ : sl ≡ s₀ ; σₗ₀ = is-⊗₀-representable-prop _ sl s₀

    -- fst-constant lines from the bracketings to the pairings,
    -- riding e₂/e₁: the ↝-fill slides of the two unit absorptions,
    -- ●₀-whiskered on the untouched side
    ρr : (m : Core.Base.I) → is-⊗₀-representable (e₂ m)
    ρr m = ↝-fill (⊗₀-nrm x ●₀ ⊗₀-nrm I) (▾₀-idn A) m ●₀ ⊗₀-nrm y

    ρl : (m : Core.Base.I) → is-⊗₀-representable (e₁ m)
    ρl m = ⊗₀-nrm x ●₀ ↝-fill (⊗₀-nrm I ●₀ ⊗₀-nrm y) (⊗₀-emb-idn-absorb y) m

    -- the unitor faces: squares in the one fiber, sides constant,
    -- bottom the ●₀-whisker of the unitor σ-line — the shadow's
    -- bottom edge is the whiskered unitor definitionally. Opaque
    -- like fiber-pentagon: level-1 witness families project their
    -- slices under generic interval binders, and the sealed heads
    -- keep those comparisons syntactic; the boundary still reduces
    -- by the type-directed rule
    opaque
      face-σr : SquareP (λ _ _ → is-⊗₀-representable (A ▿₀ B))
                σᵣ₀ refl (λ i → unitr-σ●₀ x i ●₀ ⊗₀-nrm y) refl
      face-σr = is-prop→SquareP (λ _ _ → is-⊗₀-representable-prop (A ▿₀ B))
                  σᵣ₀ refl (λ i → unitr-σ●₀ x i ●₀ ⊗₀-nrm y) refl

      face-σl : SquareP (λ _ _ → is-⊗₀-representable (A ▿₀ B))
                σₗ₀ refl (λ i → ⊗₀-nrm x ●₀ unitl-σ●₀ y i) refl
      face-σl = is-prop→SquareP (λ _ _ → is-⊗₀-representable-prop (A ▿₀ B))
                  σₗ₀ refl (λ i → ⊗₀-nrm x ●₀ unitl-σ●₀ y i) refl

    face-r : ap fst σᵣ₀ ≡ ap (_⊗₀ y) (⊗₀-unitr x)
    face-r m i = face-σr m i .fst

    face-l : ap fst σₗ₀ ≡ ap (x ⊗₀_) (⊗₀-unitl y)
    face-l m i = face-σl m i .fst

    -- the associator face: the witness square over the transposed
    -- coherence field, sides the ρ-lines, bottom the sealed
    -- assoc-σ●₀ — its shadow lands on ⊗₀-assoc with no unfolding
    opaque
      face-σa
        : (mid : is-monoidal-2-coherent M)
        → SquareP (λ m i → is-⊗₀-representable
                             (mid .is-monoidal-2-coherent.is-coh₀ x y (~ i) (~ m)))
          σₗᵣ (λ m → ρl (~ m))
          (assoc-σ●₀ (⊗₀-nrm x) (⊗₀-nrm I) (⊗₀-nrm y))
          (λ m → ρr (~ m))
      face-σa mid =
        is-prop→SquareP
          (λ m i → is-⊗₀-representable-prop
                     (mid .is-monoidal-2-coherent.is-coh₀ x y (~ i) (~ m)))
          σₗᵣ (λ m → ρl (~ m))
          (assoc-σ●₀ (⊗₀-nrm x) (⊗₀-nrm I) (⊗₀-nrm y))
          (λ m → ρr (~ m))

    face-a : is-monoidal-2-coherent M → ap fst σₗᵣ ≡ ⊗₀-assoc x I y
    face-a mid m i = face-σa mid m i .fst

    -- opaque like fiber-pentagon: level-1 witness families project
    -- its slices under generic interval binders; the boundary still
    -- reduces by the type-directed rule
    opaque
      fiber-triangle : σₗᵣ ∙ σᵣ₀ ≡ σₗ₀
      fiber-triangle = is-contr→is-set (⊗₀-rep-contr s₀) sl s₀ (σₗᵣ ∙ σᵣ₀) σₗ₀

    -- the ∙-tree of the triangle, leaf by leaf: the associator and
    -- unitr whiskers into the fiber, one ap-comp shuffle, the fiber
    -- triangle's shadow, the unitl face out
    step₁ = sym (ap-comp fst σₗᵣ σᵣ₀)
    step₂ = ap (ap fst) fiber-triangle
    whisker-r = ap (ap fst σₗᵣ ∙_) (sym face-r)

    whisker-a
      : (mid : is-monoidal-2-coherent M)
      → ⊗₀-assoc x I y ∙ ap (_⊗₀ y) (⊗₀-unitr x)
      ≡ ap fst σₗᵣ ∙ ap (_⊗₀ y) (⊗₀-unitr x)
    whisker-a mid = ap (_∙ ap (_⊗₀ y) (⊗₀-unitr x)) (sym (face-a mid))

    triangle-weak
      : ap fst σₗᵣ ∙ ap (_⊗₀ y) (⊗₀-unitr x)
      ≡ ap (x ⊗₀_) (⊗₀-unitl y)
    triangle-weak = whisker-r ∙ step₁ ∙ step₂ ∙ face-l

    ⊗₀-triangle
      : is-monoidal-2-coherent M
      → ⊗₀-assoc x I y ∙ ap (_⊗₀ y) (⊗₀-unitr x) ≡ ap (x ⊗₀_) (⊗₀-unitl y)
    ⊗₀-triangle mid = whisker-a mid ∙ triangle-weak

    -- the fiber square behind the loop: the σ-line against the
    -- is-coh₀-transport line. Opaque like fiber-pentagon: level-1
    -- witness families project its slices under generic interval
    -- binders; the boundary still reduces by the type-directed rule
    opaque
      loop-sq
        : (mid : is-monoidal-2-coherent M)
        → σ-loop
        ≡ ap ((⊗₀-nrm x ●₀ ⊗₀-nrm y) ↝_)
             (ap sym (sym (mid .is-monoidal-2-coherent.is-coh₀ x y)))
      loop-sq mid =
        is-contr→is-set T-contr r₀¹ r₀² σ-loop
          (ap ((⊗₀-nrm x ●₀ ⊗₀-nrm y) ↝_)
              (ap sym (sym (mid .is-monoidal-2-coherent.is-coh₀ x y))))

    loop-refl : is-monoidal-2-coherent M → loop ≡ refl
    loop-refl mid = ap (ap fst) (loop-sq mid)
```

## The displaced pentagon

The level-1 pentagon in `●`-form: the five bracketings of a
fourfold `●₁` displace the level-0 witnesses `p₁`–`p₅`, the five
edges displace the `σ`s — `assoc-σ●₁` lines, `●₁`-whiskered on
the same side as at level 0 — and the square between the glued
edge composites fills by `is-prop→SquareP`: the displaced
witness spaces are contractible pointwise over the whole of
`fiber-pentagon`, one transported `⊗₁-wit-contr` per point.

The hom shadow projects through `fst`. Because the edges are
glued by `⊗₁-wit-∙`, their hom components are the `comp-pathp₂`
composites of the whiskered `assoc●₁` lines by construction, so
`pentagon●₁` is a genuine identification of associator
composites over the fiber square's shadow, the displaced image
of `pentagon●₀`'s core.

```agda
  module pentagon●₁ {F F' G G' H H' K K' : ⊗₀-composite}
    {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
    {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
    {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
    {X : is-⊗₀-representable K} {X' : is-⊗₀-representable K'}
    {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
    {θ : ⊗₁-composite H H'} {κ : ⊗₁-composite K K'}
    (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ)
    (Ŵ : ⊗₁-wit W W' θ) (X̂ : ⊗₁-wit X X' κ)
    where

    private
      module P  = pentagon●₀ U V W X
      module P' = pentagon●₀ U' V' W' X'

    -- the homs the witnesses represent
    φ = Û .fst ; ψ = V̂ .fst ; χ = Ŵ .fst ; ω = X̂ .fst

    N₁ : ⊗₁-composite P.T P'.T
    N₁ = η ▿₁ ζ ▿₁ θ ▿₁ κ

    p̂₁ : ⊗₁-wit P.p₁ P'.p₁ N₁ ; p̂₁ = ((Û ●₁ V̂) ●₁ Ŵ) ●₁ X̂
    p̂₂ : ⊗₁-wit P.p₂ P'.p₂ N₁ ; p̂₂ = (Û ●₁ (V̂ ●₁ Ŵ)) ●₁ X̂
    p̂₃ : ⊗₁-wit P.p₃ P'.p₃ N₁ ; p̂₃ = Û ●₁ ((V̂ ●₁ Ŵ) ●₁ X̂)
    p̂₄ : ⊗₁-wit P.p₄ P'.p₄ N₁ ; p̂₄ = (Û ●₁ V̂) ●₁ (Ŵ ●₁ X̂)
    p̂₅ : ⊗₁-wit P.p₅ P'.p₅ N₁ ; p̂₅ = Û ●₁ (V̂ ●₁ (Ŵ ●₁ X̂))

    σ̂₂₁ : PathP (λ i → ⊗₁-wit (P.σ₂₁ i) (P'.σ₂₁ i) N₁) p̂₂ p̂₁
    σ̂₂₁ i = assoc-σ●₁ Û V̂ Ŵ i ●₁ X̂

    σ̂₃₂ : PathP (λ i → ⊗₁-wit (P.σ₃₂ i) (P'.σ₃₂ i) N₁) p̂₃ p̂₂
    σ̂₃₂ = assoc-σ●₁ Û (V̂ ●₁ Ŵ) X̂

    σ̂₅₃ : PathP (λ i → ⊗₁-wit (P.σ₅₃ i) (P'.σ₅₃ i) N₁) p̂₅ p̂₃
    σ̂₅₃ i = Û ●₁ assoc-σ●₁ V̂ Ŵ X̂ i

    σ̂₄₁ : PathP (λ i → ⊗₁-wit (P.σ₄₁ i) (P'.σ₄₁ i) N₁) p̂₄ p̂₁
    σ̂₄₁ = assoc-σ●₁ (Û ●₁ V̂) Ŵ X̂

    σ̂₅₄ : PathP (λ i → ⊗₁-wit (P.σ₅₄ i) (P'.σ₅₄ i) N₁) p̂₅ p̂₄
    σ̂₅₄ = assoc-σ●₁ Û V̂ (Ŵ ●₁ X̂)

    top̂ : PathP (λ i → ⊗₁-wit ((P.σ₅₃ ∙ P.σ₃₂ ∙ P.σ₂₁) i)
                              ((P'.σ₅₃ ∙ P'.σ₃₂ ∙ P'.σ₂₁) i) N₁)
                p̂₅ p̂₁
    top̂ = ⊗₁-wit-∙ P.σ₅₃ (P.σ₃₂ ∙ P.σ₂₁) P'.σ₅₃ (P'.σ₃₂ ∙ P'.σ₂₁)
            σ̂₅₃ (⊗₁-wit-∙ P.σ₃₂ P.σ₂₁ P'.σ₃₂ P'.σ₂₁ σ̂₃₂ σ̂₂₁)

    bot̂ : PathP (λ i → ⊗₁-wit ((P.σ₅₄ ∙ P.σ₄₁) i) ((P'.σ₅₄ ∙ P'.σ₄₁) i) N₁)
                p̂₅ p̂₁
    bot̂ = ⊗₁-wit-∙ P.σ₅₄ P.σ₄₁ P'.σ₅₄ P'.σ₄₁ σ̂₅₄ σ̂₄₁

    wit-prop
      : (j i : Core.Base.I)
      → is-prop (⊗₁-wit (P.fiber-pentagon j i) (P'.fiber-pentagon j i) N₁)
    wit-prop j i =
      is-contr→is-prop
        (subst is-contr
          (λ k → ⊗₁-wit (P.fiber-pentagon (j ∧ k) (i ∧ k))
                        (P'.fiber-pentagon (j ∧ k) (i ∧ k)) N₁)
          (⊗₁-wit-contr p̂₅))

    fiber-pentagon₁
      : PathP (λ j → PathP (λ i → ⊗₁-wit (P.fiber-pentagon j i)
                                         (P'.fiber-pentagon j i) N₁)
                     p̂₅ p̂₁)
              top̂ bot̂
    fiber-pentagon₁ = is-prop→SquareP wit-prop top̂ refl bot̂ refl

    pentagon●₁
      : PathP (λ j → PathP (λ i → C.hom (P.fiber-pentagon j i .fst)
                                        (P'.fiber-pentagon j i .fst))
                     (φ ⊗₁ (ψ ⊗₁ (χ ⊗₁ ω)))
                     (((φ ⊗₁ ψ) ⊗₁ χ) ⊗₁ ω))
              (λ i → top̂ i .fst) (λ i → bot̂ i .fst)
    pentagon●₁ j i = fiber-pentagon₁ j i .fst
```

## The canonical displaced pentagon

The pentagon over `⊗₀-pentagon` itself: a square of hom-lines
whose edges are the `comp-pathp₂`-composites of the whiskered
`⊗₁-assoc` lines. `⊗₀-pentagon` is a `∙`-tree, and every leaf
displaces by construction: the `A`-whiskers are `assoc●₁-nrm`
slides over their level-0 mates, the `ap-comp` shuffles are
`comp-pathp₂-ap` squares — the hom component of a `⊗₁-wit-∙`
glue *is* the `comp-pathp₂` at the reindexed witness family, so
the shuffle square's two ends are the two readings of the same
composite — and the core leaf is `pentagon●₁`. `comp-pathp₂` at
the family of pentagon fillers glues the displaced leaves along
exactly the base tree, so every interface between consecutive
leaves is definitional.

```agda
  module pentagon₁ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
                   {z z'} (χ : C.hom z z') {w w'} (ω : C.hom w w')
    where

    private
      module Q  = pentagon₀ x y z w
      module Q' = pentagon₀ x' y' z' w'
      module P₁ = pentagon●₁ (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ)
                             (⊗₁-wit-nrm χ) (⊗₁-wit-nrm ω)

      Fam : (x ⊗₀ y ⊗₀ z ⊗₀ w ≡ ((x ⊗₀ y) ⊗₀ z) ⊗₀ w)
          → (x' ⊗₀ y' ⊗₀ z' ⊗₀ w' ≡ ((x' ⊗₀ y') ⊗₀ z') ⊗₀ w')
          → Type h
      Fam p p' = PathP (λ i → C.hom (p i) (p' i))
                       (φ ⊗₁ ψ ⊗₁ χ ⊗₁ ω) (((φ ⊗₁ ψ) ⊗₁ χ) ⊗₁ ω)

      -- the displaced A-whiskers: assoc●₁-nrm at the same
      -- compound witnesses A₁–A₃ straighten
      Â₁ = assoc●₁-nrm (⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm ψ)
                       (⊗₁-wit-nrm χ) (⊗₁-wit-nrm ω)
      Â₂ = assoc●₁-nrm (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ)
                       (⊗₁-wit-nrm χ ●₁ ⊗₁-wit-nrm ω)
      Â₃ = assoc●₁-nrm (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ ●₁ ⊗₁-wit-nrm χ)
                       (⊗₁-wit-nrm ω)

      -- the inner witness glue of top̂, shared by both shuffle legs
      ẑ = ⊗₁-wit-∙ Q.σ₃₂ Q.σ₂₁ Q'.σ₃₂ Q'.σ₂₁ P₁.σ̂₃₂ P₁.σ̂₂₁
```

The chain of edges: the stated top edge, the σ-projection
composites in their three degrees of splitting, the hom shadows
of `top̂`/`bot̂`, the half-straightened composites, and the stated
bottom edge.

```agda
    top₁ : Fam (ap (x ⊗₀_) (⊗₀-assoc y z w)
                ∙ ⊗₀-assoc x (y ⊗₀ z) w ∙ ap (_⊗₀ w) (⊗₀-assoc x y z))
               (ap (x' ⊗₀_) (⊗₀-assoc y' z' w')
                ∙ ⊗₀-assoc x' (y' ⊗₀ z') w' ∙ ap (_⊗₀ w') (⊗₀-assoc x' y' z'))
    top₁ =
      comp-pathp₂ C.hom
        (ap (x ⊗₀_) (⊗₀-assoc y z w))
        (⊗₀-assoc x (y ⊗₀ z) w ∙ ap (_⊗₀ w) (⊗₀-assoc x y z))
        (ap (x' ⊗₀_) (⊗₀-assoc y' z' w'))
        (⊗₀-assoc x' (y' ⊗₀ z') w' ∙ ap (_⊗₀ w') (⊗₀-assoc x' y' z'))
        (λ i → φ ⊗₁ ⊗₁-assoc ψ χ ω i)
        (comp-pathp₂ C.hom
          (⊗₀-assoc x (y ⊗₀ z) w) (ap (_⊗₀ w) (⊗₀-assoc x y z))
          (⊗₀-assoc x' (y' ⊗₀ z') w') (ap (_⊗₀ w') (⊗₀-assoc x' y' z'))
          (⊗₁-assoc φ (ψ ⊗₁ χ) ω)
          (λ i → ⊗₁-assoc φ ψ χ i ⊗₁ ω))

    bot₁ : Fam (⊗₀-assoc x y (z ⊗₀ w) ∙ ⊗₀-assoc (x ⊗₀ y) z w)
               (⊗₀-assoc x' y' (z' ⊗₀ w') ∙ ⊗₀-assoc (x' ⊗₀ y') z' w')
    bot₁ =
      comp-pathp₂ C.hom
        (⊗₀-assoc x y (z ⊗₀ w)) (⊗₀-assoc (x ⊗₀ y) z w)
        (⊗₀-assoc x' y' (z' ⊗₀ w')) (⊗₀-assoc (x' ⊗₀ y') z' w')
        (⊗₁-assoc φ ψ (χ ⊗₁ ω)) (⊗₁-assoc (φ ⊗₁ ψ) χ ω)

    private
      E₁ = comp-pathp₂ C.hom
             (ap fst Q.σ₅₃) (ap fst Q.σ₃₂ ∙ ap fst Q.σ₂₁)
             (ap fst Q'.σ₅₃) (ap fst Q'.σ₃₂ ∙ ap fst Q'.σ₂₁)
             (λ i → P₁.σ̂₅₃ i .fst)
             (comp-pathp₂ C.hom
               (ap fst Q.σ₃₂) (ap fst Q.σ₂₁)
               (ap fst Q'.σ₃₂) (ap fst Q'.σ₂₁)
               (λ i → P₁.σ̂₃₂ i .fst) (λ i → P₁.σ̂₂₁ i .fst))

      E₂ = comp-pathp₂ C.hom
             (ap fst Q.σ₅₃) (ap fst (Q.σ₃₂ ∙ Q.σ₂₁))
             (ap fst Q'.σ₅₃) (ap fst (Q'.σ₃₂ ∙ Q'.σ₂₁))
             (λ i → P₁.σ̂₅₃ i .fst) (λ i → ẑ i .fst)

      E₃ : Fam (ap fst (Q.σ₅₃ ∙ Q.σ₃₂ ∙ Q.σ₂₁))
               (ap fst (Q'.σ₅₃ ∙ Q'.σ₃₂ ∙ Q'.σ₂₁))
      E₃ i = P₁.top̂ i .fst

      E₄ : Fam (ap fst (Q.σ₅₄ ∙ Q.σ₄₁)) (ap fst (Q'.σ₅₄ ∙ Q'.σ₄₁))
      E₄ i = P₁.bot̂ i .fst

      E₅ = comp-pathp₂ C.hom
             (ap fst Q.σ₅₄) (ap fst Q.σ₄₁)
             (ap fst Q'.σ₅₄) (ap fst Q'.σ₄₁)
             (λ i → P₁.σ̂₅₄ i .fst) (λ i → P₁.σ̂₄₁ i .fst)

      E₆ = comp-pathp₂ C.hom
             (⊗₀-assoc x y (z ⊗₀ w)) (ap fst Q.σ₄₁)
             (⊗₀-assoc x' y' (z' ⊗₀ w')) (ap fst Q'.σ₄₁)
             (⊗₁-assoc φ ψ (χ ⊗₁ ω)) (λ i → P₁.σ̂₄₁ i .fst)
```

One displaced leaf per base leaf. The whiskers ride the
`assoc●₁-nrm` slides; the shuffles are `comp-pathp₂-ap`
squares, reversed where the base leaf is a `sym`; the core is
`pentagon●₁` verbatim. Every stated endpoint is the
definitional value of its neighbour's boundary.

```agda
      whisker̂₃ : PathP (λ m → Fam (Q.whisker₃ m) (Q'.whisker₃ m)) top₁ E₁
      whisker̂₃ m =
        comp-pathp₂ C.hom
          (ap fst Q.σ₅₃) (Q.A₃ (~ m) ∙ ap fst Q.σ₂₁)
          (ap fst Q'.σ₅₃) (Q'.A₃ (~ m) ∙ ap fst Q'.σ₂₁)
          (λ i → P₁.σ̂₅₃ i .fst)
          (comp-pathp₂ C.hom
            (Q.A₃ (~ m)) (ap fst Q.σ₂₁)
            (Q'.A₃ (~ m)) (ap fst Q'.σ₂₁)
            (Â₃ (~ m)) (λ i → P₁.σ̂₂₁ i .fst))

      step̂₁ : PathP (λ m → Fam (Q.step₁ m) (Q'.step₁ m)) E₁ E₂
      step̂₁ m =
        comp-pathp₂ C.hom
          (ap fst Q.σ₅₃) (ap-comp fst Q.σ₃₂ Q.σ₂₁ (~ m))
          (ap fst Q'.σ₅₃) (ap-comp fst Q'.σ₃₂ Q'.σ₂₁ (~ m))
          (λ i → P₁.σ̂₅₃ i .fst)
          (comp-pathp₂-ap C.hom fst fst Q.σ₃₂ Q.σ₂₁ Q'.σ₃₂ Q'.σ₂₁
            (λ i → P₁.σ̂₃₂ i .fst) (λ i → P₁.σ̂₂₁ i .fst) (~ m))

      step̂₂ : PathP (λ m → Fam (Q.step₂ m) (Q'.step₂ m)) E₂ E₃
      step̂₂ m =
        comp-pathp₂-ap C.hom fst fst
          Q.σ₅₃ (Q.σ₃₂ ∙ Q.σ₂₁) Q'.σ₅₃ (Q'.σ₃₂ ∙ Q'.σ₂₁)
          (λ i → P₁.σ̂₅₃ i .fst) (λ i → ẑ i .fst) (~ m)

      step̂₄ : PathP (λ m → Fam (Q.step₄ m) (Q'.step₄ m)) E₄ E₅
      step̂₄ =
        comp-pathp₂-ap C.hom fst fst Q.σ₅₄ Q.σ₄₁ Q'.σ₅₄ Q'.σ₄₁
          (λ i → P₁.σ̂₅₄ i .fst) (λ i → P₁.σ̂₄₁ i .fst)

      whisker̂₂ : PathP (λ m → Fam (Q.whisker₂ m) (Q'.whisker₂ m)) E₅ E₆
      whisker̂₂ m =
        comp-pathp₂ C.hom
          (Q.A₂ m) (ap fst Q.σ₄₁)
          (Q'.A₂ m) (ap fst Q'.σ₄₁)
          (Â₂ m) (λ i → P₁.σ̂₄₁ i .fst)

      whisker̂₁ : PathP (λ m → Fam (Q.whisker₁ m) (Q'.whisker₁ m)) E₆ bot₁
      whisker̂₁ m =
        comp-pathp₂ C.hom
          (⊗₀-assoc x y (z ⊗₀ w)) (Q.A₁ m)
          (⊗₀-assoc x' y' (z' ⊗₀ w')) (Q'.A₁ m)
          (⊗₁-assoc φ ψ (χ ⊗₁ ω)) (Â₁ m)

      pentagon̂● : PathP (λ m → Fam (Q.pentagon●₀ m) (Q'.pentagon●₀ m)) E₁ E₅
      pentagon̂● =
        comp-pathp₂ Fam Q.step₁ (Q.step₂ ∙ Q.step₃ ∙ Q.step₄)
                        Q'.step₁ (Q'.step₂ ∙ Q'.step₃ ∙ Q'.step₄)
          step̂₁
          (comp-pathp₂ Fam Q.step₂ (Q.step₃ ∙ Q.step₄)
                           Q'.step₂ (Q'.step₃ ∙ Q'.step₄)
            step̂₂
            (comp-pathp₂ Fam Q.step₃ Q.step₄ Q'.step₃ Q'.step₄
              P₁.pentagon●₁ step̂₄))

    ⊗₁-pentagon
      : PathP (λ m → PathP (λ i → C.hom (Q.⊗₀-pentagon m i)
                                        (Q'.⊗₀-pentagon m i))
                     (φ ⊗₁ ψ ⊗₁ χ ⊗₁ ω) (((φ ⊗₁ ψ) ⊗₁ χ) ⊗₁ ω))
              top₁ bot₁
    ⊗₁-pentagon =
      comp-pathp₂ Fam
        Q.whisker₃ (Q.pentagon●₀ ∙ Q.whisker₂ ∙ Q.whisker₁)
        Q'.whisker₃ (Q'.pentagon●₀ ∙ Q'.whisker₂ ∙ Q'.whisker₁)
        whisker̂₃
        (comp-pathp₂ Fam
          Q.pentagon●₀ (Q.whisker₂ ∙ Q.whisker₁)
          Q'.pentagon●₀ (Q'.whisker₂ ∙ Q'.whisker₁)
          pentagon̂●
          (comp-pathp₂ Fam Q.whisker₂ Q.whisker₁ Q'.whisker₂ Q'.whisker₁
            whisker̂₂ whisker̂₁))
```

## The displaced triangle

The triangle over `⊗₀-triangle`: a square of hom-lines whose top
edge is the `comp-pathp₂`-composite of `⊗₁-assoc` and the
whiskered `⊗₁-unitr`, bottom edge the whiskered `⊗₁-unitl`.
Every level-0 cell was built as a wit-calculus projection, so
every leaf displaces by the same construction one level up: the
witnesses by `●₁`/`↝̂` at normal witnesses, the `ρ`-lines by
`↝̂-fill`, each face square by `is-prop→SquareP` at the pointwise
contractible `⊗₁-wit` family over its level-0 mate — the
associator face riding `is-coh₁` exactly as its base rides
`is-coh₀` — the shuffle by `comp-pathp₂-ap`, and the fiber
triangle by the `⊗₁-wit-∙` glue of the `σ̂`-lines against the
direct one. Every interface between consecutive leaves is
definitional.

The loop closes with `is-coh₁`: over `loop-sq`, the displaced
transports are joined by the `↝̂`-image of the coherence square,
and `is-prop→SquareP` at the displaced witness family projects
the displaced `loop-refl` — the hom shadow of the level-0
argument, riding the same fiber square.

```agda
  module triangle₁ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y') where
    private
      module T  = triangle₀ x  y
      module T' = triangle₀ x' y'

    ι = C.idn I

    N : ⊗₁-composite (T.A ▿₀ T.E ▿₀ T.B) (T'.A ▿₀ T'.E ▿₀ T'.B)
    N = ⊗₁-emb φ ▿₁ ⊗₁-emb ι ▿₁ ⊗₁-emb ψ

    ê₁ : PathP (λ i → ⊗₁-composite (T.e₁ i) (T'.e₁ i))
               N (⊗₁-emb φ ▿₁ ⊗₁-emb ψ)
    ê₁ i = ⊗₁-emb φ ▿₁ ⊗₁-emb-idn-absorb ψ i

    ê₂ : PathP (λ i → ⊗₁-composite (T.e₂ i) (T'.e₂ i))
               N (⊗₁-emb φ ▿₁ ⊗₁-emb ψ)
    ê₂ i = ▾₁-idn (⊗₁-emb φ) i ▿₁ ⊗₁-emb ψ

    r̂₁ : ⊗₁-wit T.r₁ T'.r₁ N
    r̂₁ = ⊗₁-wit-nrm φ ●₁ (⊗₁-wit-nrm ι ●₁ ⊗₁-wit-nrm ψ)

    r̂₂ : ⊗₁-wit T.r₂ T'.r₂ N
    r̂₂ = (⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm ι) ●₁ ⊗₁-wit-nrm ψ

    r̂₀¹ : ⊗₁-wit T.r₀¹ T'.r₀¹ N
    r̂₀¹ = (⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm ψ) ↝̂ (λ i → ê₁ (~ i))

    r̂₀² : ⊗₁-wit T.r₀² T'.r₀² N
    r̂₀² = (⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm ψ) ↝̂ (λ i → ê₂ (~ i))

    -- the displaced loop σ-line: ⊗₁-wit-σ[_,_] at the sealed base
    -- lines; the displaced loop is its fst-shadow
    σ̂-loop : PathP (λ i → ⊗₁-wit (T.σ-loop i) (T'.σ-loop i) N) r̂₀¹ r̂₀²
    σ̂-loop = ⊗₁-wit-σ[ T.σ-loop , T'.σ-loop ] r̂₀¹ r̂₀²

    loop₁ : PathP (λ i → C.hom (T.loop i) (T'.loop i)) (φ ⊗₁ ψ) (φ ⊗₁ ψ)
    loop₁ i = σ̂-loop i .fst

    -- the displaced unitor witnesses: the endpoints of
    -- unitr-σ●₁/unitl-σ●₁, the very pairs the unitors project
    Ûf : ⊗₁-wit T.Uf T'.Uf (⊗₁-emb φ)
    Ûf = (⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm ι) ↝̂ ▾₁-idn (⊗₁-emb φ)

    V̂g : ⊗₁-wit T.Vg T'.Vg (⊗₁-emb ψ)
    V̂g = (⊗₁-wit-nrm ι ●₁ ⊗₁-wit-nrm ψ) ↝̂ ⊗₁-emb-idn-absorb ψ

    ŝ₀ : ⊗₁-wit T.s₀ T'.s₀ (⊗₁-emb φ ▿₁ ⊗₁-emb ψ)
    ŝ₀ = ⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm ψ

    ŝl : ⊗₁-wit T.sl T'.sl (⊗₁-emb φ ▿₁ ⊗₁-emb ψ)
    ŝl = ⊗₁-wit-nrm φ ●₁ V̂g

    ŝr : ⊗₁-wit T.sr T'.sr (⊗₁-emb φ ▿₁ ⊗₁-emb ψ)
    ŝr = Ûf ●₁ ⊗₁-wit-nrm ψ

    -- the displaced σ-lines: ⊗₁-wit-σ[_,_] instances at the sealed
    -- level-0 lines — the seals are consumed as neutral families,
    -- no unfolding
    σ̂ₗᵣ : PathP (λ i → ⊗₁-wit (T.σₗᵣ i) (T'.σₗᵣ i)
                              (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
                ŝl ŝr
    σ̂ₗᵣ = ⊗₁-wit-σ[ T.σₗᵣ , T'.σₗᵣ ] ŝl ŝr

    σ̂ᵣ₀ : PathP (λ i → ⊗₁-wit (T.σᵣ₀ i) (T'.σᵣ₀ i)
                              (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
                ŝr ŝ₀
    σ̂ᵣ₀ = ⊗₁-wit-σ[ T.σᵣ₀ , T'.σᵣ₀ ] ŝr ŝ₀

    σ̂ₗ₀ : PathP (λ i → ⊗₁-wit (T.σₗ₀ i) (T'.σₗ₀ i)
                              (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
                ŝl ŝ₀
    σ̂ₗ₀ = ⊗₁-wit-σ[ T.σₗ₀ , T'.σₗ₀ ] ŝl ŝ₀

    -- the displaced ρ-lines: ↝̂-fill slides, ●₁-whiskered as at
    -- level 0, over exactly the level-0 slides
    ρ̂r : (m : Core.Base.I) → ⊗₁-wit (T.ρr m) (T'.ρr m) (ê₂ m)
    ρ̂r m = ↝̂-fill (⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm ι) (▾₁-idn (⊗₁-emb φ)) m
           ●₁ ⊗₁-wit-nrm ψ

    ρ̂l : (m : Core.Base.I) → ⊗₁-wit (T.ρl m) (T'.ρl m) (ê₁ m)
    ρ̂l m = ⊗₁-wit-nrm φ
           ●₁ ↝̂-fill (⊗₁-wit-nrm ι ●₁ ⊗₁-wit-nrm ψ) (⊗₁-emb-idn-absorb ψ) m

    -- the face bottoms, named: an inline face is elaborated in the
    -- ascription and again in the fill, and the two elaborations
    -- are compared term-by-term; a named face is checked once and
    -- compared by name
    whisker-σ̂r
      : PathP (λ i → ⊗₁-wit (unitr-σ●₀ x i ●₀ ⊗₀-nrm y)
                            (unitr-σ●₀ x' i ●₀ ⊗₀-nrm y')
                            (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
              ŝr ŝ₀
    whisker-σ̂r i = unitr-σ●₁ φ i ●₁ ⊗₁-wit-nrm ψ

    whisker-σ̂l
      : PathP (λ i → ⊗₁-wit (⊗₀-nrm x ●₀ unitl-σ●₀ y i)
                            (⊗₀-nrm x' ●₀ unitl-σ●₀ y' i)
                            (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
              ŝl ŝ₀
    whisker-σ̂l i = ⊗₁-wit-nrm φ ●₁ unitl-σ●₁ ψ i

    assoc-σ̂
      : PathP (λ i → ⊗₁-wit (assoc-σ●₀ (⊗₀-nrm x) (⊗₀-nrm I) (⊗₀-nrm y) i)
                            (assoc-σ●₀ (⊗₀-nrm x') (⊗₀-nrm I) (⊗₀-nrm y') i)
                            N)
              r̂₁ r̂₂
    assoc-σ̂ = assoc-σ●₁ (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ι) (⊗₁-wit-nrm ψ)

    face₁-r
      : PathP (λ i → C.hom (ap fst T.σᵣ₀ i) (ap fst T'.σᵣ₀ i))
              ((φ ⊗₁ ι) ⊗₁ ψ) (φ ⊗₁ ψ)
    face₁-r i = σ̂ᵣ₀ i .fst

    face₁-l
      : PathP (λ i → C.hom (ap fst T.σₗ₀ i) (ap fst T'.σₗ₀ i))
              (φ ⊗₁ ι ⊗₁ ψ) (φ ⊗₁ ψ)
    face₁-l i = σ̂ₗ₀ i .fst
```

The displaced unitor faces: `is-prop→SquareP` at the pointwise
contractible witness family over the level-0 square, sides
constant, bottom the `●₁`-whisker of the `unitr-σ●₁` resp.
`unitl-σ●₁` line — the `fst`-shadow's bottom edge is the
whiskered `⊗₁-unitr` resp. `⊗₁-unitl` definitionally.

```agda
    private
      wit-prop-r
        : (m i : Core.Base.I)
        → is-prop (⊗₁-wit (T.face-σr m i) (T'.face-σr m i)
                          (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
      wit-prop-r m i =
        is-contr→is-prop
          (subst is-contr
            (λ k → ⊗₁-wit (T.face-σr (m ∧ k) (i ∧ k))
                          (T'.face-σr (m ∧ k) (i ∧ k))
                          (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
            (⊗₁-wit-contr ŝr))

      wit-prop-l
        : (m i : Core.Base.I)
        → is-prop (⊗₁-wit (T.face-σl m i) (T'.face-σl m i)
                          (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
      wit-prop-l m i =
        is-contr→is-prop
          (subst is-contr
            (λ k → ⊗₁-wit (T.face-σl (m ∧ k) (i ∧ k))
                          (T'.face-σl (m ∧ k) (i ∧ k))
                          (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
            (⊗₁-wit-contr ŝl))

    face-σ̂r
      : PathP (λ m → PathP (λ i → ⊗₁-wit (T.face-σr m i) (T'.face-σr m i)
                                         (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
                     ŝr ŝ₀)
              σ̂ᵣ₀ whisker-σ̂r
    face-σ̂r = is-prop→SquareP wit-prop-r σ̂ᵣ₀ refl whisker-σ̂r refl

    face-r̂
      : PathP (λ m → PathP (λ i → C.hom (T.face-r m i) (T'.face-r m i))
                     ((φ ⊗₁ ι) ⊗₁ ψ) (φ ⊗₁ ψ))
              face₁-r (λ i → ⊗₁-unitr φ i ⊗₁ ψ)
    face-r̂ m i = face-σ̂r m i .fst

    face-σ̂l
      : PathP (λ m → PathP (λ i → ⊗₁-wit (T.face-σl m i) (T'.face-σl m i)
                                         (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
                     ŝl ŝ₀)
              σ̂ₗ₀ whisker-σ̂l
    face-σ̂l = is-prop→SquareP wit-prop-l σ̂ₗ₀ refl whisker-σ̂l refl

    face-l̂
      : PathP (λ m → PathP (λ i → C.hom (T.face-l m i) (T'.face-l m i))
                     (φ ⊗₁ ι ⊗₁ ψ) (φ ⊗₁ ψ))
              face₁-l (λ i → φ ⊗₁ ⊗₁-unitl ψ i)
    face-l̂ m i = face-σ̂l m i .fst
```

The displaced fiber triangle: the `⊗₁-wit-∙` glue of the two
`⊗₁-wit-σ` lines against the direct one, over `fiber-triangle` —
the glued edge's hom component is the `comp-pathp₂` of the
`⊗₁-wit-unique` shadows by construction.

```agda
    top̂ : PathP (λ i → ⊗₁-wit ((T.σₗᵣ ∙ T.σᵣ₀) i) ((T'.σₗᵣ ∙ T'.σᵣ₀) i)
                              (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
                ŝl ŝ₀
    top̂ = ⊗₁-wit-∙ T.σₗᵣ T.σᵣ₀ T'.σₗᵣ T'.σᵣ₀ σ̂ₗᵣ σ̂ᵣ₀

    private
      wit-prop-t
        : (m i : Core.Base.I)
        → is-prop (⊗₁-wit (T.fiber-triangle m i) (T'.fiber-triangle m i)
                          (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
      wit-prop-t m i =
        is-contr→is-prop
          (subst is-contr
            (λ k → ⊗₁-wit (T.fiber-triangle (m ∧ k) (i ∧ k))
                          (T'.fiber-triangle (m ∧ k) (i ∧ k))
                          (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
            (⊗₁-wit-contr ŝl))

    fiber-triangle₁
      : PathP (λ m → PathP (λ i → ⊗₁-wit (T.fiber-triangle m i)
                                         (T'.fiber-triangle m i)
                                         (⊗₁-emb φ ▿₁ ⊗₁-emb ψ))
                     ŝl ŝ₀)
              top̂ σ̂ₗ₀
    fiber-triangle₁ = is-prop→SquareP wit-prop-t top̂ refl σ̂ₗ₀ refl
```

The chain of edges and the displaced leaves, glued along exactly
the base tree; the associator face and the whisker that consumes
it live under the coherence hypothesis, the rest is absolute.

```agda
    private
      Fam : (x ⊗₀ I ⊗₀ y ≡ x ⊗₀ y) → (x' ⊗₀ I ⊗₀ y' ≡ x' ⊗₀ y') → Type h
      Fam p p' = PathP (λ i → C.hom (p i) (p' i)) (φ ⊗₁ ι ⊗₁ ψ) (φ ⊗₁ ψ)

    top₁ : Fam (⊗₀-assoc x I y ∙ ap (_⊗₀ y) (⊗₀-unitr x))
               (⊗₀-assoc x' I y' ∙ ap (_⊗₀ y') (⊗₀-unitr x'))
    top₁ =
      comp-pathp₂ C.hom
        (⊗₀-assoc x I y) (ap (_⊗₀ y) (⊗₀-unitr x))
        (⊗₀-assoc x' I y') (ap (_⊗₀ y') (⊗₀-unitr x'))
        (⊗₁-assoc φ ι ψ) (λ i → ⊗₁-unitr φ i ⊗₁ ψ)

    bot₁ : Fam (ap (x ⊗₀_) (⊗₀-unitl y)) (ap (x' ⊗₀_) (⊗₀-unitl y'))
    bot₁ i = φ ⊗₁ ⊗₁-unitl ψ i

    private
      E₁ = comp-pathp₂ C.hom
             (ap fst T.σₗᵣ) (ap (_⊗₀ y) (⊗₀-unitr x))
             (ap fst T'.σₗᵣ) (ap (_⊗₀ y') (⊗₀-unitr x'))
             (λ i → σ̂ₗᵣ i .fst) (λ i → ⊗₁-unitr φ i ⊗₁ ψ)

      E₂ = comp-pathp₂ C.hom
             (ap fst T.σₗᵣ) (ap fst T.σᵣ₀)
             (ap fst T'.σₗᵣ) (ap fst T'.σᵣ₀)
             (λ i → σ̂ₗᵣ i .fst) face₁-r

      E₃ : Fam (ap fst (T.σₗᵣ ∙ T.σᵣ₀)) (ap fst (T'.σₗᵣ ∙ T'.σᵣ₀))
      E₃ i = top̂ i .fst

    step̂₁ : PathP (λ m → Fam (T.step₁ m) (T'.step₁ m)) E₂ E₃
    step̂₁ m =
      comp-pathp₂-ap C.hom fst fst T.σₗᵣ T.σᵣ₀ T'.σₗᵣ T'.σᵣ₀
        (λ i → σ̂ₗᵣ i .fst) face₁-r (~ m)

    step̂₂ : PathP (λ m → Fam (T.step₂ m) (T'.step₂ m)) E₃ face₁-l
    step̂₂ m i = fiber-triangle₁ m i .fst

    whisker-r̂ : PathP (λ m → Fam (T.whisker-r m) (T'.whisker-r m)) E₁ E₂
    whisker-r̂ m =
      comp-pathp₂ C.hom
        (ap fst T.σₗᵣ) (T.face-r (~ m))
        (ap fst T'.σₗᵣ) (T'.face-r (~ m))
        (λ i → σ̂ₗᵣ i .fst) (face-r̂ (~ m))

    triangle-weak̂
      : PathP (λ m → Fam (T.triangle-weak m) (T'.triangle-weak m)) E₁ bot₁
    triangle-weak̂ =
      comp-pathp₂ Fam T.whisker-r (T.step₁ ∙ T.step₂ ∙ T.face-l)
                      T'.whisker-r (T'.step₁ ∙ T'.step₂ ∙ T'.face-l)
        whisker-r̂
        (comp-pathp₂ Fam T.step₁ (T.step₂ ∙ T.face-l)
                         T'.step₁ (T'.step₂ ∙ T'.face-l)
          step̂₁
          (comp-pathp₂ Fam T.step₂ T.face-l T'.step₂ T'.face-l
            step̂₂ face-l̂))

    module _ (mid : is-monoidal-2-coherent M) where
      private
        wit-prop-a
          : (m i : Core.Base.I)
          → is-prop (⊗₁-wit (T.face-σa mid m i) (T'.face-σa mid m i)
                            (mid .is-monoidal-2-coherent.is-coh₁ φ ψ
                              (~ i) (~ m)))
        wit-prop-a m i =
          is-contr→is-prop
            (subst is-contr
              (λ k → ⊗₁-wit (T.face-σa mid (m ∧ k) (i ∧ k))
                            (T'.face-σa mid (m ∧ k) (i ∧ k))
                            (mid .is-monoidal-2-coherent.is-coh₁ φ ψ
                              (~ (i ∧ k)) (~ (m ∧ k))))
              (⊗₁-wit-contr ŝl))

      face-σ̂a
        : PathP (λ m → PathP (λ i → ⊗₁-wit (T.face-σa mid m i)
                                           (T'.face-σa mid m i)
                                           (mid .is-monoidal-2-coherent.is-coh₁
                                             φ ψ (~ i) (~ m)))
                       (ρ̂l (~ m)) (ρ̂r (~ m)))
                σ̂ₗᵣ assoc-σ̂
      face-σ̂a =
        is-prop→SquareP wit-prop-a
          σ̂ₗᵣ (λ m → ρ̂l (~ m))
          assoc-σ̂
          (λ m → ρ̂r (~ m))

      face-â
        : PathP (λ m → PathP (λ i → C.hom (T.face-a mid m i)
                                          (T'.face-a mid m i))
                       (φ ⊗₁ ι ⊗₁ ψ) ((φ ⊗₁ ι) ⊗₁ ψ))
                (λ i → σ̂ₗᵣ i .fst) (⊗₁-assoc φ ι ψ)
      face-â m i = face-σ̂a m i .fst

      whisker-â
        : PathP (λ m → Fam (T.whisker-a mid m) (T'.whisker-a mid m)) top₁ E₁
      whisker-â m =
        comp-pathp₂ C.hom
          (T.face-a mid (~ m)) (ap (_⊗₀ y) (⊗₀-unitr x))
          (T'.face-a mid (~ m)) (ap (_⊗₀ y') (⊗₀-unitr x'))
          (face-â (~ m)) (λ i → ⊗₁-unitr φ i ⊗₁ ψ)

      ⊗₁-triangle
        : PathP (λ m → PathP (λ i → C.hom (T.⊗₀-triangle mid m i)
                                          (T'.⊗₀-triangle mid m i))
                       (φ ⊗₁ ι ⊗₁ ψ) (φ ⊗₁ ψ))
                top₁ bot₁
      ⊗₁-triangle =
        comp-pathp₂ Fam
          (T.whisker-a mid) T.triangle-weak
          (T'.whisker-a mid) T'.triangle-weak
          whisker-â triangle-weak̂

      private
        K  = T.loop-sq  mid
        K' = T'.loop-sq mid

        wprop
          : (k i : Core.Base.I)
          → is-prop (⊗₁-wit (K k i) (K' k i) N)
        wprop k i =
          is-contr→is-prop
            (subst is-contr
              (λ t → ⊗₁-wit (K (k ∧ t) (i ∧ t)) (K' (k ∧ t) (i ∧ t)) N)
              (⊗₁-wit-contr r̂₀¹))

        -- the ↝̂-image of the coherence square: the displaced
        -- is-coh₀-transport line joining the two loop witnesses
        ĉ : PathP (λ i → ⊗₁-wit (K i1 i) (K' i1 i) N) r̂₀¹ r̂₀²
        ĉ i =
          (⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm ψ)
          ↝̂ (λ t → mid .is-monoidal-2-coherent.is-coh₁ φ ψ (~ i) (~ t))

        Ŝ : PathP (λ k → PathP (λ i → ⊗₁-wit (K k i) (K' k i) N) r̂₀¹ r̂₀²)
                  σ̂-loop ĉ
        Ŝ = is-prop→SquareP wprop σ̂-loop refl ĉ refl

      loop₁-refl
        : PathP (λ k → PathP (λ i → C.hom (T.loop-refl  mid k i)
                                          (T'.loop-refl mid k i))
                       (φ ⊗₁ ψ) (φ ⊗₁ ψ))
                loop₁ refl
      loop₁-refl k i = Ŝ k i .fst
```
