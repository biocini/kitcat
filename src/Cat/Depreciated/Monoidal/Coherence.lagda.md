Lane Biocini
July 2026

Coherence of the tensor over the two-field record: the interchange
coherence block, developed once over an arbitrary interchange pair
in witness form and instantiated at either field, and the pentagon,
which consumes no interchange at all. The archived single-field
form is `Cat.Depreciated.Monoidal.Legacy.Coherence`.

The `ι-mult` statements are 3-coherence hypotheses — consumed
rather than proved, well-typed by the strict mixed associativity of
the ternary orders; naturality of the supplied interchange in its
first pair is free, the `Path.commutes` reading of a square in the
propositional representability fiber, and its displaced mate is
`comp-pathp₂-commutes` on the interchange cube. The pentagon runs
entirely in the pull-side calculus: the five bracketings of a
fourfold pairing inhabit one propositional fiber, the fiber
pentagon is a set-level identification, the object pentagon its
`fst`-shadow straightened by `nrm`-slides, and the displaced
pentagon glues one displaced leaf per base leaf.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Monoidal.Coherence where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp; comp-pathp₂-ap)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (is-prop→SquareP)
open import Core.Transport.J using (subst)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Base
open import Cat.Depreciated.Monoidal
open import Cat.Depreciated.Monoidal.Bifunctor

module coherence {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  open bifunctor-theory M
  private module C = category C
```

## Interchange coherence

Over an arbitrary interchange pair in the fields' own shape: the
witness form at both grades, the pointwise forms their
`nrm`-shadows.

```agda
  module interchange-coherence
    (ι♭ : {A B : ⊗₀-composite}
        → is-⊗₀-representable A → is-⊗₀-representable B
        → A ▿₀ B ≡ A ▵₀ B)
    (ι♭₁ : ∀ {A A' B B' : ⊗₀-composite}
             {U : is-⊗₀-representable A} {U' : is-⊗₀-representable A'}
             {V : is-⊗₀-representable B} {V' : is-⊗₀-representable B'}
             {η : ⊗₁-composite A A'} {ζ : ⊗₁-composite B B'}
         → ⊗₁-wit U U' η → ⊗₁-wit V V' ζ
         → PathP (λ i → ⊗₁-composite (ι♭ U V i) (ι♭ U' V' i))
                 (η ▿₁ ζ) (η ▵₁ ζ))
    where

    private
      ι-pt : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y
      ι-pt x y = ι♭ (⊗₀-nrm x) (⊗₀-nrm y)

      ι₁-pt : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
            → PathP (λ i → ⊗₁-composite (ι-pt x y i) (ι-pt x' y' i))
                    (⊗₁-emb φ ▾₁ ψ) (φ ▴₁ ⊗₁-emb ψ)
      ι₁-pt φ ψ = ι♭₁ (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ)

    open over-interchange ι-pt using (_○₀_)
    open over-interchange-bifunctor ι-pt ι₁-pt using (_○₁_)

    ι-mult-r₀
      : ∀ {F G H : ⊗₀-composite}
        (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
        (W : is-⊗₀-representable H)
      → Type o
    ι-mult-r₀ {H = H} U V W =
      ap (λ X → X ▿₀ H) (ι♭ U V) ≡ ι♭ U (V ●₀ W)

    ι-mult-l₀
      : ∀ {F G H : ⊗₀-composite}
        (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
        (W : is-⊗₀-representable H)
      → Type o
    ι-mult-l₀ {F = F} U V W =
      ap (λ X → F ▵₀ X) (ι♭ V W) ≡ ι♭ (U ○₀ V) W

    -- opaque like assoc-σ●₀: the naturality cube's type family
    -- projects this line at generic interval points, at both grades;
    -- the sealed head keeps those comparisons neutral, and the
    -- endpoints still reduce by the type-directed rule
    opaque
      ●₀-coh
        : ∀ {F G : ⊗₀-composite}
          (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
        → PathP (λ i → is-⊗₀-representable (ι♭ U V i))
                (U ●₀ V) (U ○₀ V)
      ●₀-coh U V =
        is-prop→PathP
          (λ i → is-⊗₀-representable-prop (ι♭ U V i))
          (U ●₀ V) (U ○₀ V)

    ⊗₀-interchange-natural
      : ∀ {F G H : ⊗₀-composite}
        (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
        (W : is-⊗₀-representable H)
      → ap (λ X → X ▿₀ H) (ι♭ U V) ∙ ι♭ (U ○₀ V) W
      ≡ ι♭ (U ●₀ V) W ∙ ap (λ X → X ▵₀ H) (ι♭ U V)
    ⊗₀-interchange-natural {H = H} U V W =
      Path.commutes
        (ap (λ X → X ▿₀ H) (ι♭ U V)) (ι♭ (U ○₀ V) W)
        (ι♭ (U ●₀ V) W) (ap (λ X → X ▵₀ H) (ι♭ U V))
        (λ j i → ι♭ (●₀-coh U V i) W j)
```

One grade up, the same four shapes displace over their level-0
mates: the `ι-mult` statements become squares of hom-composite
lines, `●₁-coh` is the `is-prop→PathP` at the displaced witness
family over the flat line, and the naturality is the displaced
`Path.commutes` at the `comp-pathp₂` composites.

```agda
    ι-mult-r₁
      : ∀ {F F' G G' H H' : ⊗₀-composite}
          {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
          {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
          {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
          {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
          {θ : ⊗₁-composite H H'}
        (mr : ι-mult-r₀ U V W) (mr' : ι-mult-r₀ U' V' W')
        (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
      → Type (o ⊔ h)
    ι-mult-r₁ {η = η} {ζ} {θ} mr mr' Û V̂ Ŵ =
      PathP (λ k → PathP (λ i → ⊗₁-composite (mr k i) (mr' k i))
                         (η ▿₁ ζ ▿₁ θ) (η ▵₁ ζ ▿₁ θ))
            (λ i → ι♭₁ Û V̂ i ▿₁ θ)
            (ι♭₁ Û (V̂ ●₁ Ŵ))

    ι-mult-l₁
      : ∀ {F F' G G' H H' : ⊗₀-composite}
          {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
          {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
          {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
          {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
          {θ : ⊗₁-composite H H'}
        (ml : ι-mult-l₀ U V W) (ml' : ι-mult-l₀ U' V' W')
        (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
      → Type (o ⊔ h)
    ι-mult-l₁ {η = η} {ζ} {θ} ml ml' Û V̂ Ŵ =
      PathP (λ k → PathP (λ i → ⊗₁-composite (ml k i) (ml' k i))
                         (η ▵₁ ζ ▿₁ θ) (η ▵₁ ζ ▵₁ θ))
            (λ i → η ▵₁ ι♭₁ V̂ Ŵ i)
            (ι♭₁ (Û ○₁ V̂) Ŵ)

    opaque
      ●₁-coh
        : ∀ {F F' G G' : ⊗₀-composite}
            {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
            {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
            {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
          (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ)
        → PathP (λ i → ⊗₁-wit (●₀-coh U V i) (●₀-coh U' V' i)
                              (ι♭₁ Û V̂ i))
                (Û ●₁ V̂) (Û ○₁ V̂)
      ●₁-coh {U = U} {U'} {V} {V'} Û V̂ =
        is-prop→PathP
          (λ i → is-contr→is-prop
            (subst is-contr
              (λ k → ⊗₁-wit (●₀-coh U V (i ∧ k)) (●₀-coh U' V' (i ∧ k))
                            (ι♭₁ Û V̂ (i ∧ k)))
              (⊗₁-wit-contr (Û ●₁ V̂))))
          (Û ●₁ V̂) (Û ○₁ V̂)

    ⊗₁-interchange-natural
      : ∀ {F F' G G' H H' : ⊗₀-composite}
          {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
          {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
          {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
          {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
          {θ : ⊗₁-composite H H'}
        (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
      → PathP (λ k → PathP (λ i → ⊗₁-composite
                                    (⊗₀-interchange-natural U V W k i)
                                    (⊗₀-interchange-natural U' V' W' k i))
                           (η ▿₁ ζ ▿₁ θ) (η ▵₁ ζ ▵₁ θ))
              (comp-pathp₂ ⊗₁-composite
                (ap (λ X → X ▿₀ H) (ι♭ U V))
                (ι♭ (U ○₀ V) W)
                (ap (λ X → X ▿₀ H') (ι♭ U' V'))
                (ι♭ (U' ○₀ V') W')
                (λ i → ι♭₁ Û V̂ i ▿₁ θ)
                (ι♭₁ (Û ○₁ V̂) Ŵ))
              (comp-pathp₂ ⊗₁-composite
                (ι♭ (U ●₀ V) W)
                (ap (λ X → X ▵₀ H) (ι♭ U V))
                (ι♭ (U' ●₀ V') W')
                (ap (λ X → X ▵₀ H') (ι♭ U' V'))
                (ι♭₁ (Û ●₁ V̂) Ŵ)
                (λ i → ι♭₁ Û V̂ i ▵₁ θ))
    ⊗₁-interchange-natural {H = H} {H'} {U = U} {U'} {V} {V'} {W} {W'}
      {θ = θ} Û V̂ Ŵ =
      comp-pathp₂-commutes ⊗₁-composite
        (ap (λ X → X ▿₀ H) (ι♭ U V))
        (ι♭ (U ○₀ V) W)
        (ι♭ (U ●₀ V) W)
        (ap (λ X → X ▵₀ H) (ι♭ U V))
        (ap (λ X → X ▿₀ H') (ι♭ U' V'))
        (ι♭ (U' ○₀ V') W')
        (ι♭ (U' ●₀ V') W')
        (ap (λ X → X ▵₀ H') (ι♭ U' V'))
        (λ j i → ι♭ (●₀-coh U V i) W j)
        (λ j i → ι♭ (●₀-coh U' V' i) W' j)
        (λ i → ι♭₁ Û V̂ i ▿₁ θ)
        (ι♭₁ (Û ○₁ V̂) Ŵ)
        (ι♭₁ (Û ●₁ V̂) Ŵ)
        (λ i → ι♭₁ Û V̂ i ▵₁ θ)
        (λ j i → ι♭₁ (●₁-coh Û V̂ i) Ŵ j)
```

## The pentagon

The fully nested composite is strictly bracketing-free, so the
five bracketings of a fourfold `●₀` inhabit one propositional
fiber; the fiber pentagon is a set-level identification of edge
composites, and the object pentagon is its `ap fst` image,
straightened to `⊗₀-assoc` endpoints by `assoc●₀-nrm`. Nothing in
this section consumes an interchange.

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

    ℓt : p₃ ≡ p₁
    ℓt = σ₃₂ ∙ σ₂₁

    ℓc : p₅ ≡ p₁
    ℓc = σ₅₃ ∙ ℓt

    rc : p₅ ≡ p₁
    rc = σ₅₄ ∙ σ₄₁

    -- opaque like assoc-σ●₀: level-1 families project its slices
    -- at generic interval points, and the sealed head keeps those
    -- comparisons syntactic; the boundary still reduces by the
    -- type-directed rule
    opaque
      fiber-pentagon : ℓc ≡ rc
      fiber-pentagon = is-contr→is-set T-contr p₅ p₁ ℓc rc

    -- the ∙-tree of the fiber pentagon's hom shadow, leaf by leaf:
    -- two ap-comp shuffles into the shadow, the shadow itself, one
    -- shuffle out — named so the displaced pentagon can glue over
    -- each leaf separately
    step₁ = sym (ap (ap fst σ₅₃ ∙_) (ap-comp fst σ₃₂ σ₂₁))
    step₂ = sym (ap-comp fst σ₅₃ ℓt)
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
  assoc●₀-nrm U V W m = assoc●₀ (nrm-slide₀ U m) (nrm-slide₀ V m) (nrm-slide₀ W m)

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
  assoc●₁-nrm Û V̂ Ŵ m = assoc●₁ (nrm-slide₁ Û m) (nrm-slide₁ V̂ m) (nrm-slide₁ Ŵ m)

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

## The displaced pentagon

The level-1 pentagon in `●`-form: the five bracketings of a
fourfold `●₁` displace the level-0 witnesses, the five edges
displace the `σ`s, and the square between the glued edge
composites fills by `is-prop→SquareP` — the displaced witness
spaces are contractible pointwise over the whole of
`fiber-pentagon`.

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
    φ = Û .fst ; ψ = V̂ .fst ; χ = Ŵ .fst ; ξ = X̂ .fst

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

    top̂ : PathP (λ i → ⊗₁-wit (P.ℓc i) (P'.ℓc i) N₁)
                p̂₅ p̂₁
    top̂ = ⊗₁-wit-∙ P.σ₅₃ P.ℓt P'.σ₅₃ P'.ℓt
            σ̂₅₃ (⊗₁-wit-∙ P.σ₃₂ P.σ₂₁ P'.σ₃₂ P'.σ₂₁ σ̂₃₂ σ̂₂₁)

    bot̂ : PathP (λ i → ⊗₁-wit (P.rc i) (P'.rc i) N₁)
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
                     (φ ⊗₁ (ψ ⊗₁ (χ ⊗₁ ξ)))
                     (((φ ⊗₁ ψ) ⊗₁ χ) ⊗₁ ξ))
              (λ i → top̂ i .fst) (λ i → bot̂ i .fst)
    pentagon●₁ j i = fiber-pentagon₁ j i .fst
```

## The canonical displaced pentagon

The pentagon over `⊗₀-pentagon` itself: a square of hom-lines
whose edges are the `comp-pathp₂`-composites of the whiskered
`⊗₁-assoc` lines. Every leaf of the base tree displaces by
construction — the `A`-whiskers are `assoc●₁-nrm` slides, the
`ap-comp` shuffles are `comp-pathp₂-ap` squares, and the core leaf
is `pentagon●₁`; `comp-pathp₂` at the family of pentagon fillers
glues the displaced leaves along exactly the base tree.

```agda
  module pentagon₁ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
                   {z z'} (χ : C.hom z z') {w w'} (ξ : C.hom w w')
    where

    private
      module Q  = pentagon₀ x y z w
      module Q' = pentagon₀ x' y' z' w'
      module P₁ = pentagon●₁ (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ)
                             (⊗₁-wit-nrm χ) (⊗₁-wit-nrm ξ)

      Fam : (x ⊗₀ y ⊗₀ z ⊗₀ w ≡ ((x ⊗₀ y) ⊗₀ z) ⊗₀ w)
          → (x' ⊗₀ y' ⊗₀ z' ⊗₀ w' ≡ ((x' ⊗₀ y') ⊗₀ z') ⊗₀ w')
          → Type h
      Fam p p' = PathP (λ i → C.hom (p i) (p' i))
                       (φ ⊗₁ ψ ⊗₁ χ ⊗₁ ξ) (((φ ⊗₁ ψ) ⊗₁ χ) ⊗₁ ξ)

      -- the displaced A-whiskers: assoc●₁-nrm at the same
      -- compound witnesses A₁–A₃ straighten
      Â₁ = assoc●₁-nrm (⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm ψ)
                       (⊗₁-wit-nrm χ) (⊗₁-wit-nrm ξ)
      Â₂ = assoc●₁-nrm (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ)
                       (⊗₁-wit-nrm χ ●₁ ⊗₁-wit-nrm ξ)
      Â₃ = assoc●₁-nrm (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ ●₁ ⊗₁-wit-nrm χ)
                       (⊗₁-wit-nrm ξ)

      -- the inner witness glue of top̂, shared by both shuffle legs
      ẑ = ⊗₁-wit-∙ Q.σ₃₂ Q.σ₂₁ Q'.σ₃₂ Q'.σ₂₁ P₁.σ̂₃₂ P₁.σ̂₂₁

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
        (λ i → φ ⊗₁ ⊗₁-assoc ψ χ ξ i)
        (comp-pathp₂ C.hom
          (⊗₀-assoc x (y ⊗₀ z) w) (ap (_⊗₀ w) (⊗₀-assoc x y z))
          (⊗₀-assoc x' (y' ⊗₀ z') w') (ap (_⊗₀ w') (⊗₀-assoc x' y' z'))
          (⊗₁-assoc φ (ψ ⊗₁ χ) ξ)
          (λ i → ⊗₁-assoc φ ψ χ i ⊗₁ ξ))

    bot₁ : Fam (⊗₀-assoc x y (z ⊗₀ w) ∙ ⊗₀-assoc (x ⊗₀ y) z w)
               (⊗₀-assoc x' y' (z' ⊗₀ w') ∙ ⊗₀-assoc (x' ⊗₀ y') z' w')
    bot₁ =
      comp-pathp₂ C.hom
        (⊗₀-assoc x y (z ⊗₀ w)) (⊗₀-assoc (x ⊗₀ y) z w)
        (⊗₀-assoc x' y' (z' ⊗₀ w')) (⊗₀-assoc (x' ⊗₀ y') z' w')
        (⊗₁-assoc φ ψ (χ ⊗₁ ξ)) (⊗₁-assoc (φ ⊗₁ ψ) χ ξ)

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
             (ap fst Q.σ₅₃) (ap fst Q.ℓt)
             (ap fst Q'.σ₅₃) (ap fst Q'.ℓt)
             (λ i → P₁.σ̂₅₃ i .fst) (λ i → ẑ i .fst)

      E₃ : Fam (ap fst Q.ℓc) (ap fst Q'.ℓc)
      E₃ i = P₁.top̂ i .fst

      E₄ : Fam (ap fst Q.rc) (ap fst Q'.rc)
      E₄ i = P₁.bot̂ i .fst

      E₅ = comp-pathp₂ C.hom
             (ap fst Q.σ₅₄) (ap fst Q.σ₄₁)
             (ap fst Q'.σ₅₄) (ap fst Q'.σ₄₁)
             (λ i → P₁.σ̂₅₄ i .fst) (λ i → P₁.σ̂₄₁ i .fst)

      E₆ = comp-pathp₂ C.hom
             (⊗₀-assoc x y (z ⊗₀ w)) (ap fst Q.σ₄₁)
             (⊗₀-assoc x' y' (z' ⊗₀ w')) (ap fst Q'.σ₄₁)
             (⊗₁-assoc φ ψ (χ ⊗₁ ξ)) (λ i → P₁.σ̂₄₁ i .fst)

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
          Q.σ₅₃ Q.ℓt Q'.σ₅₃ Q'.ℓt
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
          (⊗₁-assoc φ ψ (χ ⊗₁ ξ)) (Â₁ m)

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
                     (φ ⊗₁ ψ ⊗₁ χ ⊗₁ ξ) (((φ ⊗₁ ψ) ⊗₁ χ) ⊗₁ ξ))
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
