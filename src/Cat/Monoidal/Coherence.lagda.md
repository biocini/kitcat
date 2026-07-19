Lane Biocini
July 2026

2-coherence of the tensor: the transcription of `Cat.Coherence`
under the dictionary hom ↦ ob, graded like the rest of the
monoidal spine. `coherence₀` carries the interchange coherence
and the object-level pentagon, both read off the propositional
representability fibers — the pentagon is one `is-contr→is-set`
away from `⊗₀-nrm`-strictness, exactly as at the hom level. The
triangle (consuming `monoidal-2-coherent`) and the displaced
level-1 pentagon over `⊗₁-assoc` follow the same spine.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Coherence where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.J using (J)

open import Cat.Type
open import Cat.Base
open import Cat.Monoidal

module coherence₀ {o h} {C : category o h} (M₀ : monoidal-axioms₀ C) where
  open monoidal-axioms₀ M₀
  open theory₀ M₀
  private module C = category C
```

## Interchange coherence

The two witness pairings agree over the interchange: the fibers
are propositional, so the `⋉₀`/`⋊₀` images of the same pair are
joined by a `PathP` over `⊗₀-interchange♭`, and naturality of the
interchange in its first pair is the `Path.commutes` reading of
that square.

```agda
  ⋉₀-coh
    : ∀ {F G : ⊗₀-composite}
      (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
    → PathP (λ i → is-⊗₀-representable (⊗₀-interchange♭ U V i))
            (U ⋉₀ V) (U ⋊₀ V)
  ⋉₀-coh U V =
    is-prop→PathP
      (λ i → is-⊗₀-representable-prop (⊗₀-interchange♭ U V i))
      (U ⋉₀ V) (U ⋊₀ V)

  ⊗₀-interchange-natural
    : ∀ {F G H : ⊗₀-composite}
      (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
      (W : is-⊗₀-representable H)
    → ap (λ X → X ▿₀ H) (⊗₀-interchange♭ U V) ∙ ⊗₀-interchange♭ (U ⋊₀ V) W
    ≡ ⊗₀-interchange♭ (U ⋉₀ V) W ∙ ap (λ X → X ▵₀ H) (⊗₀-interchange♭ U V)
  ⊗₀-interchange-natural {H = H} U V W =
    Path.commutes
      (ap (λ X → X ▿₀ H) (⊗₀-interchange♭ U V)) (⊗₀-interchange♭ (U ⋊₀ V) W)
      (⊗₀-interchange♭ (U ⋉₀ V) W) (ap (λ X → X ▵₀ H) (⊗₀-interchange♭ U V))
      (λ j i → ⊗₀-interchange♭ (⋉₀-coh U V i) W j)
```

## The pentagon

The fully nested composite is strictly bracketing-free, so the
five bracketings of a fourfold `⋉₀` inhabit one propositional
fiber; the fiber pentagon is a set-level identification of edge
composites, and the object pentagon is its `ap fst` image,
straightened to `⊗₀-assoc` endpoints by `assoc⋉₀-nrm`.

```agda
  module pentagon⋉₀ {F G H K : ⊗₀-composite}
    (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
    (W : is-⊗₀-representable H) (X : is-⊗₀-representable K)
    where

    T : ⊗₀-composite
    T = F ▿₀ G ▿₀ H ▿₀ K

    p₁ p₂ p₃ p₄ p₅ : is-⊗₀-representable T
    p₁ = ((U ⋉₀ V) ⋉₀ W) ⋉₀ X
    p₂ = (U ⋉₀ (V ⋉₀ W)) ⋉₀ X
    p₃ = U ⋉₀ ((V ⋉₀ W) ⋉₀ X)
    p₄ = (U ⋉₀ V) ⋉₀ (W ⋉₀ X)
    p₅ = U ⋉₀ (V ⋉₀ (W ⋉₀ X))

    T-contr : is-contr (is-⊗₀-representable T)
    T-contr .center = p₁
    T-contr .paths  = is-⊗₀-representable-prop T p₁

    σ₂₁ : p₂ ≡ p₁ ; σ₂₁ i = assoc-σ⋉₀ U V W i ⋉₀ X
    σ₃₂ : p₃ ≡ p₂ ; σ₃₂   = assoc-σ⋉₀ U (V ⋉₀ W) X
    σ₅₃ : p₅ ≡ p₃ ; σ₅₃ i = U ⋉₀ assoc-σ⋉₀ V W X i
    σ₄₁ : p₄ ≡ p₁ ; σ₄₁   = assoc-σ⋉₀ (U ⋉₀ V) W X
    σ₅₄ : p₅ ≡ p₄ ; σ₅₄   = assoc-σ⋉₀ U V (W ⋉₀ X)

    fiber-pentagon : σ₅₃ ∙ σ₃₂ ∙ σ₂₁ ≡ σ₅₄ ∙ σ₄₁
    fiber-pentagon =
      is-contr→is-set T-contr p₅ p₁ (σ₅₃ ∙ σ₃₂ ∙ σ₂₁) (σ₅₄ ∙ σ₄₁)

    pentagon⋉₀
      : ap (U .fst ⊗₀_) (assoc⋉₀ V W X)
        ∙ assoc⋉₀ U (V ⋉₀ W) X
        ∙ ap (_⊗₀ X .fst) (assoc⋉₀ U V W)
      ≡ assoc⋉₀ U V (W ⋉₀ X) ∙ assoc⋉₀ (U ⋉₀ V) W X
    pentagon⋉₀ =
        sym (ap (ap fst σ₅₃ ∙_) (ap-comp fst σ₃₂ σ₂₁))
      ∙ sym (ap-comp fst σ₅₃ (σ₃₂ ∙ σ₂₁))
      ∙ ap (ap fst) fiber-pentagon
      ∙ ap-comp fst σ₅₄ σ₄₁

  assoc⋉₀-nrm
    : ∀ {F G H : ⊗₀-composite}
      (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
      (W : is-⊗₀-representable H)
    → assoc⋉₀ U V W ≡ ⊗₀-assoc (U .fst) (V .fst) (W .fst)
  assoc⋉₀-nrm (m , p) (n , q) (o , r) =
      J (λ _ r' → assoc⋉₀ (m , p) (n , q) (o , r')
                ≡ assoc⋉₀ (m , p) (n , q) (⊗₀-nrm o)) refl r
    ∙ J (λ _ q' → assoc⋉₀ (m , p) (n , q') (⊗₀-nrm o)
                ≡ assoc⋉₀ (m , p) (⊗₀-nrm n) (⊗₀-nrm o)) refl q
    ∙ J (λ _ p' → assoc⋉₀ (m , p') (⊗₀-nrm n) (⊗₀-nrm o)
                ≡ assoc⋉₀ (⊗₀-nrm m) (⊗₀-nrm n) (⊗₀-nrm o)) refl p

  module _ (x y z w : C.ob) where
    open pentagon⋉₀ (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z) (⊗₀-nrm w)

    private
      A₁ = assoc⋉₀-nrm (⊗₀-nrm x ⋉₀ ⊗₀-nrm y) (⊗₀-nrm z) (⊗₀-nrm w)
      A₂ = assoc⋉₀-nrm (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z ⋉₀ ⊗₀-nrm w)
      A₃ = assoc⋉₀-nrm (⊗₀-nrm x) (⊗₀-nrm y ⋉₀ ⊗₀-nrm z) (⊗₀-nrm w)

    ⊗₀-pentagon
      : ap (x ⊗₀_) (⊗₀-assoc y z w)
        ∙ ⊗₀-assoc x (y ⊗₀ z) w
        ∙ ap (_⊗₀ w) (⊗₀-assoc x y z)
      ≡ ⊗₀-assoc x y (z ⊗₀ w) ∙ ⊗₀-assoc (x ⊗₀ y) z w
    ⊗₀-pentagon =
        ap (λ t → ap (x ⊗₀_) (⊗₀-assoc y z w)
                  ∙ (t ∙ ap (_⊗₀ w) (⊗₀-assoc x y z))) (sym A₃)
      ∙ pentagon⋉₀
      ∙ ap (λ t → t ∙ assoc⋉₀ (⊗₀-nrm x ⋉₀ ⊗₀-nrm y) (⊗₀-nrm z) (⊗₀-nrm w)) A₂
      ∙ ap (⊗₀-assoc x y (z ⊗₀ w) ∙_) A₁
```
