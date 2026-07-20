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
The displaced level-1 pentagon over `⊗₁-assoc` follows the same
spine.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Coherence where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (is-prop→SquareP)
open import Core.Transport.J using (J; subst)

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

## The triangle

The middle-unit composite `A ▿₀ E ▿₀ B` carries five witnesses:
the two bracketings `r₁`/`r₂` and the `↝`-transports of the
plain pair along the two unit contractions. Every face of the
triangle is a `⊗₀-repr-unique` between two of them — the unitor
faces computed by `⊗₀-repr-ap` at the one-sided pairings, the
associator face definitionally `⊗₀-assoc x I y` — and `is-coh₀`
identifies the two transports, closing the `loop` and
strengthening the weak triangle to the standard one.

```agda
  module triangle₀ (x y : C.ob) where
    A = ⊗₀-emb x
    E = ⊗₀-emb I
    B = ⊗₀-emb y

    -- 1 = source of ⊗₀-assoc (right-nested), 2 = target (left-nested)
    e₁ : A ▿₀ (E ▿₀ B) ≡ A ▿₀ B ;  e₁ = ap (A ▿₀_) (⊗₀-emb-idn-absorb y)
    e₂ : (A ▿₀ E) ▿₀ B ≡ A ▿₀ B ;  e₂ = ap (_▿₀ B) (▾₀-idn A)

    r₁ r₂ r₀¹ r₀² : is-⊗₀-representable (A ▿₀ E ▿₀ B)
    r₁  = ⊗₀-nrm x ⋉₀ (⊗₀-nrm I ⋉₀ ⊗₀-nrm y)     -- fst = x ⊗₀ (I ⊗₀ y)
    r₂  = (⊗₀-nrm x ⋉₀ ⊗₀-nrm I) ⋉₀ ⊗₀-nrm y     -- fst = (x ⊗₀ I) ⊗₀ y
    r₀¹ = (⊗₀-nrm x ⋉₀ ⊗₀-nrm y) ↝ sym e₁
    r₀² = (⊗₀-nrm x ⋉₀ ⊗₀-nrm y) ↝ sym e₂

    T-contr : is-contr (is-⊗₀-representable (A ▿₀ E ▿₀ B))
    T-contr .center = r₁
    T-contr .paths  = is-⊗₀-representable-prop _ r₁

    opaque
      unfolding assoc-σ⋉₀

      assoc-eq : ⊗₀-repr-unique r₁ r₂ ≡ ⊗₀-assoc x I y
      assoc-eq = refl

    loop : x ⊗₀ y ≡ x ⊗₀ y
    loop = ⊗₀-repr-unique r₀¹ r₀²

    Uf : is-⊗₀-representable A ; Uf = (⊗₀-nrm x ⋉₀ ⊗₀-nrm I) ↝ ▾₀-idn A
    Vg : is-⊗₀-representable B ; Vg = (⊗₀-nrm I ⋉₀ ⊗₀-nrm y) ↝ ⊗₀-emb-idn-absorb y

    s₀ s₁ s₂ : is-⊗₀-representable (A ▿₀ B)
    s₀ = ⊗₀-nrm x ⋉₀ ⊗₀-nrm y   ;  s₁ = r₁ ↝ e₁  ;  s₂ = r₂ ↝ e₂

    Ĝr : is-⊗₀-representable A → is-⊗₀-representable (A ▿₀ B)
    Ĝr u = u ⋉₀ ⊗₀-nrm y

    Ĝl : is-⊗₀-representable B → is-⊗₀-representable (A ▿₀ B)
    Ĝl v = ⊗₀-nrm x ⋉₀ v

    private
      W  = (⊗₀-nrm x ⋉₀ ⊗₀-nrm I) .snd ; X  = ⊗₀-emb-comp (x ⊗₀ I) y
      W' = (⊗₀-nrm I ⋉₀ ⊗₀-nrm y) .snd ; X' = ⊗₀-emb-comp x (I ⊗₀ y)

      wr : s₂ .snd ≡ Ĝr Uf .snd
      wr = sym (Path.assoc X (ap (_▿₀ B) W) e₂)
         ∙ ap (X ∙_) (sym (ap-comp (_▿₀ B) W (▾₀-idn A)))

      wl : s₁ .snd ≡ Ĝl Vg .snd
      wl = sym (Path.assoc X' (ap (A ▿₀_) W') e₁)
         ∙ ap (X' ∙_) (sym (ap-comp (A ▿₀_) W' (⊗₀-emb-idn-absorb y)))

    face-r : ⊗₀-repr-unique s₂ s₀ ≡ ap (_⊗₀ y) (⊗₀-unitr x)
    face-r = sym (⊗₀-repr-∙ s₂ (Ĝr Uf) s₀)
           ∙ ap (_∙ ⊗₀-repr-unique (Ĝr Uf) s₀)
                (⊗₀-repr-refl (s₂ .snd) (Ĝr Uf .snd) wr)
           ∙ Path.unitl (⊗₀-repr-unique (Ĝr Uf) s₀)
           ∙ ⊗₀-repr-ap Ĝr Uf (⊗₀-nrm x)

    face-l : ⊗₀-repr-unique s₁ s₀ ≡ ap (x ⊗₀_) (⊗₀-unitl y)
    face-l = sym (⊗₀-repr-∙ s₁ (Ĝl Vg) s₀)
           ∙ ap (_∙ ⊗₀-repr-unique (Ĝl Vg) s₀)
                (⊗₀-repr-refl (s₁ .snd) (Ĝl Vg .snd) wl)
           ∙ Path.unitl (⊗₀-repr-unique (Ĝl Vg) s₀)
           ∙ ⊗₀-repr-ap Ĝl Vg (⊗₀-nrm y)

    triangle-weak
      : ⊗₀-repr-unique s₁ s₂ ∙ ap (_⊗₀ y) (⊗₀-unitr x)
      ≡ ap (x ⊗₀_) (⊗₀-unitl y)
    triangle-weak =
      ap (⊗₀-repr-unique s₁ s₂ ∙_) (sym face-r) ∙ ⊗₀-repr-∙ s₁ s₂ s₀ ∙ face-l

    loop-refl : is-monoidal-2-coherent M → loop ≡ refl
    loop-refl mid = ap (ap fst)
      (is-contr→is-set T-contr r₀¹ r₀² (is-⊗₀-representable-prop _ r₀¹ r₀²)
        (ap ((⊗₀-nrm x ⋉₀ ⊗₀-nrm y) ↝_)
            (ap sym (sym (mid .is-monoidal-2-coherent.is-coh₀ x y)))))

    opaque
      unfolding assoc-σ⋉₀

      face-a : is-monoidal-2-coherent M → ⊗₀-repr-unique s₁ s₂ ≡ ⊗₀-assoc x I y
      face-a mid =
          ap (λ t → ⊗₀-repr-unique (r₁ ↝ e₁) (r₂ ↝ t))
             (mid .is-monoidal-2-coherent.is-coh₀ x y)
        ∙ ↝-repr r₁ r₂ e₁

    ⊗₀-triangle
      : is-monoidal-2-coherent M
      → ⊗₀-assoc x I y ∙ ap (_⊗₀ y) (⊗₀-unitr x) ≡ ap (x ⊗₀_) (⊗₀-unitl y)
    ⊗₀-triangle mid =
      ap (_∙ ap (_⊗₀ y) (⊗₀-unitr x)) (sym (face-a mid)) ∙ triangle-weak
```

## The displaced pentagon

The level-1 pentagon in `⋉`-form: the five bracketings of a
fourfold `⋉₁` displace the level-0 witnesses `p₁`–`p₅`, the five
edges displace the `σ`s — `assoc-σ⋉₁` lines, `⋉₁`-whiskered on
the same side as at level 0 — and the square between the glued
edge composites fills by `is-prop→SquareP`: the displaced
witness spaces are contractible pointwise over the whole of
`fiber-pentagon`, one transported `⊗₁-wit-contr` per point.

The hom shadow projects through `fst`. Because the edges are
glued by `⊗₁-wit-∙`, their hom components are the `comp-pathp₂`
composites of the whiskered `assoc⋉₁` lines by construction, so
`pentagon⋉₁` is a genuine identification of associator
composites over the fiber square's shadow, the displaced image
of `pentagon⋉₀`'s core.

```agda
  module pentagon⋉₁ {F F' G G' H H' K K' : ⊗₀-composite}
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
      module P  = pentagon⋉₀ U V W X
      module P' = pentagon⋉₀ U' V' W' X'

    -- the homs the witnesses represent
    φ = Û .fst ; ψ = V̂ .fst ; χ = Ŵ .fst ; ω = X̂ .fst

    N₁ : ⊗₁-composite P.T P'.T
    N₁ = η ▿₁ ζ ▿₁ θ ▿₁ κ

    p̂₁ : ⊗₁-wit P.p₁ P'.p₁ N₁ ; p̂₁ = ((Û ⋉₁ V̂) ⋉₁ Ŵ) ⋉₁ X̂
    p̂₂ : ⊗₁-wit P.p₂ P'.p₂ N₁ ; p̂₂ = (Û ⋉₁ (V̂ ⋉₁ Ŵ)) ⋉₁ X̂
    p̂₃ : ⊗₁-wit P.p₃ P'.p₃ N₁ ; p̂₃ = Û ⋉₁ ((V̂ ⋉₁ Ŵ) ⋉₁ X̂)
    p̂₄ : ⊗₁-wit P.p₄ P'.p₄ N₁ ; p̂₄ = (Û ⋉₁ V̂) ⋉₁ (Ŵ ⋉₁ X̂)
    p̂₅ : ⊗₁-wit P.p₅ P'.p₅ N₁ ; p̂₅ = Û ⋉₁ (V̂ ⋉₁ (Ŵ ⋉₁ X̂))

    σ̂₂₁ : PathP (λ i → ⊗₁-wit (P.σ₂₁ i) (P'.σ₂₁ i) N₁) p̂₂ p̂₁
    σ̂₂₁ i = assoc-σ⋉₁ Û V̂ Ŵ i ⋉₁ X̂

    σ̂₃₂ : PathP (λ i → ⊗₁-wit (P.σ₃₂ i) (P'.σ₃₂ i) N₁) p̂₃ p̂₂
    σ̂₃₂ = assoc-σ⋉₁ Û (V̂ ⋉₁ Ŵ) X̂

    σ̂₅₃ : PathP (λ i → ⊗₁-wit (P.σ₅₃ i) (P'.σ₅₃ i) N₁) p̂₅ p̂₃
    σ̂₅₃ i = Û ⋉₁ assoc-σ⋉₁ V̂ Ŵ X̂ i

    σ̂₄₁ : PathP (λ i → ⊗₁-wit (P.σ₄₁ i) (P'.σ₄₁ i) N₁) p̂₄ p̂₁
    σ̂₄₁ = assoc-σ⋉₁ (Û ⋉₁ V̂) Ŵ X̂

    σ̂₅₄ : PathP (λ i → ⊗₁-wit (P.σ₅₄ i) (P'.σ₅₄ i) N₁) p̂₅ p̂₄
    σ̂₅₄ = assoc-σ⋉₁ Û V̂ (Ŵ ⋉₁ X̂)

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

    pentagon⋉₁
      : PathP (λ j → PathP (λ i → C.hom (P.fiber-pentagon j i .fst)
                                        (P'.fiber-pentagon j i .fst))
                     (φ ⊗₁ (ψ ⊗₁ (χ ⊗₁ ω)))
                     (((φ ⊗₁ ψ) ⊗₁ χ) ⊗₁ ω))
              (λ i → top̂ i .fst) (λ i → bot̂ i .fst)
    pentagon⋉₁ j i = fiber-pentagon₁ j i .fst
```
