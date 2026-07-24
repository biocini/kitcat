Lane Biocini
July 2026

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Coherence where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (is-contr-is-prop; is-prop→SquareP)
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
open import Core.Function.Embedding
  using (equiv→lc; image-fibers-contr→is-embedding)
open import Core.Groupoid using (sym-distr)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Op
open import Cat.Depreciated.Base

record is-2-coherent {o h} (C : category o h) : Type (o ⊔ h) where
  no-eta-equality

  private module C = category C
  private module T = theory C
  field
    is-coh
      : ∀ {x y z} (f : C.hom x y) (g : C.hom y z)
      → ap (C._▿ (C.emb g)) (T.▾-idn (C.emb f)) ≡ ap ((C.emb f) C.▿_) (T.emb-idn-absorb g)

module interchange-coh {o h} (C : category o h) where
  open category C
  open theory C

  ι-mult-r : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
             (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
           → Type (o ⊔ h)
  ι-mult-r {Cc = Cc} U V W = ap (λ X → X ▿ Cc) (interchange♭ U V) ≡ interchange♭ U (V ● W)

  ι-mult-l : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
             (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
           → Type (o ⊔ h)
  ι-mult-l {A = A} U V W = ap (λ X → A ▵ X) (interchange♭ V W) ≡ interchange♭ (U ○ V) W

  ●-coh : ∀ {x y z} {A : composite x y} {B : composite y z}
          (U : is-representable A) (V : is-representable B)
        → PathP (λ i → is-representable (interchange♭ U V i)) (U ● V) (U ○ V)
  ●-coh U V = is-prop→PathP (λ i → is-representable-prop (interchange♭ U V i)) (U ● V) (U ○ V)

  interchange-natural
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
    → ap (λ X → X ▿ Cc) (interchange♭ U V) ∙ interchange♭ (U ○ V) W
    ≡ interchange♭ (U ● V) W ∙ ap (λ X → X ▵ Cc) (interchange♭ U V)
  interchange-natural {Cc = Cc} U V W =
    Path.commutes
      (ap (λ X → X ▿ Cc) (interchange♭ U V)) (interchange♭ (U ○ V) W)
      (interchange♭ (U ● V) W) (ap (λ X → X ▵ Cc) (interchange♭ U V))
      (λ j i → interchange♭ (●-coh U V i) W j)

module _ {o h} (C : category o h) where
  open category C
  open theory C
  module pentagon● {x y z w v}
    {A : composite x y} {B : composite y z} {C : composite z w} {D : composite w v}
    (U : is-representable A) (V : is-representable B)
    (W : is-representable C) (X : is-representable D)
    where

    T : composite x v
    T = A ▿ B ▿ C ▿ D

    p₁ p₂ p₃ p₄ p₅ : is-representable T
    p₁ = ((U ● V) ● W) ● X
    p₂ = (U ● (V ● W)) ● X
    p₃ = U ● ((V ● W) ● X)
    p₄ = (U ● V) ● (W ● X)
    p₅ = U ● (V ● (W ● X))

    T-contr : is-contr (is-representable T)
    T-contr .center = p₁
    T-contr .paths  = is-representable-prop T p₁

    σ₂₁ : p₂ ≡ p₁ ; σ₂₁ i = assoc-σ● U V W i ● X
    σ₃₂ : p₃ ≡ p₂ ; σ₃₂   = assoc-σ● U (V ● W) X
    σ₅₃ : p₅ ≡ p₃ ; σ₅₃ i = U ● assoc-σ● V W X i
    σ₄₁ : p₄ ≡ p₁ ; σ₄₁   = assoc-σ● (U ● V) W X
    σ₅₄ : p₅ ≡ p₄ ; σ₅₄   = assoc-σ● U V (W ● X)

    -- opaque like the monoidal fiber-pentagon: displayed families
    -- project its slices at generic interval points, and the sealed
    -- head keeps those comparisons syntactic; the boundary still
    -- reduces by the type-directed rule
    opaque
      fiber-pentagon : σ₅₃ ∙ σ₃₂ ∙ σ₂₁ ≡ σ₅₄ ∙ σ₄₁
      fiber-pentagon = is-contr→is-set T-contr p₅ p₁ (σ₅₃ ∙ σ₃₂ ∙ σ₂₁) (σ₅₄ ∙ σ₄₁)

    -- the ∙-tree of the fiber pentagon's hom shadow, leaf by leaf:
    -- two ap-comp shuffles into the shadow, the shadow itself, one
    -- shuffle out — named so a displaced pentagon can glue over
    -- each leaf separately
    step₁ = sym (ap (ap fst σ₅₃ ∙_) (ap-comp fst σ₃₂ σ₂₁))
    step₂ = sym (ap-comp fst σ₅₃ (σ₃₂ ∙ σ₂₁))
    step₃ = ap (ap fst) fiber-pentagon
    step₄ = ap-comp fst σ₅₄ σ₄₁

    pentagon●
      : ap (U .fst ⨾_) (assoc● V W X) ∙ assoc● U (V ● W) X ∙ ap (_⨾ X .fst) (assoc● U V W)
      ≡ assoc● U V (W ● X) ∙ assoc● (U ● V) W X
    pentagon● = step₁ ∙ step₂ ∙ step₃ ∙ step₄

  -- a witness slid back along its own path: at m = i0 the slide is
  -- the witness itself (path eta), at m = i1 the normal form (the
  -- witness path's typed boundary) — both definitional, so any
  -- calculus projection applied along the slide is a nrm-
  -- straightening square with strict endpoints, and its displaced
  -- mate is the same slide one level up. The elementary transport-
  -- only form of the straightening lives in Cat.Depreciated.Coherence.Gloss.
  nrm-slide
    : ∀ {x y} {A : composite x y} (U : is-representable A) (m : I)
    → is-representable (U .snd (~ m))
  nrm-slide U m = U .fst , λ k → U .snd (k ∧ ~ m)

  assoc●-nrm
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {C : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable C)
    → assoc● U V W ≡ assoc (U .fst) (V .fst) (W .fst)
  assoc●-nrm U V W m = assoc● (nrm-slide U m) (nrm-slide V m) (nrm-slide W m)

  module pentagon {x y z w v} (f : hom x y) (g : hom y z) (h : hom z w) (k : hom w v) where
    open pentagon● (nrm f) (nrm g) (nrm h) (nrm k) public

    A₁ = assoc●-nrm (nrm f ● nrm g) (nrm h) (nrm k)   -- ≡ assoc (f ⨾ g) h k
    A₂ = assoc●-nrm (nrm f) (nrm g) (nrm h ● nrm k)   -- ≡ assoc f g (h ⨾ k)
    A₃ = assoc●-nrm (nrm f) (nrm g ● nrm h) (nrm k)   -- ≡ assoc f (g ⨾ h) k

    whisker₃ = ap (λ t → ap (f ⨾_) (assoc g h k)
                         ∙ (t ∙ ap (_⨾ k) (assoc f g h))) (sym A₃)
    whisker₂ = ap (λ t → t ∙ assoc● (nrm f ● nrm g) (nrm h) (nrm k)) A₂
    whisker₁ = ap (assoc f g (h ⨾ k) ∙_) A₁

    pentagon
      : ap (f ⨾_) (assoc g h k) ∙ assoc f (g ⨾ h) k ∙ ap (_⨾ k) (assoc f g h)
      ≡ assoc f g (h ⨾ k) ∙ assoc (f ⨾ g) h k
    pentagon = whisker₃ ∙ pentagon● ∙ whisker₂ ∙ whisker₁
```

The triangle

The unit composite `A ▿ B` carries the plain pairing `s₀` and the
two unitor-bearing pairings `sl`/`sr` — the `●`-whiskers of the
transported one-sided witnesses `Vg`/`Uf` — and every face of the
triangle is the `fst`-shadow of a propositional witness square with
wit-calculus edges. The unitor faces are squares in the one fiber,
sides constant; the associator face rides the coherence field
itself — its base square is `is-coh` transposed, its sides the
`ρ`-lines: `↝-fill` slides of the two unit absorptions,
`●`-whiskered, connecting the bracketings `r₁`/`r₂` to `sl`/`sr`
with constant `fst`. The fiber triangle is one `is-contr→is-set`,
and the tree glues shadow-by-shadow exactly as the pentagon's, so
every leaf displaces by construction. The elementary transport-only
faces live in `Cat.Depreciated.Coherence.Gloss`.

```agda
  module triangle {x y z} (f : hom x y) (g : hom y z) where
    A = emb f
    E = emb (idn y)
    B = emb g

    -- 1 = source of assoc (right-nested), 2 = target (left-nested)
    e₁ : A ▿ (E ▿ B) ≡ A ▿ B ;  e₁ = ap (A ▿_) (emb-idn-absorb g)
    e₂ : (A ▿ E) ▿ B ≡ A ▿ B ;  e₂ = ap (_▿ B) (▾-idn A)

    r₁ r₂ r₀¹ r₀² : is-representable (A ▿ E ▿ B)
    r₁  = nrm f ● (nrm (idn y) ● nrm g)      -- fst = f ⨾ (idn y ⨾ g)
    r₂  = (nrm f ● nrm (idn y)) ● nrm g      -- fst = (f ⨾ idn y) ⨾ g
    r₀¹ = (nrm f ● nrm g) ↝ sym e₁
    r₀² = (nrm f ● nrm g) ↝ sym e₂

    T-contr : is-contr (is-representable (A ▿ E ▿ B))
    T-contr .center = r₁
    T-contr .paths  = is-representable-prop _ r₁

    -- the loop σ-line, sealed like the unitor σ-lines: the loop is
    -- its fst-shadow, and the fiber square behind loop-refl gets
    -- sealed faces — families over that square never expose the
    -- propositionality body
    opaque
      σ-loop : r₀¹ ≡ r₀²
      σ-loop = is-representable-prop _ r₀¹ r₀²

    loop : f ⨾ g ≡ f ⨾ g
    loop = ap fst σ-loop

    Uf : is-representable A ; Uf = (nrm f ● nrm (idn y)) ↝ ▾-idn A
    Vg : is-representable B ; Vg = (nrm (idn y) ● nrm g) ↝ emb-idn-absorb g

    s₀ sl sr : is-representable (A ▿ B)
    s₀ = nrm f ● nrm g
    sl = nrm f ● Vg              -- fst = f ⨾ (idn y ⨾ g)
    sr = Uf ● nrm g              -- fst = (f ⨾ idn y) ⨾ g

    -- opaque like assoc-σ●: the tree and the displayed witness
    -- families only ever read their boundaries off the types, and
    -- the sealed heads keep the fiber comparisons syntactic; the
    -- displaced mates are repr-σᴰ[_] instances at these sealed
    -- lines, no unfolding
    opaque
      σₗᵣ : sl ≡ sr ; σₗᵣ = is-representable-prop _ sl sr
      σᵣ₀ : sr ≡ s₀ ; σᵣ₀ = is-representable-prop _ sr s₀
      σₗ₀ : sl ≡ s₀ ; σₗ₀ = is-representable-prop _ sl s₀

    -- fst-constant lines from the bracketings to the pairings,
    -- riding e₂/e₁: the ↝-fill slides of the two unit absorptions,
    -- ●-whiskered on the untouched side
    ρr : (m : I) → is-representable (e₂ m)
    ρr m = ↝-fill (nrm f ● nrm (idn y)) (▾-idn A) m ● nrm g

    ρl : (m : I) → is-representable (e₁ m)
    ρl m = nrm f ● ↝-fill (nrm (idn y) ● nrm g) (emb-idn-absorb g) m

    -- the unitor faces: squares in the one fiber, sides constant,
    -- bottom the ●-whisker of the unitor σ-line — the shadow's
    -- bottom edge is the whiskered unitor definitionally. Opaque
    -- like fiber-pentagon: displayed witness families project their
    -- slices under generic interval binders, and the sealed heads
    -- keep those comparisons syntactic; the boundary still reduces
    -- by the type-directed rule
    opaque
      face-σr : SquareP (λ _ _ → is-representable (A ▿ B))
                σᵣ₀ refl (λ i → unitr-σ● f i ● nrm g) refl
      face-σr = is-prop→SquareP (λ _ _ → is-representable-prop (A ▿ B))
                  σᵣ₀ refl (λ i → unitr-σ● f i ● nrm g) refl

      face-σl : SquareP (λ _ _ → is-representable (A ▿ B))
                σₗ₀ refl (λ i → nrm f ● unitl-σ● g i) refl
      face-σl = is-prop→SquareP (λ _ _ → is-representable-prop (A ▿ B))
                  σₗ₀ refl (λ i → nrm f ● unitl-σ● g i) refl

    face-r : ap fst σᵣ₀ ≡ ap (_⨾ g) (unitr f)
    face-r m i = face-σr m i .fst

    face-l : ap fst σₗ₀ ≡ ap (f ⨾_) (unitl g)
    face-l m i = face-σl m i .fst

    -- the associator face: the witness square over the transposed
    -- coherence field, sides the ρ-lines, bottom the sealed
    -- assoc-σ● — its shadow lands on assoc with no unfolding
    opaque
      face-σa
        : (mid : is-2-coherent C)
        → SquareP (λ m i → is-representable
                             (mid .is-2-coherent.is-coh f g (~ i) (~ m)))
          σₗᵣ (λ m → ρl (~ m))
          (assoc-σ● (nrm f) (nrm (idn y)) (nrm g))
          (λ m → ρr (~ m))
      face-σa mid =
        is-prop→SquareP
          (λ m i → is-representable-prop
                     (mid .is-2-coherent.is-coh f g (~ i) (~ m)))
          σₗᵣ (λ m → ρl (~ m))
          (assoc-σ● (nrm f) (nrm (idn y)) (nrm g))
          (λ m → ρr (~ m))

    face-a : is-2-coherent C → ap fst σₗᵣ ≡ assoc f (idn y) g
    face-a mid m i = face-σa mid m i .fst

    -- opaque like fiber-pentagon: displayed witness families project
    -- its slices under generic interval binders; the boundary still
    -- reduces by the type-directed rule
    opaque
      fiber-triangle : σₗᵣ ∙ σᵣ₀ ≡ σₗ₀
      fiber-triangle = is-contr→is-set (rep-contr s₀) sl s₀ (σₗᵣ ∙ σᵣ₀) σₗ₀

    -- the ∙-tree of the triangle, leaf by leaf: the associator and
    -- unitr whiskers into the fiber, one ap-comp shuffle, the fiber
    -- triangle's shadow, the unitl face out
    step₁ = sym (ap-comp fst σₗᵣ σᵣ₀)
    step₂ = ap (ap fst) fiber-triangle
    whisker-r = ap (ap fst σₗᵣ ∙_) (sym face-r)

    whisker-a
      : (mid : is-2-coherent C)
      → assoc f (idn y) g ∙ ap (_⨾ g) (unitr f)
      ≡ ap fst σₗᵣ ∙ ap (_⨾ g) (unitr f)
    whisker-a mid = ap (_∙ ap (_⨾ g) (unitr f)) (sym (face-a mid))

    triangle-weak : ap fst σₗᵣ ∙ ap (_⨾ g) (unitr f) ≡ ap (f ⨾_) (unitl g)
    triangle-weak = whisker-r ∙ step₁ ∙ step₂ ∙ face-l

    triangle : is-2-coherent C
             → assoc f (idn y) g ∙ ap (_⨾ g) (unitr f) ≡ ap (f ⨾_) (unitl g)
    triangle mid = whisker-a mid ∙ triangle-weak

    -- the fiber square behind the loop: the σ-line against the
    -- is-coh-transport line. Opaque like fiber-triangle: displayed
    -- witness families project its slices under generic interval
    -- binders; the boundary still reduces by the type-directed rule
    opaque
      loop-sq
        : (mid : is-2-coherent C)
        → σ-loop
        ≡ ap ((nrm f ● nrm g) ↝_)
             (ap sym (sym (mid .is-2-coherent.is-coh f g)))
      loop-sq mid =
        is-contr→is-set T-contr r₀¹ r₀² σ-loop
          (ap ((nrm f ● nrm g) ↝_)
              (ap sym (sym (mid .is-2-coherent.is-coh f g))))

    loop-refl : is-2-coherent C → loop ≡ refl
    loop-refl mid = ap (ap fst) (loop-sq mid)
```

```agda
  ▾-idn-▿ : ∀ {x y z} (A : composite x y) (B : composite y z)
           → ▾-idn (A ▿ B) ≡ ap (A ▿_) (▾-idn B)
  ▾-idn-▿ A B = refl

  idn-▿ : ∀ {x y} {A : composite x y} → is-representable A → emb (idn x) ▿ A ≡ A
  idn-▿ U = interchange♭ (nrm (idn _)) U ∙ idn-▴ _      -- emb-idn-absorb f ≐ idn-▿ (nrm f)

module op-coh {o h} (C : category o h) where
  open category C
  open theory C
  open interchange-coh C
  open op C using (σ; σ'; ⟲; ⟳)
  private
    module Cᵒ = category (op C)
    module Tᵒ = theory  (op C)
    module Iᵒ = interchange-coh (op C)

  private
    ▿-op : ∀ {x y z} (X : Cᵒ.composite x y) (Y : Cᵒ.composite y z)
          → (X Cᵒ.▿ Y) ≡ ⟲ (⟳ Y ▵ ⟳ X)
    ▿-op _ _ = refl

    ▵-op : ∀ {x y z} (X : Cᵒ.composite x y) (Y : Cᵒ.composite y z)
           → (X Cᵒ.▵ Y) ≡ ⟲ (⟳ Y ▿ ⟳ X)
    ▵-op _ _ = refl

    ▵-assoc : ∀ {x y z w} (β : composite x y) (α : composite y z) (δ : composite z w)
              → (β ▵ α) ▵ δ ≡ β ▵ (α ▵ δ)
    ▵-assoc _ _ _ = refl

    ▿-is-▾     : ∀ {x y z} (α : composite x y) (g : hom y z) → (α ▿ emb g) ≡ (α ▾ g)
    ▿-is-▾     _ _ = refl

    ▵-is-▴  : ∀ {x y z} (f : hom x y) (α : composite y z) → (emb f ▵ α) ≡ (f ▴ α)
    ▵-is-▴  _ _ = refl

    mirror-lhs : ∀ {x y z} (f : hom x y) (g : hom y z)
      → ((Cᵒ.emb g Cᵒ.▿ Cᵒ.emb (Cᵒ.idn y)) Cᵒ.▿ Cᵒ.emb f)
      ≡ ⟲ (emb f ▵ emb (idn y) ▵ emb g)
    mirror-lhs _ _ = refl

    mirror-rhs : ∀ {x y z} (f : hom x y) (g : hom y z)
      → (Cᵒ.emb g Cᵒ.▿ Cᵒ.emb f) ≡ ⟲ (emb f ▵ emb g)
    mirror-rhs _ _ = refl

  emb-▴-idn : ∀ {x y} (f : hom x y) → (f ▴ emb (idn y)) ≡ emb f
  emb-▴-idn {y = y} f = sym (interchange f (idn y)) ∙ ▾-idn (emb f)

  is-2-coherent'' : ∀ {x y z} (f : hom x y) (g : hom y z) → Type (o ⊔ h)
  is-2-coherent'' {y = y} f g = ap (emb f ▵_) (idn-▴ (emb g)) ≡ ap (_▵ emb g) (emb-▴-idn f)

  private
    ⨾-op : ∀ {x y z} (f : hom x y) (g : hom y z) → (g Tᵒ.⨾ f) ≡ (f ⨾ g)
    ⨾-op _ _ = refl

    emb-comp-op-check : ∀ {x y z} (f : hom x y) (g : hom y z)
                      → Tᵒ.emb-comp g f ≡ ap ⟲ (emb-comp-op f g)
    emb-comp-op-check _ _ = refl

    emb-comp-check : ∀ {x y z} (f : hom x y) (g : hom y z)
                   → Tᵒ.emb-comp-op g f ≡ ap ⟲ (emb-comp f g)
    emb-comp-check _ _ = refl

    interchange-op : ∀ {x y z} (f : hom x y) (g : hom y z)
                   → Cᵒ.interchange g f ≡ ap ⟲ (sym (interchange f g))
    interchange-op _ _ = refl

    pre-distr-op : ∀ {x y z} (f : hom x y) (g : hom y z) {w} (a : hom w x)
                 → Tᵒ.pre-distr g f a ≡ post-distr f g a
    pre-distr-op _ _ _ = refl

    ce-pre-op : ∀ {x y z} (f : hom x y) (g : hom y z)
              → Tᵒ.comp-eq-pre g f ≡ comp-eq-post f g
    ce-pre-op f g = sym (Path.assoc _ _ _)

    ce-post-op : ∀ {x y z} (f : hom x y) (g : hom y z)
               → Tᵒ.comp-eq-post g f ≡ comp-eq-pre f g
    ce-post-op f g = Path.assoc _ _ _

    pip-op : ∀ {x y z} (f : hom x y) (g : hom y z)
           → Tᵒ.pre-is-post g f ≡ sym (pre-is-post f g)
    pip-op f g =
        ap (λ t → sym t ∙ Tᵒ.comp-eq-post g f) (ce-pre-op f g)
      ∙ ap (sym (comp-eq-post f g) ∙_) (ce-post-op f g)
      ∙ sym (sym-distr (sym (comp-eq-pre f g)) (comp-eq-post f g))

  absorb-l-op : ∀ {x v} (b : Cᵒ.hom x v) → Tᵒ.absorb-l b ≡ absorb-r b
  absorb-l-op {x} b = ap (_∙ unit b) (pip-op b (idn x))

  absorb-r-op : ∀ {w x} (a : Cᵒ.hom w x) → Tᵒ.absorb-r a ≡ absorb-l a
  absorb-r-op {x = x} a = ap (_∙ unit a) (ap sym (pip-op (idn x) a) ∙ refl)

  bridge-l : ∀ {y z} (g : hom y z) → Tᵒ.▾-idn (Cᵒ.emb g) ≡ ap ⟲ (idn-▴ (emb g))
  bridge-l g i = funext λ γ →
    ap (λ β → Cᵒ.emb g (γ .fst , β))
       (ap (γ .snd .fst ,_) (absorb-l-op (γ .snd .snd) i))

  bridge-idn : ∀ {x y} (β : Cᵒ.composite x y) → Tᵒ.idn-▴ β ≡ ap ⟲ (▾-idn (⟳ β))
  bridge-idn β i = funext λ γ →
    ap (λ α → β (α , γ .snd))
       (ap (γ .fst .fst ,_) (absorb-r-op (γ .fst .snd) i))

  bridge-r : ∀ {x y} (f : hom x y) → Tᵒ.emb-idn-absorb f ≡ ap ⟲ (emb-▴-idn f)
  bridge-r {y = y} f =
      ap (ap ⟲ (sym (interchange f (idn y))) ∙_) (bridge-idn (Cᵒ.emb f))
    ∙ sym (ap-comp ⟲ (sym (interchange f (idn y))) (▾-idn (emb f)))

  -- 2-coh→ : ∀ {x y z} (f : hom x y) (g : hom y z)
  --        → is-2-coherent'' f g → is-2-coherent Tᵒ g f
  -- 2-coh→ f g mid =
  --     ap (ap (Cᵒ._▿ Cᵒ.emb f)) (bridge-l g)
  --   ∙ ap (ap ⟲) mid
  --   ∙ sym (ap (ap (Cᵒ.emb g Cᵒ.▿_)) (bridge-r f))

  -- 2-coh← : ∀ {x y z} (f : hom x y) (g : hom y z)
  --        → Tᵒ.triangle.is-2-coherent g f → is-2-coherent'' f g
  -- 2-coh← f g midᵒ = ap (ap ⟳)
  --   ( sym (ap (ap (Cᵒ._▿ Cᵒ.emb f)) (bridge-l g))
  --   ∙ midᵒ
  --   ∙ ap (ap (Cᵒ.emb g Cᵒ.▿_)) (bridge-r f) )

  rep-op  : ∀ {x y} {α : composite y x} → is-representable α → Cᵒ.is-representable (⟲ α)
  rep-op  (k , p) = k , ap ⟲ p

  rep-op' : ∀ {x y} {α : composite y x} → Cᵒ.is-representable (⟲ α) → is-representable α
  rep-op' (k , p) = k , ap ⟳ p

  rep-op-invol : ∀ {x y} {α : composite y x} (U : is-representable α) → rep-op' (rep-op U) ≡ U
  rep-op-invol _ = refl

  -- the op mirror of a witness line, generalized over the line:
  -- κ is consumed as a neutral family and rep-op' preserves fst
  -- definitionally, so instances at sealed σ-heads need no unfolding
  repr-op[_] : ∀ {x y} {α : composite y x} {Uᵒ Vᵒ : Cᵒ.is-representable (⟲ α)}
             → (κ : Uᵒ ≡ Vᵒ) → ap fst κ ≡ repr-unique (rep-op' Uᵒ) (rep-op' Vᵒ)
  repr-op[ κ ] = repr-lc (ap rep-op' κ)

  repr-sym : ∀ {x y} {α : composite x y} (U V : is-representable α)
           → sym (repr-unique U V) ≡ repr-unique V U
  repr-sym U V = repr-lc (sym (is-representable-prop _ U V))

  -- both unitors are fst-shadows of sealed σ-lines: repr-op[_] reads
  -- the op line, repr-lc the plain one, and repr-cast carries the
  -- op-bridge between the two stated witnesses — the seals stay shut
  unitr-op : ∀ {x y} (f : Cᵒ.hom x y) → Tᵒ.unitr f ≡ unitl f
  unitr-op {x} {y} f =
      repr-op[ Tᵒ.unitr-σ● f ]
    ∙ repr-cast (nrm f) wit
    ∙ sym (repr-lc (unitl-σ● f))
    where
      Q₀ : emb (idn y ⨾ f) ≡ idn y ▴ emb f
      Q₀ = emb-comp-op (idn y) f
      Q : emb (idn y ⨾ f) ≡ emb (idn y) ▾ f
      Q = emb-comp (idn y) f
      ι : emb (idn y) ▾ f ≡ idn y ▴ emb f
      ι = interchange (idn y) f
      U : idn y ▴ emb f ≡ emb f
      U = idn-▴ (emb f)

      P₁ : is-representable (emb f)
      P₁ = rep-op' ((Cᵒ.nrm f Tᵒ.● Cᵒ.nrm (idn y)) Tᵒ.↝ Tᵒ.▾-idn (Cᵒ.emb f))
      P₂ : is-representable (emb f)
      P₂ = (nrm (idn y) ● nrm f) ↝ emb-idn-absorb f

      wit : P₁ .snd ≡ P₂ .snd
      wit =
        begin
          ap ⟳ ((ap ⟲ Q₀ ∙ refl) ∙ Tᵒ.▾-idn (Cᵒ.emb f))
            ≡⟨ ap (λ t → ap ⟳ ((ap ⟲ Q₀ ∙ refl) ∙ t)) (bridge-l f) ⟩
          ap ⟳ ((ap ⟲ Q₀ ∙ refl) ∙ ap ⟲ U)
            ≡⟨ ap-comp ⟳ (ap ⟲ Q₀ ∙ refl) (ap ⟲ U) ⟩
          ap ⟳ (ap ⟲ Q₀ ∙ refl) ∙ U
            ≡⟨ ap (_∙ U) (ap-comp ⟳ (ap ⟲ Q₀) refl) ⟩
          (Q₀ ∙ refl) ∙ U      ≡⟨ ap (_∙ U) (Path.unitr Q₀) ⟩
          Q₀ ∙ U               ≡˘⟨ ap (_∙ U) (coh→∙ (idn y) f) ⟩
          (Q ∙ ι) ∙ U          ≡˘⟨ Path.assoc Q ι U ⟩
          Q ∙ (ι ∙ U)          ≡˘⟨ ap (_∙ (ι ∙ U)) (Path.unitr Q) ⟩
          (Q ∙ refl) ∙ (ι ∙ U)
        ∎

  ⟲-∙ : ∀ {x y} {α β γ : composite y x} (p : α ≡ β) (q : β ≡ γ)
      → ap ⟲ (p ∙ q) ≡ ap ⟲ p ∙ ap ⟲ q
  ⟲-∙ _ _ = refl

  ⟳-∙ : ∀ {x y} {α β γ : Cᵒ.composite x y} (p : α ≡ β) (q : β ≡ γ)
      → ap ⟳ (p ∙ q) ≡ ap ⟳ p ∙ ap ⟳ q
  ⟳-∙ _ _ = refl

  ⟲-sym : ∀ {x y} {α β : composite y x} (p : α ≡ β) → ap ⟲ (sym p) ≡ sym (ap ⟲ p)
  ⟲-sym _ = refl

  ⟳⟲-ap : ∀ {x y} {α β : composite y x} (p : α ≡ β) → ap ⟳ (ap ⟲ p) ≡ p
  ⟳⟲-ap _ = refl

  T'-op : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → (Cᵒ.emb h Cᵒ.▿ Cᵒ.emb g Cᵒ.▿ Cᵒ.emb f) ≡ ⟲ (emb f ▵ emb g ▵ emb h)
  T'-op _ _ _ = refl


  M-assoc : ∀ {x y z w} (A : composite x y) (B : composite y z) (Cc : composite z w)
          → (A ▵ B) ▿ Cc ≡ A ▵ (B ▿ Cc)
  M-assoc _ _ _ = refl        -- bimod, generalized

  ●-op : ∀ {x y z} {A : composite x y} {B : composite y z}
         (U : is-representable A) (V : is-representable B)
       → rep-op' (rep-op V Tᵒ.● rep-op U) ≡ (U ○ V)
  ●-op _ _ = refl

  ι-square
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
    → PathP (λ i → interchange♭ (U ● V) W i ≡ interchange♭ (U ○ V) W i)
        (ap (λ X → X ▿  Cc) (interchange♭ U V))
        (ap (λ X → X ▵ Cc) (interchange♭ U V))
  ι-square U V W j i = interchange♭ (●-coh U V i) W j

  is-3-coherent
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
    → Type (o ⊔ h)
  is-3-coherent {A = A} {Cc = Cc} U V W =
      interchange♭ U (V ● W) ∙ ap (λ X → A ▵ X) (interchange♭ V W)
    ≡ interchange♭ (U ● V) W ∙ ap (λ X → X ▵ Cc) (interchange♭ U V)

  mult→3coh
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
    → ι-mult-r U V W → ι-mult-l U V W → is-3-coherent U V W
  mult→3coh {A = A} {Cc = Cc} U V W mr ml =
      ap (λ t → t ∙ ap (λ X → A ▵ X) (interchange♭ V W)) (sym mr)
    ∙ ap (λ t → ap (λ X → X ▿ Cc) (interchange♭ U V) ∙ t) ml
    ∙ interchange-natural U V W


  ○-op : ∀ {x y z} {A : composite x y} {B : composite y z}
           (U : is-representable A) (V : is-representable B)
         → rep-op' (rep-op V Tᵒ.○ rep-op U) ≡ (U ● V)
  ○-op _ _ = refl

  ι-mult-r-op
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
    → ι-mult-l U V W → Iᵒ.ι-mult-r (rep-op W) (rep-op V) (rep-op U)
  ι-mult-r-op U V W m = ap (λ t → ap ⟲ (sym t)) m

  ι-mult-l-op
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
    → ι-mult-r U V W → Iᵒ.ι-mult-l (rep-op W) (rep-op V) (rep-op U)
  ι-mult-l-op U V W m = ap (λ t → ap ⟲ (sym t)) m


  ι-can : ∀ {x y z} {A : composite x y} {B : composite y z}
          (U : is-representable A) (V : is-representable B) → A ▿ B ≡ A ▵ B
  ι-can U V = sym ((U ● V) .snd) ∙ (U ○ V) .snd

  ι-can-is-ι : ∀ {x y z} {A : composite x y} {B : composite y z}
               (U : is-representable A) (V : is-representable B)
             → ι-can U V ≡ interchange♭ U V
  ι-can-is-ι (m , p) (n , q) =
    J (λ _ q' → ι-can (m , p) (n , q') ≡ interchange♭ (m , p) (n , q'))
      (J (λ _ p' → ι-can (m , p') (nrm n) ≡ interchange♭ (m , p') (nrm n)) base p) q
    where
      X = emb-comp m n ; Y = emb-comp-op m n ; ι = interchange m n
      base : sym (X ∙ refl) ∙ (Y ∙ refl) ≡ ι
      base = ap (λ t → sym t ∙ (Y ∙ refl)) (Path.unitr X)
           ∙ ap (λ t → sym X ∙ t) (Path.unitr Y)
           ∙ ap (λ t → sym X ∙ t) (sym (coh→∙ m n))
           ∙ Path.assoc (sym X) X ι
           ∙ ap (_∙ ι) (Path.invl X)
           ∙ Path.unitl ι

record category-3-coherent {o h} (C : category o h) : Type (o ⊔ h) where
  open category C
  open theory C
  open interchange-coh C

  field
    interchange-rcomp
      : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
        (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
      → ap (λ X → X ▿ Cc) (interchange♭ U V) ≡ interchange♭ U (V ● W)

    interchange-lcomp
      : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
        (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
      → ap (λ X → A ▵ X) (interchange♭ V W) ≡ interchange♭ (U ○ V) W

  -- The two double-slides agree: T' → M₁ → T'' equals T' → N → T''.
  interchange-square
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
    → interchange♭ U (V ● W) ∙ ap (λ X → A ▵ X) (interchange♭ V W)
    ≡ interchange♭ (U ● V) W ∙ ap (λ X → X ▵ Cc) (interchange♭ U V)
  interchange-square {A = A} {Cc = Cc} U V W =
      ap (λ t → t ∙ ap (λ X → A ▵ X) (interchange♭ V W))
         (sym (interchange-rcomp U V W))
    ∙ ap (λ t → ap (λ X → X ▿ Cc) (interchange♭ U V) ∙ t)
         (interchange-lcomp U V W)
    ∙ interchange-natural U V W
```
