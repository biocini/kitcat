Lane Biocini
July 2026

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Coherence where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
open import Core.Function.Embedding
  using (equiv→lc; image-fibers-contr→is-embedding)
open import Core.Groupoid using (sym-distr)

open import Cat.Type
open import Cat.Op
open import Cat.Base

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
  ι-mult-r {Cc = Cc} U V W =
    ap (λ X → X ▿ Cc) (interchange♭ U V) ≡ interchange♭ U (V ● W)

  ι-mult-l : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
             (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
           → Type (o ⊔ h)
  ι-mult-l {A = A} U V W =
    ap (λ X → A ▵ X) (interchange♭ V W) ≡ interchange♭ (U ○ V) W

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
  -- only form of the straightening lives in Cat.Coherence.Gloss.
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

```

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

    opaque
      unfolding assoc-σ●

      assoc-eq : repr-unique r₁ r₂ ≡ assoc f (idn y) g
      assoc-eq = refl

    loop : f ⨾ g ≡ f ⨾ g
    loop = repr-unique r₀¹ r₀²

    Uf : is-representable A ; Uf = (nrm f ● nrm (idn y)) ↝ ▾-idn A
    Vg : is-representable B ; Vg = (nrm (idn y) ● nrm g) ↝ emb-idn-absorb g

    s₀ s₁ s₂ : is-representable (A ▿ B)
    s₀ = nrm f ● nrm g          ;  s₁ = r₁ ↝ e₁  ;  s₂ = r₂ ↝ e₂

    Ĝr : is-representable A → is-representable (A ▿ B) ; Ĝr u = u ● nrm g
    Ĝl : is-representable B → is-representable (A ▿ B) ; Ĝl v = nrm f ● v

    private
      W  = (nrm f ● nrm (idn y)) .snd ; X  = emb-comp (f ⨾ idn y) g
      W' = (nrm (idn y) ● nrm g) .snd ; X' = emb-comp f (idn y ⨾ g)

      wr : s₂ .snd ≡ Ĝr Uf .snd
      wr = sym (Path.assoc X (ap (_▿ B) W) e₂)
         ∙ ap (X ∙_) (sym (ap-comp (_▿ B) W (▾-idn A)))

      wl : s₁ .snd ≡ Ĝl Vg .snd
      wl = sym (Path.assoc X' (ap (A ▿_) W') e₁)
         ∙ ap (X' ∙_) (sym (ap-comp (A ▿_) W' (emb-idn-absorb g)))

    face-r : repr-unique s₂ s₀ ≡ ap (_⨾ g) (unitr f)
    face-r = sym (repr-∙ s₂ (Ĝr Uf) s₀)
           ∙ ap (_∙ repr-unique (Ĝr Uf) s₀) (repr-refl (s₂ .snd) (Ĝr Uf .snd) wr)
           ∙ Path.unitl (repr-unique (Ĝr Uf) s₀)
           ∙ repr-ap Ĝr Uf (nrm f)

    face-l : repr-unique s₁ s₀ ≡ ap (f ⨾_) (unitl g)
    face-l = sym (repr-∙ s₁ (Ĝl Vg) s₀)
           ∙ ap (_∙ repr-unique (Ĝl Vg) s₀) (repr-refl (s₁ .snd) (Ĝl Vg .snd) wl)
           ∙ Path.unitl (repr-unique (Ĝl Vg) s₀)
           ∙ repr-ap Ĝl Vg (nrm g)

    triangle-weak : repr-unique s₁ s₂ ∙ ap (_⨾ g) (unitr f) ≡ ap (f ⨾_) (unitl g)
    triangle-weak = ap (repr-unique s₁ s₂ ∙_) (sym face-r) ∙ repr-∙ s₁ s₂ s₀ ∙ face-l

    loop-refl : is-2-coherent C → loop ≡ refl
    loop-refl mid = ap (ap fst)
      (is-contr→is-set T-contr r₀¹ r₀² (is-representable-prop _ r₀¹ r₀²)
         (ap ((nrm f ● nrm g) ↝_) (ap sym (sym (mid .is-2-coherent.is-coh f g)))))


    opaque
      unfolding assoc-σ●

      face-a : is-2-coherent C → repr-unique s₁ s₂ ≡ assoc f (idn y) g
      face-a mid = ap (λ t → repr-unique (r₁ ↝ e₁) (r₂ ↝ t)) (mid .is-2-coherent.is-coh f g) ∙ ↝-repr r₁ r₂ e₁

    triangle : is-2-coherent C
             → assoc f (idn y) g ∙ ap (_⨾ g) (unitr f) ≡ ap (f ⨾_) (unitl g)
    triangle mid = ap (_∙ ap (_⨾ g) (unitr f)) (sym (face-a mid)) ∙ triangle-weak


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
  is-2-coherent'' {y = y} f g =
    ap (emb f ▵_) (idn-▴ (emb g)) ≡ ap (_▵ emb g) (emb-▴-idn f)

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
  absorb-r-op {x = x} a =
    ap (_∙ unit a) (ap sym (pip-op (idn x) a) ∙ refl)

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

  repr-op : ∀ {x y} {α : composite y x} (U V : is-representable α)
          → Tᵒ.repr-unique (rep-op U) (rep-op V) ≡ repr-unique U V
  repr-op {α = α} U V =
    repr-lc (ap rep-op' (Tᵒ.is-representable-prop (⟲ α) (rep-op U) (rep-op V)))

  repr-sym : ∀ {x y} {α : composite x y} (U V : is-representable α)
           → sym (repr-unique U V) ≡ repr-unique V U
  repr-sym U V = repr-lc (sym (is-representable-prop _ U V))

  unitr-op : ∀ {x y} (f : Cᵒ.hom x y) → Tᵒ.unitr f ≡ unitl f
  unitr-op {x} {y} f =
      repr-op P₁ (nrm f)
    ∙ sym (repr-∙ P₁ P₂ (nrm f))
    ∙ ap (_∙ repr-unique P₂ (nrm f)) (repr-refl (P₁ .snd) (P₂ .snd) wit)
    ∙ Path.unitl (repr-unique P₂ (nrm f))
    where
      Q₀ = emb-comp-op (idn y) f ; Q = emb-comp (idn y) f
      ι  = interchange (idn y) f ; U = idn-▴ (emb f)

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
