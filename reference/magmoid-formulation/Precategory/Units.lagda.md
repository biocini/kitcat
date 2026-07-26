Lane Biocini, February 2025

Idempotent equivalences and unit characterization.
Propositional identity structure without hom-set assumption.

References:
- Kraus, "Internal ∞-Categorical Models of Dependent Type Theory"
- Chen, "Semicategories with Identities"
- Capriotti-Kraus, "Univalent Higher Categories via Complete Semi-Segal Types"

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Units where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel
open import Core.Kan hiding (assoc; unitl; unitr)
open import Core.Transport
open import Core.Equiv

open import Cat.Base

private variable
  u v : Level

module unit-defs {u v} (C : precategory u v) where
  private module C = Cat C
  open C using (ob; hom; _⨾_; is-eqv)

  is-idempotent : ∀ {x} → hom x x → Type v
  is-idempotent i = i ≡ i ⨾ i

  record is-idem-equiv {x} (i : hom x x) : Type (u ⊔ v) where
    no-eta-equality
    field
      idem : is-idempotent i
      eqv  : is-eqv i

  {-# INLINE is-idem-equiv.constructor #-}

  has-iso-lcoh : ∀ {x} {i : hom x x} → is-eqv i → Type v
  has-iso-lcoh {i = i} e = C.iso-inv.runit e ≡ i

  has-iso-rcoh : ∀ {x} {i : hom x x} → is-eqv i → Type v
  has-iso-rcoh {i = i} e = C.iso-inv.lunit e ≡ i

  record is-coherent-unit {x} (i : hom x x) : Type (u ⊔ v) where
    no-eta-equality
    field
      eqv  : is-eqv i
      lcoh : has-iso-lcoh eqv
      rcoh : has-iso-rcoh eqv

  {-# INLINE is-coherent-unit.constructor #-}

module idem-equiv-coh {u v} (C : precategory u v) where
  private module C = Cat C
  open C
  open unit-defs C

  module _ {x} {i : hom x x} (e : is-eqv i) (p : is-idempotent i) where
    open iso-inv e

    c0 : fiber (i ⨾_) i
    c0 = Equiv.c ((i ⨾_) , e .fst) i

    c1 : fiber (_⨾ i) i
    c1 = Equiv.c ((_⨾ i) , e .snd) i

    h0 : hom x x
    h0 = c0 .fst

    p0 : i ⨾ h0 ≡ i
    p0 = c0 .snd

    h1 : hom x x
    h1 = c1 .fst

    p1 : h1 ⨾ i ≡ i
    p1 = c1 .snd

    f0 : Path (fiber (i ⨾_) i) c0 (i , sym p)
    f0 = Equiv.fibers ((i ⨾_) , e .fst) (i , sym p)

    f1 : Path (fiber (_⨾ i) i) c1 (i , sym p)
    f1 = Equiv.fibers ((_⨾ i) , e .snd) (i , sym p)

    α0 : h0 ≡ i
    α0 = ap fst f0

    α1 : h1 ≡ i
    α1 = ap fst f1

    has-rcoh : has-iso-rcoh e
    has-rcoh = α0

    has-lcoh : has-iso-lcoh e
    has-lcoh = α1

  idem-equiv→coherent : ∀ {x} {i : hom x x} → is-idem-equiv i → is-coherent-unit i
  idem-equiv→coherent {i = i} ie .is-coherent-unit.eqv = ie .is-idem-equiv.eqv
  idem-equiv→coherent {i = i} ie .is-coherent-unit.lcoh = has-lcoh (ie .is-idem-equiv.eqv) (ie .is-idem-equiv.idem)
  idem-equiv→coherent {i = i} ie .is-coherent-unit.rcoh = has-rcoh (ie .is-idem-equiv.eqv) (ie .is-idem-equiv.idem)

module coherent→idem {u v} (C : precategory u v) where
  private module C = Cat C
  open C using (ob; hom; _⨾_; is-eqv)
  open unit-defs C

  module _ {x} {i : hom x x} (e : is-eqv i) (lcoh : has-iso-lcoh e) (rcoh : has-iso-rcoh e) where
    private module inv = C.iso-inv e

    rpre : i ⨾ inv.lunit ≡ i
    rpre = inv.pre-counit i

    lpost : inv.runit ⨾ i ≡ i
    lpost = inv.post-counit i

    w0 : i ⨾ i ≡ i
    w0 = ap (i ⨾_) (sym rcoh) ∙ rpre

    w1 : i ⨾ i ≡ i
    w1 = ap (_⨾ i) (sym lcoh) ∙ lpost

    -- Construct idempotence via the fiber path
    -- (i ⨾ i, w0) and (i ⨾ i, w1) are in fiber id i
    -- Since fiber id i ≃ (i ⨾ i ≡ i) and both paths exist, we get idem
    fib-center : fiber id i
    fib-center = i , refl

    fib0 : fiber id i
    fib0 = i ⨾ i , w0

    fib1 : fiber id i
    fib1 = i ⨾ i , w1

    -- Actually, simpler: w0 and w1 both prove i ⨾ i ≡ i
    -- So i ⨾ i ≡ i holds, which is idempotence
    idem : is-idempotent i
    idem = sym w0

  coherent→idem-equiv : ∀ {x} {i : hom x x} → is-coherent-unit i → is-idem-equiv i
  coherent→idem-equiv {i = i} cu .is-idem-equiv.idem = idem (cu .is-coherent-unit.eqv) (cu .is-coherent-unit.lcoh) (cu .is-coherent-unit.rcoh)
  coherent→idem-equiv {i = i} cu .is-idem-equiv.eqv = cu .is-coherent-unit.eqv

module unit-unique {u v} (C : precategory u v) where
  private module C = Cat C
  open C
  open unit-defs C

  idem-equiv-unique : ∀ {x} {i₁ i₂ : hom x x}
    → is-idem-equiv i₁ → is-idem-equiv i₂ → i₁ ≡ i₂
  idem-equiv-unique {i₁ = i₁} {i₂} ie₁ ie₂ =
    sym (idn.rneutral (ie₂ .is-idem-equiv.eqv) (ie₂ .is-idem-equiv.idem) i₁)
    ∙ idn.lneutral (ie₁ .is-idem-equiv.eqv) (ie₁ .is-idem-equiv.idem) i₂

-- Kraus Theorem 3.1.9: idempotence is propositional for equivalences
-- Chen, "Semicategories with Identities", Section 3.3
module idem-is-prop {u v} (C : precategory u v) where
  private module C = Cat C
  open C hiding (lunit; runit)
  open unit-defs C

  -- Chen diagonal approach:
  -- For any idempotence p, the fiber path gives rcoh : lunit ≡ i.
  -- Via from-pathp: w0 = ap (i ⨾_) (sym rcoh) ∙ pre-counit i ≡ sym p.
  -- The singl Σ j, lunit ≡ j is a prop, so rcoh_p₁ ≡ rcoh_p₂.
  -- Therefore w0_p₁ ≡ w0_p₂, hence p₁ ≡ p₂.
  is-idempotent-is-prop : ∀ {x} {i : hom x x} (e : is-eqv i) → is-prop (is-idempotent i)
  is-idempotent-is-prop {x} {i} e p₁ p₂ = goal where
    open iso-inv e

    -- Fiber center is independent of p
    fib-center : fiber (i ⨾_) i
    fib-center = lunit , pre-counit i

    -- Fiber contractibility gives paths to any element
    fiber-contr : is-contr (fiber (i ⨾_) i)
    fiber-contr = e .fst .eqv-fibers i

    -- Fiber paths for each idempotence proof
    f₁ : fiber (i ⨾_) i
    f₁ = i , sym p₁

    f₂ : fiber (i ⨾_) i
    f₂ = i , sym p₂

    path₁ : fib-center ≡ f₁
    path₁ = fiber-contr .paths f₁

    path₂ : fib-center ≡ f₂
    path₂ = fiber-contr .paths f₂

    -- Extract rcoh paths: lunit ≡ i
    rcoh₁ : lunit ≡ i
    rcoh₁ = ap fst path₁

    rcoh₂ : lunit ≡ i
    rcoh₂ = ap fst path₂

    -- The singl Σ j, lunit ≡ j is a prop (contractible)
    singl-prop : is-prop (Σ j ∶ hom x x , lunit ≡ j)
    singl-prop = Singl-unique

    -- Both (i, rcoh₁) and (i, rcoh₂) are in the singl
    singl₁ : Σ j ∶ hom x x , lunit ≡ j
    singl₁ = i , rcoh₁

    singl₂ : Σ j ∶ hom x x , lunit ≡ j
    singl₂ = i , rcoh₂

    -- By singl prop: these are equal
    singl-eq : singl₁ ≡ singl₂
    singl-eq = singl-prop singl₁ singl₂

    -- Extract: rcoh₁ ≡ rcoh₂ (the fst components are both i, so ap snd gives a path)
    -- Since fst singl₁ = i = fst singl₂, the PathP from snd is a plain path
    fst-eq : i ≡ i
    fst-eq = ap fst singl-eq

    -- snd gives PathP (λ k → lunit ≡ fst-eq k) rcoh₁ rcoh₂
    snd-pathp : PathP (λ k → lunit ≡ fst-eq k) rcoh₁ rcoh₂
    snd-pathp k = singl-eq k .snd

    -- The singl is contractible, so also a set
    singl-contr : is-contr (Σ j ∶ hom x x , lunit ≡ j)
    singl-contr = Singl-contr lunit

    singl-set : is-set (Σ j ∶ hom x x , lunit ≡ j)
    singl-set = is-contr→is-set singl-contr

    -- fst-eq is a loop at i. Use that cosingl is a set to show paths are unique.
    -- The path singl-eq can be compared to a constant path if one exists.
    -- Since singl₁ and singl₂ have the same fst = i, we can construct
    -- a path with fst = refl if rcoh₁ ≡ rcoh₂ holds... but that's circular.
    --
    -- Alternative: use that the contractible singl has trivial loops.
    -- The element (i, rcoh₁) has a unique path from center (lunit, refl).
    -- The element (i, rcoh₂) also has a unique path from center.
    -- singl-eq = sym (center-to-1) ∙ center-to-2
    -- where center-to-k = singl-contr .paths (i, rcoh_k)
    --
    -- ap fst (singl-contr .paths (i, rcoh)) = rcoh (the path lunit ≡ i)
    -- So ap fst singl-eq = sym rcoh₁ ∙ rcoh₂ = fst-eq
    --
    -- Key insight: use fiber directly. The fiber is contractible → set.
    -- Paths f₁ ≡ f₂ are uniquely determined.

    fiber-set : is-set (fiber (i ⨾_) i)
    fiber-set = is-contr→is-set fiber-contr

    -- Direct fiber path
    fiber-eq : f₁ ≡ f₂
    fiber-eq = is-contr→is-prop fiber-contr f₁ f₂

    -- The fst projection of fiber-eq
    θ : i ≡ i
    θ = ap fst fiber-eq

    -- The snd gives PathP from sym p₁ to sym p₂ over θ
    fiber-snd : PathP (λ k → i ⨾ θ k ≡ i) (sym p₁) (sym p₂)
    fiber-snd k = fiber-eq k .snd

    -- Now use fiber being a set: if we can find ANY path f₁ ≡ f₂ with ap fst = refl,
    -- then θ = refl. We construct this using rcoh equality.
    --
    -- Actually, simpler: fiber-eq = sym path₁ ∙ path₂
    -- ap fst fiber-eq = sym (ap fst path₁) ∙ ap fst path₂ = sym rcoh₁ ∙ rcoh₂
    --
    -- We need sym rcoh₁ ∙ rcoh₂ ≡ refl, i.e., rcoh₁ ≡ rcoh₂.
    --
    -- From singl-eq: (i, rcoh₁) ≡ (i, rcoh₂) in singl.
    -- ap fst singl-eq : i ≡ i is fst-eq.
    -- If fst-eq = refl, then snd-pathp : rcoh₁ ≡ rcoh₂.
    --
    -- singl-eq = is-contr→is-prop singl-contr singl₁ singl₂
    --            = sym (singl-contr .paths singl₁) ∙ singl-contr .paths singl₂
    -- singl-contr .paths (j, q) k = (q k, λ l → q (k ∧ l))
    -- So ap fst (singl-contr .paths (i, rcoh)) k = rcoh k
    -- Thus ap fst singl-eq = sym rcoh₁ ∙ rcoh₂ = fst-eq
    --
    -- This is the same as θ! So θ = fst-eq.
    -- And showing θ = refl is equivalent to showing fst-eq = refl.

    -- Use that the singl is a set to compare paths.
    -- singl₁ and singl₂ have the same fst component: i.
    -- We need a path singl₁ ≡ singl₂ with ap fst = refl.
    -- Such a path exists iff rcoh₁ ≡ rcoh₂ (the circular issue).
    --
    -- Alternative approach: The path type lunit ≡ i embeds into the singl.
    -- The singl is contractible, hence a prop.
    -- Two elements (i, rcoh₁) and (i, rcoh₂) are equal.
    -- The path between them has fst : i ≡ i.
    -- Since lunit ≡ i embeds into singl at the SAME base point i,
    -- and singl is a SET, paths in singl between same endpoints are equal.
    -- Any two paths singl₁ ≡ singl₂ are equal.
    -- If we can show ONE such path has ap fst = refl, we're done.
    --
    -- To construct a path with ap fst = refl, we need rcoh₁ ≡ rcoh₂ first!
    -- This seems circular...
    --
    -- BREAKTHROUGH: Use that singl is CONTRACTIBLE, not just a set.
    -- In a contractible type, the loop space at any point is also contractible.
    -- So loops at (i, rcoh₁) in singl are trivial.
    -- fst-eq is NOT a loop (it goes from i to i, but via ap fst of a non-loop path).
    --
    -- Actually the real insight: in a PROP, all paths are equal.
    -- singl is a prop. singl-eq is THE unique path singl₁ ≡ singl₂.
    -- But different choices of representative might give different ap fst...
    --
    -- ACTUAL FIX: Use that in a contractible type, ANY path x ≡ y is equal to
    -- sym (center-path x) ∙ center-path y.
    -- For singl: singl-contr .paths (i, rcoh) k = (rcoh k, λ l → rcoh (k ∧ l))
    -- This path goes from (lunit, refl) to (i, rcoh).
    -- ap fst of this path is rcoh.
    --
    -- singl-eq = sym (paths singl₁) ∙ paths singl₂
    -- ap fst singl-eq = sym rcoh₁ ∙ rcoh₂
    --
    -- Now, is sym rcoh₁ ∙ rcoh₂ = refl? That requires rcoh₁ = rcoh₂.
    -- But rcoh₁ and rcoh₂ are both paths lunit ≡ i.
    -- They arise from fiber paths, which are uniquely determined.
    --
    -- KEY: The fiber and singl are DIFFERENT structures!
    -- Fiber paths path₁, path₂ give rcoh₁, rcoh₂.
    -- These live in Σ j, lunit ≡ j at the common endpoint i.
    -- The embedding lunit ≡ i → (Σ j, lunit ≡ j) via (i, _) is injective
    -- on paths because the singl is a set!
    --
    -- Wait, that doesn't directly help.
    --
    -- Let me try: the map (lunit ≡ i) → singl via j ↦ (i, j) is constant
    -- on the codomain (everything in singl is equal to the center).
    -- No, that's wrong too.
    --
    -- FINAL INSIGHT from Chen's paper:
    -- The fiber being contractible means the type (i ⨾ j ≡ i) is equivalent to (j ≡ lunit).
    -- So (i ⨾ i ≡ i) ≃ (i ≡ lunit).
    -- Idempotence p : i ≡ i ⨾ i corresponds under this to some path i ≡ lunit.
    -- But wait, that's the REVERSE direction...
    --
    -- Actually: fiber (i ⨾_) i is contractible with center (lunit, pre-counit i).
    -- An element (j, q : i ⨾ j ≡ i) is uniquely path-connected to center.
    -- The path from center to (i, sym p) has fst = rcoh : lunit ≡ i.
    --
    -- Now (lunit ≡ i) is one specific path type. If we know it's a prop, we're done.
    -- But hom x x is not assumed to be a set!
    --
    -- However, (lunit ≡ i) EMBEDS into the fiber via j ↦ (j, transport-path).
    -- No wait, that's not quite right either.
    --
    -- OK here's the actual solution:
    -- The singl Σ j, lunit ≡ j is CONTRACTIBLE, hence a PROP.
    -- Elements (i, rcoh₁) and (i, rcoh₂) are equal as pairs.
    -- Since they have the same first component i (definitionally!),
    -- the second components must be equal as paths: rcoh₁ ≡ rcoh₂.
    --
    -- How do we extract this? Pair equality gives:
    -- fst-eq : i ≡ i
    -- PathP (λ k → lunit ≡ fst-eq k) rcoh₁ rcoh₂
    --
    -- If fst-eq = refl, then this PathP becomes rcoh₁ ≡ rcoh₂.
    -- To show fst-eq = refl, note that fst-eq is a LOOP at i.
    -- i is in hom x x. hom x x might not be a set.
    -- BUT: fst-eq = ap fst singl-eq, and cosingl is a set.
    -- Hmm, that doesn't directly help for loops in hom x x.
    --
    -- REAL SOLUTION: Use that the type (i ≡ i) in hom x x
    -- has a retraction to the trivial type induced by the fiber structure.
    -- Or: use J on fst-eq.

    -- Use J to extract rcoh₁ ≡ rcoh₂ from the singl path
    -- J : (P : ∀ y → x ≡ y → Type) → P x refl → (p : x ≡ y) → P y p
    -- Apply J to singl-eq : singl₁ ≡ singl₂
    -- Motive: λ (j, r) _ → r ≡ rcoh₁
    -- Base at singl₁ = (i, rcoh₁): rcoh₁ ≡ rcoh₁, so base = refl
    -- Result at singl₂ = (i, rcoh₂): rcoh₂ ≡ rcoh₁
    rcoh₂≡rcoh₁ : rcoh₂ ≡ rcoh₁
    rcoh₂≡rcoh₁ = J (λ { (j , r) _ → r ≡ rcoh₁ }) refl singl-eq

    rcoh-eq : rcoh₁ ≡ rcoh₂
    rcoh-eq = sym rcoh₂≡rcoh₁

    -- Now θ ≡ refl follows: fiber-eq equals sym path₁ ∙ path₂ (by set uniqueness)
    -- and ap fst (sym path₁ ∙ path₂) = sym rcoh₁ ∙ rcoh₂ = sym rcoh₁ ∙ rcoh₁ = refl
    -- (using invl from Core.Kan)

    -- The canonical path via center
    canon-path : f₁ ≡ f₂
    canon-path = sym path₁ ∙ path₂

    -- fiber-eq equals canon-path (fiber is a set)
    fiber-eq-canon : fiber-eq ≡ canon-path
    fiber-eq-canon = fiber-set f₁ f₂ fiber-eq canon-path

    -- θ equals the canonical loop sym rcoh₁ ∙ rcoh₂
    θ-canon : θ ≡ sym rcoh₁ ∙ rcoh₂
    θ-canon = ap (ap fst) fiber-eq-canon

    θ-is-refl : θ ≡ refl
    θ-is-refl = θ-canon ∙ ap (sym rcoh₁ ∙_) rcoh-eq ∙ invl rcoh₁

    -- With θ ≡ refl, we can extract sym p₁ ≡ sym p₂ from the fiber snd
    sym-p-eq : sym p₁ ≡ sym p₂
    sym-p-eq = subst (λ loop → PathP (λ k → i ⨾ loop k ≡ i) (sym p₁) (sym p₂)) θ-is-refl fiber-snd

    goal : p₁ ≡ p₂
    goal = ap sym sym-p-eq

-- Full propositionality of is-idem-equiv
module unit-prop {u v} (C : precategory u v) where
  private module C = Cat C
  open C
  open unit-defs C
  open idem-is-prop C

  is-idem-equiv-is-prop : ∀ {x} {i : hom x x} → is-prop (is-idem-equiv i)
  is-idem-equiv-is-prop {i = i} ie₁ ie₂ = path where
    e₁ = ie₁ .is-idem-equiv.eqv
    e₂ = ie₂ .is-idem-equiv.eqv
    p₁ = ie₁ .is-idem-equiv.idem
    p₂ = ie₂ .is-idem-equiv.idem

    eqv-eq : e₁ ≡ e₂
    eqv-eq = is-eqv-is-prop i e₁ e₂

    idem-eq : p₁ ≡ p₂
    idem-eq = is-idempotent-is-prop e₁ p₁ p₂

    path : ie₁ ≡ ie₂
    path j .is-idem-equiv.idem = idem-eq j
    path j .is-idem-equiv.eqv = eqv-eq j
```

