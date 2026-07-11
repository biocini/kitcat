Lane Biocini
July 2026

The Mac Lane triangle for representable hcategories. Over a bundle
`(C : hcategory o h)` the *weak* triangle
`ap (_⨾ g) (unitr f) ≡ assoc f (idn y) g ∙ α₂₃` holds with the middle
edge `α₂₃` abstract — no coherence overlay, only the base axioms and
`assoc-tower`.

The three triangle vertices sit in the composition fiber
`compose-contr f g`, right-nested binary witnesses through the `·-idn`
expansion. Each face reads a fiber edge `αᵢⱼ` against a named unit/
associativity law through `contr-face` and a canonical lift — the
right whisker `Λg` (face₁₃, the *free* unitr face) and the reindex `R`
against the `·-idn` tail (face₁₂, associativity). The tower mirrors
`Cat.Coherence`'s old record-level weak triangle onto the flat
carrier, reusing `assoc-tower` (from `Cat.Codep.Coherence`) for
`assoc`/`assoc-σ`/`pt-l`/`pt-r`/`E₃`.

## The full triangle closes through the identity-argument gauge

The *full* triangle identifies `α₂₃` with the left-whiskered `unitl g`
(`face₂₃`, the paid unitl face). It closes against the `Cat.Codep`
stack once the coherence overlay `A2 : hcategory-2-coherent C` is in
scope — it needs no fourth cell. The mechanism:

  * The library `unitl g` (`Cat.Codep.Base`) is `ap fst` of a path in
    `emb-image-contr g`, whose left endpoint witness is
    `emb-comp (idn y) g ∙ emb-idn-absorb g`. The fiber `compose-contr
    f g` is contractible, hence a set, so any fiber path realising
    `ap (f ⨾_) (unitl g)` necessarily threads `emb-idn-absorb g`.
  * `emb-idn-absorb g`'s pre-position reading is *definitionally* the
    `absorb-r` form (`interchange … ∙ ap … (absorb-r (idn y))`).
  * The overlay `absorb-lcoh` supplies `absorb-l` in the `post-eval`
    form. Reconciling the two is exactly `absorb-r (idn y) ≡
    post-eval (idn y)` — and that cell is **derivable**, not a new
    field: it is `gauge-r` (`Cat.Codep.Coherent`), the homotopy-
    naturality of `absorb-r` along `post-eval` whiskered against the
    θ-core reconciliations. So `face₂₃` costs only the three overlay
    cells, no independent fourth.

`Gloss.TriangleFace23` first isolated the bridge as a total
function of that single cell; `gauge-r` then discharged the cell.
`EU` reads the `unitl` fiber-witness square back as a path, and the
paid face collapses pointwise (`happly` distributes definitionally)
onto pt₂'s `·-idn` route via `bridge`/`INNER`.

The earlier claim that `face₂₃` needed an *independent* fourth cell was
a misattribution. The `Cat.Codep.Coherent` header's S²/π₃ independence
result is about strict **op-involution** of the cell tower — one
dimension up — not about this gauge, which is π₁-level and derivable.

The op-dual (mirror) triangle is the free instantiation at
`(op C , op-coherent A2)` — see `mirror-triangle` below.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Triangle where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using
  ( is-contr→is-prop; _∙_; contr-face; module Path; pcom; hcom )
open import Core.Path.Base using (ap-comp)
open import Core.Coherence.Base using (coh-project)

open import Cat.Codep.Base
open import Cat.Codep.Coherence using (module assoc-tower)
open import Cat.Codep.Coherent using (hcategory-2-coherent; op-coherent)
open import Cat.Codep.Op using (op)
```

## Weak triangle

The weak tower gates on the bundle alone. `triangle-fibers` fixes
`f g` and carries the three vertices, the `σ`/`α` edges, and the two
free faces `face₁₃`/`face₁₂`. The middle edge `α₂₃` stays abstract.

```agda
module triangle-weak-tower {o h} (C : hcategory o h) where
  open hcategory C
  open assoc-tower C

  module triangle-fibers {x y z} (f : hom x y) (g : hom y z) where
    private
      e : hom y y
      e = idn y

    cc : is-contr (fiber emb (emb f · g))
    cc = compose-contr f g

    pt₁ : fiber emb (emb f · g)
    pt₁ = (f ⨾ e) ⨾ g
        , emb-comp (f ⨾ e) g
        ∙ ap (_· g) (emb-comp f e)
        ∙ ap (_· g) (·-idn (emb f))

    pt₂ : fiber emb (emb f · g)
    pt₂ = f ⨾ (e ⨾ g)
        , emb-comp f (e ⨾ g)
        ∙ ·-comp (emb f) e g
        ∙ ap (_· g) (·-idn (emb f))

    pt₃ : fiber emb (emb f · g)
    pt₃ = f ⨾ g , emb-comp f g

    σ₁₃ = is-contr→is-prop cc pt₁ pt₃
    σ₁₂ = is-contr→is-prop cc pt₁ pt₂
    σ₂₃ = is-contr→is-prop cc pt₂ pt₃

    α₁₃ : (f ⨾ e) ⨾ g ≡ f ⨾ g
    α₁₃ = ap fst σ₁₃

    α₁₂ : (f ⨾ e) ⨾ g ≡ f ⨾ (e ⨾ g)
    α₁₂ = ap fst σ₁₂

    α₂₃ : f ⨾ (e ⨾ g) ≡ f ⨾ g
    α₂₃ = ap fst σ₂₃

    -- face₁₃: the right whisker of unitr f by g. Λg lifts an
    -- emb-fiber over emb f to one over emb f · g; the unitr fiber
    -- path U is whiskered through it.
    Λg : fiber emb (emb f) → fiber emb (emb f · g)
    Λg (m , p) = m ⨾ g , emb-comp m g ∙ ap (_· g) p

    U : (f ⨾ e , emb-comp f e ∙ ·-idn (emb f)) ≡ (f , refl)
    U = is-contr→is-prop (emb-image-contr f) _ _

    face₁₃ : α₁₃ ≡ ap (_⨾ g) (unitr f)
    face₁₃ = contr-face cc σ₁₃ w₁₃ (λ i → Λg (U i)) v₁₃
      where
        w₁₃ : pt₁ .snd ≡ (Λg (U i0)) .snd
        w₁₃ = sym (ap (emb-comp (f ⨾ e) g ∙_)
          (ap-comp (_· g) (emb-comp f e) (·-idn (emb f))))
        v₁₃ : (Λg (U i1)) .snd ≡ pt₃ .snd
        v₁₃ = Path.unitr (emb-comp f g)

    -- face₁₂: the reindex against the shared ·-idn tail. R reindexes
    -- an emb-fiber over E₃ f e g to one over emb f · g by post-
    -- composing the tail; the associator assoc-σ f e g rides through.
    face₁₂ : α₁₂ ≡ assoc f e g
    face₁₂ = contr-face cc σ₁₂
      (Path.assoc (emb-comp (f ⨾ e) g) (ap (_· g) (emb-comp f e)) tail)
      (λ i → R (assoc-σ f e g i))
      (sym (Path.assoc (emb-comp f (e ⨾ g)) (·-comp (emb f) e g) tail))
      where
        tail : E₃ f e g ≡ emb f · g
        tail = ap (_· g) (·-idn (emb f))
        R : fiber emb (E₃ f e g) → fiber emb (emb f · g)
        R (m , p) = m , p ∙ tail

  module triangle {x y z} (f : hom x y) (g : hom y z) where
    open triangle-fibers f g

    hom-identity : α₁₃ ≡ α₁₂ ∙ α₂₃
    hom-identity =
      coh-project cc fst σ₁₃ (σ₁₂ ∙ σ₂₃) refl (ap-comp fst σ₁₂ σ₂₃)

  triangle-weak
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → ap (_⨾ g) (unitr f)
    ≡ assoc f (idn y) g ∙ triangle-fibers.α₂₃ f g
  triangle-weak f g =
    pcom face₁₃ hom-identity (ap (_∙ α₂₃) face₁₂)
    where
      open triangle-fibers f g
      open triangle f g
```

## Full triangle

With the coherence overlay `A2` in scope, `face₂₃` closes the middle
edge `α₂₃` against the left-whiskered `unitl g`, and the full Mac Lane
triangle follows. The bridge is `gauge-r` (from `Cat.Codep.Coherent`):
the library `unitl g` bakes in `emb-idn-absorb g`, whose pre-position
reading is the `absorb-r` form, and the overlay's `absorb-lcoh`
supplies the `post-eval` form — `gauge-r` reconciles the two.

`EU` reads the `unitl` fiber-witness square as a path
`ap emb (unitl g) ≡ emb-comp e g ∙ emb-idn-absorb g`. Whiskered at the
center context and bridged through `gauge-r`, it collapses the paid
`unitl` face pointwise onto pt₂'s `·-idn` route (`coh`); the two
`contr-face` endpoint witnesses `w23`/`v23` are then routine.

```agda
module triangle-full-tower {o h} (C : hcategory o h)
  (A2 : hcategory-2-coherent C) where
  open hcategory C
  open hcategory-2-coherent A2
  open assoc-tower C
  open triangle-weak-tower C

  module triangle-full {x y z} (f : hom x y) (g : hom y z) where
    open triangle-fibers f g
    open triangle f g

    e : hom y y
    e = idn y

    P₀ : emb (e ⨾ g) ≡ emb g
    P₀ = emb-comp e g ∙ emb-idn-absorb g

    Ug : PathP (λ _ → fiber emb (emb g)) ((e ⨾ g) , P₀) (g , refl)
    Ug = is-contr→is-prop (emb-image-contr g) _ _

    -- EU: the unitl fiber-witness square, read as a path.
    EU : ap emb (unitl g) ≡ P₀
    EU t s = hcom (∂ t ∨ ∂ s) λ where
      k (t = i0) → Ug s .snd i0
      k (t = i1) → P₀ s
      k (s = i0) → emb (e ⨾ g)
      k (s = i1) → Ug (~ t) .snd (t ∨ k)
      k (k = i0) → Ug (s ∧ ~ t) .snd (s ∧ t)

    -- The pre-side bridge, per context slot b.
    module bridged {v' : ob} (b : hom z v') where
      δ₀ : ctx y z
      δ₀ = (ctr y , (v' , b))

      c₀ : hom y v'
      c₀ = pre g b

      -- emb-idn-absorb at the center: the absorb-r reading baked into
      -- the library unitl g.
      K-absorbr : pre (idn y) c₀ ≡ c₀
      K-absorbr = happly (emb-idn-absorb g) δ₀

      -- bridge: K (absorb-r form) ≡ absorb-l c₀ (post-eval form) via
      -- gauge-r. K-is-absorbr / absorb-l-posteval collapse by refl.
      bridge : K-absorbr ≡ absorb-l c₀
      bridge =
        ap (interchange (idn y) g (idn y) b ∙_)
          (ap (ap (λ a' → emb g ((y , a') , (v' , b)))) gauge-r)
        ∙ sym (absorb-lcoh g b)

      -- UL: ap of pre along unitl, read through EU at the center.
      UL : ap (λ hh → pre hh b) (unitl g) ≡ pre-comp e g b ∙ K-absorbr
      UL = ap (λ p → happly p δ₀) EU

      INNER : pre-comp e g b ∙ absorb-l c₀
            ≡ ap (λ hh → pre hh b) (unitl g)
      INNER = ap (pre-comp e g b ∙_) (sym bridge) ∙ sym UL

    -- coh: pt₂'s ·-idn/·-comp route ≡ the left-whiskered unitl route.
    -- Pointwise it is `ap F₀` of INNER; happly distributes definitionally.
    CP : (γ : ctx x z)
       → happly (·-comp (emb f) e g ∙ ap (_· g) (·-idn (emb f))) γ
       ≡ happly (ap (emb f ·_) (unitl g)) γ
    CP γ =
      sym (ap-comp F₀ (pre-comp e g bγ) (absorb-l (pre g bγ)))
      ∙ ap (ap F₀) (bridged.INNER bγ)
      where
        bγ : hom z (γ .snd .fst)
        bγ = γ .snd .snd
        F₀ : hom y (γ .snd .fst) → res γ
        F₀ k = emb f (γ .fst , (γ .snd .fst , k))

    coh : (·-comp (emb f) e g ∙ ap (_· g) (·-idn (emb f)))
        ≡ ap (emb f ·_) (unitl g)
    coh i j γ = CP γ i j

    -- The left-whiskered unitl witness, and the two contr-face
    -- endpoint witnesses against pt₂ / pt₃.
    wit23 : (i : I) → emb (f ⨾ (unitl g i)) ≡ emb f · g
    wit23 i = emb-comp f (unitl g i) ∙ ap (emb f ·_) (λ j → unitl g (i ∨ j))

    w23 : pt₂ .snd ≡ wit23 i0
    w23 = ap (emb-comp f (e ⨾ g) ∙_) coh

    v23 : wit23 i1 ≡ pt₃ .snd
    v23 = Path.unitr (emb-comp f g)

    face₂₃ : α₂₃ ≡ ap (f ⨾_) (unitl g)
    face₂₃ = contr-face cc σ₂₃ w23 (λ i → f ⨾ (unitl g i) , wit23 i) v23

    triangle : ap (_⨾ g) (unitr f)
             ≡ assoc f (idn y) g ∙ ap (f ⨾_) (unitl g)
    triangle =
      pcom face₁₃ hom-identity
        (ap (_∙ α₂₃) face₁₂ ∙ ap (assoc f (idn y) g ∙_) face₂₃)
```

## Mirror (op-dual) triangle

The full triangle is uniform over any coherent hcategory, and
`op-coherent` transports the overlay to `op C`. So the op-dual Mac Lane
triangle needs no separate post-side proof: it is the instantiation of
`triangle-full-tower` at `(op C , op-coherent A2)`. In `op C` the
composite reverses and the unitors swap (`pre ↔ post`), so `triangle`
there is the mirror of the base statement — with the roles of the free
and paid faces exchanged, and `gauge-l` (rather than `gauge-r`) closing
the paid face inside `op-coherent`'s transported cells.

```agda
module mirror-triangle {o h} {C : hcategory o h}
  (A2 : hcategory-2-coherent C) where
  open triangle-full-tower (op C) (op-coherent A2) public
```
