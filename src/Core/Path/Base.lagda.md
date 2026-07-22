---
author: Lane Biocini
date: 2025-10
contents: Path algebra — symmetry, concatenation, squares, and coherences.
---

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Path.Base where

open import Core.Transport.Base
open import Core.Transport.J using (J)
open import Core.Base
open import Core.Type
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Pointed
open import Core.Kan
open import Core.Sub

private
  variable
    u v : Level
    A : I → Type u

ap-comp : ∀ {u v} {A : Type u} {B : Type v} (f : A → B)
        {x y z : A} (p : x ≡ y) (q : y ≡ z)
        → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-comp f p q = ap fst
  (HComposite.unique refl (ap f p) (ap f q)
    (ap f (p ∙ q) , λ i j → f (cat.fill p q i j))
    (ap f p ∙ ap f q , cat.fill (ap f p) (ap f q)))

ap-∘ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
     (g : B → C) (f : A → B)
     {x y : A} (p : x ≡ y)
     → ap (λ a → g (f a)) p ≡ ap g (ap f p)
ap-∘ g f p = refl

-- comp-pathp₁-ap: the displaced ap-comp at a unary family — one
-- coherence cube instead of two. The com is retaken along the
-- HComposite coherence between ap-comp's two fillers, whose
-- i0/i1 slices are the two comp-pathp₁ lines definitionally.
comp-pathp₁-ap
  : ∀ {uA u w} {A : Type uA} {X : Type u}
    (F : X → Type w) (f : A → X)
    {a₀ a₁ a₂ : A} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {h₀ : F (f a₀)} {h₁ : F (f a₁)} {h₂ : F (f a₂)}
    (P : PathP (λ i → F (f (pa i))) h₀ h₁)
    (Q : PathP (λ i → F (f (qa i))) h₁ h₂)
  → PathP (λ m → PathP (λ i → F (ap-comp f pa qa m i)) h₀ h₂)
          (comp-pathp₁ (λ a → F (f a)) pa qa P Q)
          (comp-pathp₁ F (ap f pa) (ap f qa) P Q)
comp-pathp₁-ap F f pa qa {h₀ = h₀} P Q m i =
  com (λ t → F (coh m i t)) (∂ i) λ where
    t (i = i0) → h₀
    t (i = i1) → Q t
    t (t = i0) → P i
  where
    coh = HComposite.coh refl (ap f pa) (ap f qa)
            (ap f (pa ∙ qa) , λ i j → f (cat.fill pa qa i j))
            (ap f pa ∙ ap f qa , cat.fill (ap f pa) (ap f qa))

-- comp-pathp₂-ap: the displaced ap-comp. A comp-pathp₂ at a
-- reindexed binary family agrees with the comp-pathp₂ at the base
-- family over the ap-images, as a square over the two ap-comp
-- shuffles: the com is retaken along the HComposite coherence
-- between ap-comp's two fillers, whose i0/i1 slices are the two
-- comp-pathp₂ lines definitionally.
comp-pathp₂-ap
  : ∀ {uA uB u v w} {A : Type uA} {B : Type uB} {X : Type u} {Y : Type v}
    (F : X → Y → Type w) (f : A → X) (g : B → Y)
    {a₀ a₁ a₂ : A} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {b₀ b₁ b₂ : B} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂)
    {h₀ : F (f a₀) (g b₀)} {h₁ : F (f a₁) (g b₁)} {h₂ : F (f a₂) (g b₂)}
    (P : PathP (λ i → F (f (pa i)) (g (pb i))) h₀ h₁)
    (Q : PathP (λ i → F (f (qa i)) (g (qb i))) h₁ h₂)
  → PathP (λ m → PathP (λ i → F (ap-comp f pa qa m i) (ap-comp g pb qb m i))
                 h₀ h₂)
          (comp-pathp₂ (λ a b → F (f a) (g b)) pa qa pb qb P Q)
          (comp-pathp₂ F (ap f pa) (ap f qa) (ap g pb) (ap g qb) P Q)
comp-pathp₂-ap F f g pa qa pb qb {h₀ = h₀} P Q m i =
  com (λ t → F (cohA m i t) (cohB m i t)) (∂ i) λ where
    t (i = i0) → h₀
    t (i = i1) → Q t
    t (t = i0) → P i
  where
    cohA = HComposite.coh refl (ap f pa) (ap f qa)
             (ap f (pa ∙ qa) , λ i j → f (cat.fill pa qa i j))
             (ap f pa ∙ ap f qa , cat.fill (ap f pa) (ap f qa))
    cohB = HComposite.coh refl (ap g pb) (ap g qb)
             (ap g (pb ∙ qb) , λ i j → g (cat.fill pb qb i j))
             (ap g pb ∙ ap g qb , cat.fill (ap g pb) (ap g qb))

ap-merge
  : ∀ {u v} {A : Type u} {B : Type v} (G : A → B) {a a' a'' : A} {w : B}
    (X : w ≡ G a) (p : a ≡ a') (e : a' ≡ a'')
  → (X ∙ ap G p) ∙ ap G e ≡ X ∙ ap G (p ∙ e)
ap-merge G X p e =
  sym (Path.assoc X (ap G p) (ap G e)) ∙ ap (X ∙_) (sym (ap-comp G p e))

-- comp-pathp₂-merge: the displaced ap-merge. ap-merge is
-- definitionally the two-leaf tree
-- sym (Path.assoc X (ap G p) (ap G e)) ∙ ap (X ∙_) (sym (ap-comp G p e)),
-- so the displaced mate is comp-pathp₂ at the family of lines over
-- the composite, along exactly that tree: one displaced cell per
-- leaf — the reversed comp-pathp₂-assoc at the head line and the
-- two ap-image lines, then the head-whiskered reversed
-- comp-pathp₂-ap. Every interface between the leaves is
-- definitional.
comp-pathp₂-merge
  : ∀ {uA uB u v w} {A : Type uA} {B : Type uB} {X : Type u} {Y : Type v}
    (F : X → Y → Type w) (f : A → X) (g : B → Y)
    {a₀ a₁ a₂ : A} {wa : X} (Xa : wa ≡ f a₀) (pa : a₀ ≡ a₁) (ea : a₁ ≡ a₂)
    {b₀ b₁ b₂ : B} {wb : Y} (Xb : wb ≡ g b₀) (pb : b₀ ≡ b₁) (eb : b₁ ≡ b₂)
    {h₀ : F wa wb} {h₁ : F (f a₀) (g b₀)} {h₂ : F (f a₁) (g b₁)}
    {h₃ : F (f a₂) (g b₂)}
    (X̂ : PathP (λ i → F (Xa i) (Xb i)) h₀ h₁)
    (P̂ : PathP (λ i → F (f (pa i)) (g (pb i))) h₁ h₂)
    (Ê : PathP (λ i → F (f (ea i)) (g (eb i))) h₂ h₃)
  → PathP (λ m → PathP (λ i → F (ap-merge f Xa pa ea m i)
                                (ap-merge g Xb pb eb m i))
                 h₀ h₃)
      (comp-pathp₂ F (Xa ∙ ap f pa) (ap f ea) (Xb ∙ ap g pb) (ap g eb)
        (comp-pathp₂ F Xa (ap f pa) Xb (ap g pb) X̂ P̂) Ê)
      (comp-pathp₂ F Xa (ap f (pa ∙ ea)) Xb (ap g (pb ∙ eb)) X̂
        (comp-pathp₂ (λ a b → F (f a) (g b)) pa ea pb eb P̂ Ê))
comp-pathp₂-merge F f g {a₂ = a₂} {wa = wa} Xa pa ea {b₂ = b₂} {wb = wb}
  Xb pb eb {h₀ = h₀} {h₃ = h₃} X̂ P̂ Ê =
  comp-pathp₂ Fam
    (sym (Path.assoc Xa (ap f pa) (ap f ea)))
    (ap (Xa ∙_) (sym (ap-comp f pa ea)))
    (sym (Path.assoc Xb (ap g pb) (ap g eb)))
    (ap (Xb ∙_) (sym (ap-comp g pb eb)))
    assoĉ shufflê
  where
    Fam : wa ≡ f a₂ → wb ≡ g b₂ → Type _
    Fam p p' = PathP (λ i → F (p i) (p' i)) h₀ h₃

    assoĉ
      : PathP (λ m → Fam (Path.assoc Xa (ap f pa) (ap f ea) (~ m))
                         (Path.assoc Xb (ap g pb) (ap g eb) (~ m)))
          (comp-pathp₂ F (Xa ∙ ap f pa) (ap f ea) (Xb ∙ ap g pb) (ap g eb)
            (comp-pathp₂ F Xa (ap f pa) Xb (ap g pb) X̂ P̂) Ê)
          (comp-pathp₂ F Xa (ap f pa ∙ ap f ea) Xb (ap g pb ∙ ap g eb) X̂
            (comp-pathp₂ F (ap f pa) (ap f ea) (ap g pb) (ap g eb) P̂ Ê))
    assoĉ m =
      comp-pathp₂-assoc F Xa (ap f pa) (ap f ea) Xb (ap g pb) (ap g eb)
        X̂ P̂ Ê (~ m)

    shufflê
      : PathP (λ m → Fam (Xa ∙ ap-comp f pa ea (~ m))
                         (Xb ∙ ap-comp g pb eb (~ m)))
          (comp-pathp₂ F Xa (ap f pa ∙ ap f ea) Xb (ap g pb ∙ ap g eb) X̂
            (comp-pathp₂ F (ap f pa) (ap f ea) (ap g pb) (ap g eb) P̂ Ê))
          (comp-pathp₂ F Xa (ap f (pa ∙ ea)) Xb (ap g (pb ∙ eb)) X̂
            (comp-pathp₂ (λ a b → F (f a) (g b)) pa ea pb eb P̂ Ê))
    shufflê m =
      comp-pathp₂ F Xa (ap-comp f pa ea (~ m)) Xb (ap-comp g pb eb (~ m))
        X̂ (comp-pathp₂-ap F f g pa ea pb eb P̂ Ê (~ m))

-- comp-pathp₂-merge-map: the displaced ap-merge whose tail lines
-- are fiberwise images ω ∘ P̂, ω ∘ Ê of lines in an inner family.
-- The bare merge ends at the comp-pathp₂ of the images, but hcom
-- does not commute with fiberwise application, so the merged end
-- is reconciled to the image of the comp-pathp₂ — comp-pathp₂-map
-- at the reindexed inner family, capped on the merge by one hcom
-- in the m-direction; every boundary is definitional.
comp-pathp₂-merge-map
  : ∀ {uA uB u v w w'} {A : Type uA} {B : Type uB} {X : Type u} {Y : Type v}
    (G : X → Y → Type w) (F : A → B → Type w') (f : A → X) (g : B → Y)
    (ω : ∀ {a b} → F a b → G (f a) (g b))
    {a₀ a₁ a₂ : A} {wa : X} (Xa : wa ≡ f a₀) (pa : a₀ ≡ a₁) (ea : a₁ ≡ a₂)
    {b₀ b₁ b₂ : B} {wb : Y} (Xb : wb ≡ g b₀) (pb : b₀ ≡ b₁) (eb : b₁ ≡ b₂)
    {h₀ : G wa wb} {k₁ : F a₀ b₀} {k₂ : F a₁ b₁} {k₃ : F a₂ b₂}
    (X̂ : PathP (λ i → G (Xa i) (Xb i)) h₀ (ω k₁))
    (P̂ : PathP (λ i → F (pa i) (pb i)) k₁ k₂)
    (Ê : PathP (λ i → F (ea i) (eb i)) k₂ k₃)
  → PathP (λ m → PathP (λ i → G (ap-merge f Xa pa ea m i)
                                (ap-merge g Xb pb eb m i))
                 h₀ (ω k₃))
      (comp-pathp₂ G (Xa ∙ ap f pa) (ap f ea) (Xb ∙ ap g pb) (ap g eb)
        (comp-pathp₂ G Xa (ap f pa) Xb (ap g pb) X̂ (λ i → ω (P̂ i)))
        (λ i → ω (Ê i)))
      (comp-pathp₂ G Xa (ap f (pa ∙ ea)) Xb (ap g (pb ∙ eb)) X̂
        (λ i → ω (comp-pathp₂ F pa ea pb eb P̂ Ê i)))
comp-pathp₂-merge-map G F f g ω Xa pa ea Xb pb eb X̂ P̂ Ê m =
  hcom (∂ m) λ where
    k (m = i0) →
      comp-pathp₂ G (Xa ∙ ap f pa) (ap f ea) (Xb ∙ ap g pb) (ap g eb)
        (comp-pathp₂ G Xa (ap f pa) Xb (ap g pb) X̂ (λ i → ω (P̂ i)))
        (λ i → ω (Ê i))
    k (m = i1) →
      comp-pathp₂ G Xa (ap f (pa ∙ ea)) Xb (ap g (pb ∙ eb)) X̂
        (comp-pathp₂-map F (λ a b → G (f a) (g b)) ω pa ea pb eb P̂ Ê (~ k))
    k (k = i0) →
      comp-pathp₂-merge G f g Xa pa ea Xb pb eb X̂
        (λ i → ω (P̂ i)) (λ i → ω (Ê i)) m

Ω : ∀ {u} → Type* u → Type u
Ω (_ , a) = a ≡ a
{-# INLINE Ω #-}

Loop : ∀ {u} → Type* u → Type* u
Loop A .fst = Ω A
Loop A .snd = refl

infix 4 _≢_
_≢_ : {A : Type u} → A → A → Type u
x ≢ y = ¬ (x ≡ y)
```

## Cancellation

Left- and right-cancellation for `_∙_`, the transposition
`move-r` — from `p ∙ sym q ≡ r` conclude `p ≡ r ∙ q` — and the
conjugation cancellation: a loop `ζ` conjugated into a composite
that agrees with the plain composite must be trivial. `move-r`
leans on the definitional involution `sym (sym q) ≐ q` to convert
the cancellation endpoint (the involution is pinned by
`Core.Groupoid.op-invol`). `ap-retr` reads `ap f`, for `f`
homotopic to the identity, as conjugation of the path by the
homotopy.

```agda
cancell
  : ∀ {u} {A : Type u} {a b c : A}
  → (p : a ≡ b) (s : b ≡ c)
  → sym p ∙ p ∙ s ≡ s
cancell p s =
  Path.assoc (sym p) p s
  ∙ ap (_∙ s) (Path.invl p)
  ∙ Path.unitl s

cancelr
  : ∀ {u} {A : Type u} {a b c : A}
  → (q : b ≡ c) (t : a ≡ b)
  → (t ∙ q) ∙ sym q ≡ t
cancelr q t =
  sym (Path.assoc t q (sym q))
  ∙ ap (t ∙_) (Path.invr q)
  ∙ Path.unitr t

move-r
  : ∀ {u} {A : Type u} {a b c : A}
  → (p : a ≡ b) (q : c ≡ b) (r : a ≡ c)
  → p ∙ sym q ≡ r → p ≡ r ∙ q
move-r p q r h =
  sym (cancelr (sym q) p) ∙ ap (_∙ q) h

conj-cancel
  : ∀ {u} {A : Type u} {a b c : A}
  → (p : a ≡ b) (q : b ≡ c) (ζ : b ≡ b)
  → p ∙ q ≡ p ∙ ζ ∙ q
  → ζ ≡ refl
conj-cancel p q ζ h =
  sym (cancelr q ζ)
  ∙ ap (_∙ sym q) (sym cancel-left)
  ∙ Path.invr q
  where
    cancel-left : q ≡ ζ ∙ q
    cancel-left =
      sym (cancell p q)
      ∙ ap (sym p ∙_) h
      ∙ cancell p (ζ ∙ q)

ap-retr
  : ∀ {u} {A : Type u} {f : A → A} (H : ∀ x → f x ≡ x) {x y : A}
  → (p : x ≡ y) → ap f p ≡ H x ∙ p ∙ sym (H y)
ap-retr {f = f} H {x = x} =
  J (λ y' p' → ap f p' ≡ H x ∙ p' ∙ sym (H y'))
    (sym (ap (H x ∙_) (Path.unitl (sym (H x))) ∙ Path.invr (H x)))
```
