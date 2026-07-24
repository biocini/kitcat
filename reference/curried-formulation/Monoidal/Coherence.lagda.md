Lane Biocini
July 2026

Native pentagon and triangle coherence for the monoidal
tensor. This is the erased-object-index image of the
coherence section of `Cat.Depreciated.Coherence`, applied to `tensor-emb`
in place of the delooped `emb`. The five reassociations of a
fourfold tensor sit in a fiber over `tensor-E₄` that the base
axioms make contractible; the pentagon is the `ap fst` image
of the two traversals of that fiber agreeing, forced by
`is-contr→is-set`. The weak triangle holds from the base
axioms; the full Mac Lane triangle requires
`monoidal-2-coherent`, which supplies `absorb-coh`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Monoidal.Coherence where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base using (contr-ind)
open import Core.Transport.J using (subst)
open import Core.Path.Base using (ap-comp)
open import Core.Coherence.Base using (coh-project)
open import Cat.Depreciated.Type
open import Cat.Depreciated.Monoidal
```

## The fourfold composite fiber

```agda
module _ {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  open category C using (ob)

  private
    tensor-E₄ : (w x y z : ob) → ob → ob → ob
    tensor-E₄ w x y z l r =
      tensor-emb w l (pre x (pre y (pre z r)))

  tensor-E₄-contr
    : (w x y z : ob)
    → is-contr (fiber tensor-emb (tensor-E₄ w x y z))
  tensor-E₄-contr w x y z .center .fst = ((w ⊗ x) ⊗ y) ⊗ z
  tensor-E₄-contr w x y z .center .snd =
    tensor-emb-composite ((w ⊗ x) ⊗ y) z
    ∙ tensor-emb-ext λ l r →
        tensor-emb-comp-pt (w ⊗ x) y l (pre z r)
      ∙ tensor-emb-comp-pt w x l (pre y (pre z r))
  tensor-E₄-contr w x y z .paths =
    is-contr→is-prop
      (subst (is-contr ∘ fiber tensor-emb) path
        (tensor-compose-contr ((w ⊗ x) ⊗ y) z)) _
    where
      path
        : (λ l r → tensor-emb ((w ⊗ x) ⊗ y) l (pre z r))
        ≡ tensor-E₄ w x y z
      path = tensor-emb-ext λ l r →
          tensor-emb-comp-pt (w ⊗ x) y l (pre z r)
        ∙ tensor-emb-comp-pt w x l (pre y (pre z r))

  tensor-E₄-ind
    : ∀ {u} (w x y z : ob)
    → (P : (s : ob)
         → tensor-emb s ≡ tensor-E₄ w x y z
         → Type u)
    → P (tensor-E₄-contr w x y z .center .fst)
        (tensor-E₄-contr w x y z .center .snd)
    → ∀ s q → P s q
  tensor-E₄-ind w x y z P base s q =
    contr-ind (tensor-E₄-contr w x y z)
      (λ where (s , q) → P s q)
      base (s , q)
```

## The associator fiber path

`assoc-σ` — the identification of the extended triple fiber's
center with the right-nested associator target `x ⊗ (y ⊗ z)` —
is a derived definition of the `monoidal` record (`Cat.Depreciated.Monoidal`),
in scope here through `open monoidal M`.

## Pentagon fibers

```agda
  module pentagon-fibers (w x y z : ob) where
    E₄c = tensor-E₄-contr w x y z

    private
      pt₁ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₁ = E₄c .center

      pt₂ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₂ = (w ⊗ (x ⊗ y)) ⊗ z
          , tensor-emb-composite (w ⊗ (x ⊗ y)) z
          ∙ tensor-emb-ext λ l r →
              tensor-emb-comp-pt w (x ⊗ y) l (pre z r)
            ∙ ap (tensor-emb w l)
                (tensor-pre-composite x y (pre z r))

      pt₃ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₃ = w ⊗ ((x ⊗ y) ⊗ z)
          , tensor-emb-composite w ((x ⊗ y) ⊗ z)
          ∙ tensor-emb-ext λ l r →
              ap (tensor-emb w l)
                (tensor-pre-composite (x ⊗ y) z r)
            ∙ ap (tensor-emb w l)
                (tensor-pre-composite x y (pre z r))

      pt₄ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₄ = (w ⊗ x) ⊗ (y ⊗ z)
          , tensor-emb-composite (w ⊗ x) (y ⊗ z)
          ∙ tensor-emb-ext λ l r →
              tensor-emb-comp-pt w x l (pre (y ⊗ z) r)
            ∙ ap (λ t → tensor-emb w l (pre x t))
                  (tensor-pre-composite y z r)

      pt₅ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₅ = w ⊗ (x ⊗ (y ⊗ z))
          , tensor-emb-composite w (x ⊗ (y ⊗ z))
          ∙ tensor-emb-ext λ l r →
              ap (tensor-emb w l)
                (tensor-pre-composite x (y ⊗ z) r)
            ∙ ap (λ t → tensor-emb w l (pre x t))
                  (tensor-pre-composite y z r)

    σ₁₄ : pt₁ ≡ pt₄
    σ₁₄ = is-contr→is-prop E₄c pt₁ pt₄

    σ₄₅ : pt₄ ≡ pt₅
    σ₄₅ = is-contr→is-prop E₄c pt₄ pt₅

    σ₁₂ : pt₁ ≡ pt₂
    σ₁₂ = is-contr→is-prop E₄c pt₁ pt₂

    σ₂₃ : pt₂ ≡ pt₃
    σ₂₃ = is-contr→is-prop E₄c pt₂ pt₃

    σ₃₅ : pt₃ ≡ pt₅
    σ₃₅ = is-contr→is-prop E₄c pt₃ pt₅

    α₁₄ : ((w ⊗ x) ⊗ y) ⊗ z ≡ (w ⊗ x) ⊗ (y ⊗ z)
    α₁₄ = ap fst σ₁₄

    α₄₅ : (w ⊗ x) ⊗ (y ⊗ z) ≡ w ⊗ (x ⊗ (y ⊗ z))
    α₄₅ = ap fst σ₄₅

    α₁₂ : ((w ⊗ x) ⊗ y) ⊗ z ≡ (w ⊗ (x ⊗ y)) ⊗ z
    α₁₂ = ap fst σ₁₂

    α₂₃ : (w ⊗ (x ⊗ y)) ⊗ z ≡ w ⊗ ((x ⊗ y) ⊗ z)
    α₂₃ = ap fst σ₂₃

    α₃₅ : w ⊗ ((x ⊗ y) ⊗ z) ≡ w ⊗ (x ⊗ (y ⊗ z))
    α₃₅ = ap fst σ₃₅

    private
      γ₁₂ : pt₁ ≡ pt₂
      γ₁₂ i =
        ⊗-assoc w x y i ⊗ z
        , tensor-emb-composite (⊗-assoc w x y i) z
        ∙ (λ j l r →
            assoc-σ w x y i .snd j l (pre z r))

      γ₃₅-pt : ∀ i → fiber tensor-emb (tensor-E₄ w x y z)
      γ₃₅-pt i =
        w ⊗ ⊗-assoc x y z i
        , tensor-emb-composite w (⊗-assoc x y z i)
        ∙ (λ j l r →
            tensor-emb w l
              (assoc-σ x y z i .snd j I r))

      v₃ : pt₃ ≡ γ₃₅-pt i0
      v₃ i = _
        , tensor-emb-composite w ((x ⊗ y) ⊗ z)
        ∙ tensor-emb-ext λ l r →
            sym (ap-comp (tensor-emb w l)
              (tensor-pre-composite (x ⊗ y) z r)
              (tensor-pre-composite x y
                (pre z r))) i

      v₅ : γ₃₅-pt i1 ≡ pt₅
      v₅ i = _
        , tensor-emb-composite w (x ⊗ (y ⊗ z))
        ∙ tensor-emb-ext λ l r →
            ap-comp (tensor-emb w l)
              (tensor-pre-composite x (y ⊗ z) r)
              (ap (pre x)
                (tensor-pre-composite y z r)) i

      γ₂₃-pt : ∀ i → fiber tensor-emb (tensor-E₄ w x y z)
      γ₂₃-pt i =
        ⊗-assoc w (x ⊗ y) z i
        , assoc-σ w (x ⊗ y) z i .snd
        ∙ tensor-emb-ext λ l r →
            ap (tensor-emb w l)
              (tensor-pre-composite x y (pre z r))

      w₂ : pt₂ ≡ γ₂₃-pt i0
      w₂ i = _
        , Path.assoc
            (tensor-emb-composite (w ⊗ (x ⊗ y)) z)
            (tensor-emb-ext λ l r →
                tensor-emb-comp-pt w (x ⊗ y) l (pre z r))
            (tensor-emb-ext λ l r →
                ap (tensor-emb w l)
                  (tensor-pre-composite x y (pre z r))) i

      w₃ : γ₂₃-pt i1 ≡ pt₃
      w₃ i = _
        , sym (Path.assoc
            (tensor-emb-composite w ((x ⊗ y) ⊗ z))
            (tensor-emb-ext λ l r →
                ap (tensor-emb w l)
                  (tensor-pre-composite (x ⊗ y) z r))
            (tensor-emb-ext λ l r →
                ap (tensor-emb w l)
                  (tensor-pre-composite x y (pre z r)))) i

      γ₄₅-pt : ∀ i → fiber tensor-emb (tensor-E₄ w x y z)
      γ₄₅-pt i =
        ⊗-assoc w x (y ⊗ z) i
        , assoc-σ w x (y ⊗ z) i .snd
        ∙ tensor-emb-ext λ l r →
            ap (λ t → tensor-emb w l (pre x t))
              (tensor-pre-composite y z r)

      w₄ : pt₄ ≡ γ₄₅-pt i0
      w₄ i = _
        , Path.assoc
            (tensor-emb-composite (w ⊗ x) (y ⊗ z))
            (tensor-emb-ext λ l r →
                tensor-emb-comp-pt w x l (pre (y ⊗ z) r))
            (tensor-emb-ext λ l r →
                ap (λ t → tensor-emb w l (pre x t))
                  (tensor-pre-composite y z r)) i

      w₅ : γ₄₅-pt i1 ≡ pt₅
      w₅ i = _
        , sym (Path.assoc
            (tensor-emb-composite w (x ⊗ (y ⊗ z)))
            (tensor-emb-ext λ l r →
                ap (tensor-emb w l)
                  (tensor-pre-composite x (y ⊗ z) r))
            (tensor-emb-ext λ l r →
                ap (λ t → tensor-emb w l (pre x t))
                  (tensor-pre-composite y z r))) i

      γ₁₄-pt : ∀ i → fiber tensor-emb (tensor-E₄ w x y z)
      γ₁₄-pt i =
        ⊗-assoc (w ⊗ x) y z i
        , assoc-σ (w ⊗ x) y z i .snd
        ∙ tensor-emb-ext λ l r →
            tensor-emb-comp-pt w x l (pre y (pre z r))

      w₁ : pt₁ ≡ γ₁₄-pt i0
      w₁ i = _
        , Path.assoc
            (tensor-emb-composite ((w ⊗ x) ⊗ y) z)
            (tensor-emb-ext λ l r →
                tensor-emb-comp-pt (w ⊗ x) y l (pre z r))
            (tensor-emb-ext λ l r →
                tensor-emb-comp-pt w x l
                  (pre y (pre z r))) i

      w₁₄-nat
        : (l r : ob)
        → ap (tensor-emb (w ⊗ x) l)
              (tensor-pre-composite y z r)
          ∙ tensor-emb-comp-pt w x l (pre y (pre z r))
        ≡ tensor-emb-comp-pt w x l (pre (y ⊗ z) r)
          ∙ ap (λ t → tensor-emb w l (pre x t))
              (tensor-pre-composite y z r)
      w₁₄-nat l r = sym (Path.commutes
        (tensor-emb-comp-pt w x l (pre (y ⊗ z) r))
        (ap (λ t → tensor-emb w l (pre x t))
          (tensor-pre-composite y z r))
        (ap (tensor-emb (w ⊗ x) l)
          (tensor-pre-composite y z r))
        (tensor-emb-comp-pt w x l (pre y (pre z r)))
        (λ i j → tensor-emb-comp-pt w x l
          (tensor-pre-composite y z r i) j))

      w₁₄ : γ₁₄-pt i1 ≡ pt₄
      w₁₄ i = _
        , (sym (Path.assoc A₁₄ B₁₄ C₁₄)
          ∙ ap (A₁₄ ∙_) N₁₄) i
        where
          A₁₄ = tensor-emb-composite (w ⊗ x) (y ⊗ z)
          B₁₄ = tensor-emb-ext λ l r →
              ap (tensor-emb (w ⊗ x) l)
                (tensor-pre-composite y z r)
          C₁₄ = tensor-emb-ext λ l r →
              tensor-emb-comp-pt w x l (pre y (pre z r))
          N₁₄ : B₁₄ ∙ C₁₄
              ≡ tensor-emb-ext λ l r →
                    tensor-emb-comp-pt w x l (pre (y ⊗ z) r)
                  ∙ ap (λ t → tensor-emb w l (pre x t))
                      (tensor-pre-composite y z r)
          N₁₄ j = tensor-emb-ext λ l r → w₁₄-nat l r j

    face₁₂ : α₁₂ ≡ ap (_⊗ z) (⊗-assoc w x y)
    face₁₂ = total-contr-unique E₄c
      α₁₂ (ap (_⊗ z) (⊗-assoc w x y))
      (ap snd σ₁₂)
      (ap snd γ₁₂)

    face₃₅ : α₃₅ ≡ ap (w ⊗_) (⊗-assoc x y z)
    face₃₅ =
      contr-face E₄c σ₃₅
        (ap snd v₃) (λ i → γ₃₅-pt i) (ap snd v₅)

    face₂₃ : α₂₃ ≡ ⊗-assoc w (x ⊗ y) z
    face₂₃ =
      contr-face E₄c σ₂₃
        (ap snd w₂) (λ i → γ₂₃-pt i) (ap snd w₃)

    face₄₅ : α₄₅ ≡ ⊗-assoc w x (y ⊗ z)
    face₄₅ =
      contr-face E₄c σ₄₅
        (ap snd w₄) (λ i → γ₄₅-pt i) (ap snd w₅)

    face₁₄ : α₁₄ ≡ ⊗-assoc (w ⊗ x) y z
    face₁₄ =
      contr-face E₄c σ₁₄
        (ap snd w₁) (λ i → γ₁₄-pt i) (ap snd w₁₄)
```

## Pentagon

```agda
  module pentagon (w x y z : ob) where
    open pentagon-fibers w x y z

    hom-identity
      : α₁₄ ∙ α₄₅ ≡ pcom (sym α₁₂) α₂₃ α₃₅
    hom-identity =
      coh-project E₄c fst (σ₁₄ ∙ σ₄₅) (pcom (sym σ₁₂) σ₂₃ σ₃₅)
        (ap-comp fst σ₁₄ σ₄₅)
        (pcom.ap (λ _ → fst) (sym σ₁₂) σ₂₃ σ₃₅)

  ⊗-pentagon
    : (w x y z : ob)
    → ⊗-assoc (w ⊗ x) y z ∙ ⊗-assoc w x (y ⊗ z)
    ≡ ap (_⊗ z) (⊗-assoc w x y)
      ∙ ⊗-assoc w (x ⊗ y) z
      ∙ ap (w ⊗_) (⊗-assoc x y z)
  ⊗-pentagon w x y z =
    pcom (ap (_∙ α₄₅) face₁₄
        ∙ ap (⊗-assoc (w ⊗ x) y z ∙_) face₄₅)
      hom-identity
      (λ i → pcom
        (sym (face₁₂ i)) (face₂₃ i) (face₃₅ i))
    ∙ pcom→∙
        (ap (_⊗ z) (⊗-assoc w x y))
        (⊗-assoc w (x ⊗ y) z)
        (ap (w ⊗_) (⊗-assoc x y z))
    where
      open pentagon-fibers w x y z
      open pentagon w x y z
```

## Weak triangle

The weak triangle uses only `absorb-l` from the unit, not
`absorb-coh`. The `α₂₃` edge remains abstract.

```agda
  module triangle-fibers (x z : ob) where
    private
      cc = tensor-compose-contr x z

      pt₁ : fiber tensor-emb
        (λ l r → tensor-emb x l (pre z r))
      pt₁ = (x ⊗ I) ⊗ z
          , tensor-emb-composite (x ⊗ I) z
          ∙ tensor-emb-ext λ l r →
              tensor-emb-comp-pt x I l (pre z r)
            ∙ ap (tensor-emb x l)
                (absorb-l (pre z r))

      pt₂ : fiber tensor-emb
        (λ l r → tensor-emb x l (pre z r))
      pt₂ = x ⊗ (I ⊗ z)
          , tensor-emb-composite x (I ⊗ z)
          ∙ tensor-emb-ext λ l r →
              ap (tensor-emb x l)
                (tensor-pre-composite I z r)
            ∙ ap (tensor-emb x l)
                (absorb-l (pre z r))

      pt₃ : fiber tensor-emb
        (λ l r → tensor-emb x l (pre z r))
      pt₃ = x ⊗ z , tensor-emb-composite x z

    σ₁₃ : pt₁ ≡ pt₃
    σ₁₃ = is-contr→is-prop cc pt₁ pt₃

    σ₁₂ : pt₁ ≡ pt₂
    σ₁₂ = is-contr→is-prop cc pt₁ pt₂

    σ₂₃ : pt₂ ≡ pt₃
    σ₂₃ = is-contr→is-prop cc pt₂ pt₃

    α₁₃ : (x ⊗ I) ⊗ z ≡ x ⊗ z
    α₁₃ = ap fst σ₁₃

    α₁₂ : (x ⊗ I) ⊗ z ≡ x ⊗ (I ⊗ z)
    α₁₂ = ap fst σ₁₂

    α₂₃ : x ⊗ (I ⊗ z) ≡ x ⊗ z
    α₂₃ = ap fst σ₂₃

    private
      unitr-σ
        : (   x ⊗ I
            , tensor-emb-composite x I
            ∙ tensor-emb-ext λ l r →
                ap (tensor-emb x l) (absorb-l r))
        ≡ (x , refl)
      unitr-σ =
        is-contr→is-prop
          (tensor-emb-image-contr-ext x) _ _

      γ₁₃-pt : ∀ i → fiber tensor-emb
        (λ l r → tensor-emb x l (pre z r))
      γ₁₃-pt i =
        ⊗-unitr x i ⊗ z
        , tensor-emb-composite (⊗-unitr x i) z
        ∙ (λ j l r →
            unitr-σ i .snd j l (pre z r))

      v₃ : γ₁₃-pt i1 ≡ pt₃
      v₃ i = _ , Path.unitr (tensor-emb-composite x z) i

      γ₁₂-pt : ∀ i → fiber tensor-emb
        (λ l r → tensor-emb x l (pre z r))
      γ₁₂-pt i =
        ⊗-assoc x I z i
        , assoc-σ x I z i .snd
        ∙ tensor-emb-ext λ l r →
            ap (tensor-emb x l)
              (absorb-l (pre z r))

      w₁ : pt₁ ≡ γ₁₂-pt i0
      w₁ i = _
        , Path.assoc
            (tensor-emb-composite (x ⊗ I) z)
            (tensor-emb-ext λ l r →
                tensor-emb-comp-pt x I l (pre z r))
            (tensor-emb-ext λ l r →
                ap (tensor-emb x l)
                  (absorb-l (pre z r))) i

      w₂ : γ₁₂-pt i1 ≡ pt₂
      w₂ i = _
        , sym (Path.assoc
            (tensor-emb-composite x (I ⊗ z))
            (tensor-emb-ext λ l r →
                ap (tensor-emb x l)
                  (tensor-pre-composite I z r))
            (tensor-emb-ext λ l r →
                ap (tensor-emb x l)
                  (absorb-l (pre z r)))) i

    face₁₃ : α₁₃ ≡ ap (_⊗ z) (⊗-unitr x)
    face₁₃ =
      contr-face cc σ₁₃
        refl (λ i → γ₁₃-pt i) (ap snd v₃)

    face₁₂ : α₁₂ ≡ ⊗-assoc x I z
    face₁₂ =
      contr-face cc σ₁₂
        (ap snd w₁) (λ i → γ₁₂-pt i) (ap snd w₂)

  module triangle (x z : ob) where
    open triangle-fibers x z

    hom-identity
      : α₁₃ ≡ α₁₂ ∙ α₂₃
    hom-identity =
      coh-project (tensor-compose-contr x z) fst σ₁₃ (σ₁₂ ∙ σ₂₃) refl
        (ap-comp fst σ₁₂ σ₂₃)

  ⊗-triangle-weak
    : (x z : ob)
    → ap (_⊗ z) (⊗-unitr x)
    ≡ ⊗-assoc x I z ∙ triangle-fibers.α₂₃ x z
  ⊗-triangle-weak x z =
    pcom face₁₃
      hom-identity
      (ap (_∙ α₂₃) face₁₂)
    where open triangle-fibers x z
          open triangle x z
```

## 2-coherence

The `absorb-coh` field is the additional coherence needed to
identify `α₂₃` with `ap (x ⊗_) (⊗-unitl z)` and obtain the
full Mac Lane triangle identity.

```agda
record monoidal-2-coherent {o h}
  {C : category o h} (M : monoidal C) : Type (o ⊔ h)
  where
  open monoidal M
  open category C using (ob)
  field
    absorb-coh
      : (x r : ob)
      → absorb-l (pre x r)
      ≡ tensor-interchange I x I r
        ∙ ap (λ t → tensor-emb x t r)
            (absorb-r I)
```

## Full Mac Lane triangle

The `⊗-2-Cat` module opens both `monoidal M` and
`monoidal-2-coherent coh`, then derives the full triangle
`ap (_⊗ z) (⊗-unitr x) ≡ ⊗-assoc x I z ∙ ap (x ⊗_) (⊗-unitl z)`
using `absorb-coh` to identify the abstract `α₂₃` edge.

```agda
module ⊗-2-Cat
  {o h} {C : category o h}
  (M : monoidal C)
  (coh : monoidal-2-coherent M)
  where
  open monoidal M public
  open monoidal-2-coherent coh public
  open category C using (ob)

  absorb-l-pre-retract
    : (x r : ob)
    → tensor-emb-pre x I r ∙ absorb-l (pre x r)
    ≡ refl
  absorb-l-pre-retract x r =
    ap (tensor-emb-pre x I r ∙_)
      (absorb-coh x r)
    ∙ Path.grp-cancel
        (ap (λ t → tensor-emb x t r)
          (absorb-r I))
        (tensor-interchange I x I r)
```

### Full triangle face₂₃

The `face₂₃` identification requires `absorb-l-pre-retract`,
which in turn requires `absorb-coh`. This is what separates
the full Mac Lane triangle from the weak version.

```agda
  private
    module face₂₃-proof (x z : ob) where
      open triangle-fibers M x z

      private
        cc = tensor-compose-contr x z

        pt₂ : fiber tensor-emb
          (λ l r →
            tensor-emb x l (pre z r))
        pt₂ = x ⊗ (I ⊗ z)
            , tensor-emb-composite x (I ⊗ z)
            ∙ tensor-emb-ext λ l r →
                ap (tensor-emb x l)
                  (tensor-pre-composite I z r)
              ∙ ap (tensor-emb x l)
                  (absorb-l (pre z r))

        pt₃ : fiber tensor-emb
          (λ l r →
            tensor-emb x l (pre z r))
        pt₃ = x ⊗ z , tensor-emb-composite x z

        unitl-σ
          : (   I ⊗ z
              , tensor-emb-composite I z)
          ≡ (   z
              , tensor-emb-ext λ l r →
                  tensor-emb-pre z l r)
        unitl-σ =
          is-contr→is-prop
            (tensor-compose-contr I z) _ _

        γ₂₃-pt : ∀ i → fiber tensor-emb
          (λ l r →
            tensor-emb x l (pre z r))
        γ₂₃-pt i =
          x ⊗ (⊗-unitl z i)
          , tensor-emb-composite x (⊗-unitl z i)
          ∙ tensor-emb-ext λ l r →
              ap (tensor-emb x l)
                ((λ j →
                    unitl-σ i .snd j I r)
                ∙ absorb-l (pre z r))

        w₀ : pt₂ ≡ γ₂₃-pt i0
        w₀ i = _
          , tensor-emb-composite x (I ⊗ z)
          ∙ tensor-emb-ext λ l r →
              sym (ap-comp (tensor-emb x l)
                (tensor-pre-composite I z r)
                (absorb-l (pre z r))) i

        v₁ : γ₂₃-pt i1
          ≡ (x ⊗ z
            , tensor-emb-composite x z ∙ refl)
        v₁ i = _
          , tensor-emb-composite x z
          ∙ tensor-emb-ext λ l r →
              ap (ap (tensor-emb x l))
                (absorb-l-pre-retract z r) i

        v₂
          : (x ⊗ z
            , tensor-emb-composite x z ∙ refl)
          ≡ pt₃
        v₂ i = _
          , Path.unitr (tensor-emb-composite x z) i

      face₂₃ : α₂₃ ≡ ap (x ⊗_) (⊗-unitl z)
      face₂₃ =
        contr-face cc σ₂₃
          (ap snd w₀) (λ i → γ₂₃-pt i)
          (ap snd v₁ ∙ ap snd v₂)

  ⊗-triangle
    : (x z : ob)
    → ap (_⊗ z) (⊗-unitr x)
    ≡ ⊗-assoc x I z ∙ ap (x ⊗_) (⊗-unitl z)
  ⊗-triangle x z =
    pcom face₁₃
      hom-identity
      (ap (_∙ α₂₃) face₁₂
      ∙ ap (⊗-assoc x I z ∙_) face₂₃)
    where open triangle-fibers M x z
          open triangle M x z
          open face₂₃-proof x z
```
