Lane Biocini
July 2026

Native pentagon coherence for the monoidal tensor. This is
the erased-object-index image of the pentagon section of
`Cat.Coherence`, applied to `tensor-emb` in place of the
delooped `emb`. The five reassociations of a fourfold tensor
sit in a fiber over `tensor-E₄` that the base axioms make
contractible; the pentagon is the `ap fst` image of the two
traversals of that fiber agreeing, forced by
`is-contr→is-set`. Triangle coherence extends this same
submodule in a later pass.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Coherence where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base using (contr-ind)
open import Core.Transport.J using (subst)
open import Core.Path.Base using (ap-comp)
open import Cat.Type
open import Cat.Monoidal
```

## The fourfold composite fiber

```agda
module _ {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  open category C using (ob)

  private
    tensor-E₄ : (w x y z : ob) → ob → ob → ob
    tensor-E₄ w x y z l r =
      tensor-emb w l (noy x (noy y (noy z r)))

  tensor-E₄-contr
    : (w x y z : ob)
    → is-contr (fiber tensor-emb (tensor-E₄ w x y z))
  tensor-E₄-contr w x y z .center .fst = ((w ⊗ x) ⊗ y) ⊗ z
  tensor-E₄-contr w x y z .center .snd =
    tensor-emb-composite ((w ⊗ x) ⊗ y) z
    ∙ tensor-emb-ext λ l r →
        tensor-emb-comp-pt (w ⊗ x) y l (noy z r)
      ∙ tensor-emb-comp-pt w x l (noy y (noy z r))
  tensor-E₄-contr w x y z .paths =
    is-contr→is-prop
      (subst (is-contr ∘ fiber tensor-emb) path
        (tensor-compose-contr ((w ⊗ x) ⊗ y) z)) _
    where
      path
        : (λ l r → tensor-emb ((w ⊗ x) ⊗ y) l (noy z r))
        ≡ tensor-E₄ w x y z
      path = tensor-emb-ext λ l r →
          tensor-emb-comp-pt (w ⊗ x) y l (noy z r)
        ∙ tensor-emb-comp-pt w x l (noy y (noy z r))

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

```agda
  private
    assoc-σ
      : (x y z : ob)
      → tensor-E₃-contr-ext x y z .center
      ≡ ( x ⊗ (y ⊗ z)
        , tensor-emb-composite x (y ⊗ z)
        ∙ tensor-emb-ext λ l r →
            ap (tensor-emb x l) (tensor-noy-composite y z r))
    assoc-σ x y z =
      is-contr→is-prop (tensor-E₃-contr-ext x y z) _ _
```

## Pentagon fibers

```agda
  module pentagon-fibers (w x y z : ob) where
    private
      E₄c = tensor-E₄-contr w x y z

      pt₁ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₁ = E₄c .center

      pt₂ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₂ = (w ⊗ (x ⊗ y)) ⊗ z
          , tensor-emb-composite (w ⊗ (x ⊗ y)) z
          ∙ tensor-emb-ext λ l r →
              tensor-emb-comp-pt w (x ⊗ y) l (noy z r)
            ∙ ap (tensor-emb w l)
                (tensor-noy-composite x y (noy z r))

      pt₃ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₃ = w ⊗ ((x ⊗ y) ⊗ z)
          , tensor-emb-composite w ((x ⊗ y) ⊗ z)
          ∙ tensor-emb-ext λ l r →
              ap (tensor-emb w l)
                (tensor-noy-composite (x ⊗ y) z r)
            ∙ ap (tensor-emb w l)
                (tensor-noy-composite x y (noy z r))

      pt₄ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₄ = (w ⊗ x) ⊗ (y ⊗ z)
          , tensor-emb-composite (w ⊗ x) (y ⊗ z)
          ∙ tensor-emb-ext λ l r →
              tensor-emb-comp-pt w x l (noy (y ⊗ z) r)
            ∙ ap (λ t → tensor-emb w l (noy x t))
                  (tensor-noy-composite y z r)

      pt₅ : fiber tensor-emb (tensor-E₄ w x y z)
      pt₅ = w ⊗ (x ⊗ (y ⊗ z))
          , tensor-emb-composite w (x ⊗ (y ⊗ z))
          ∙ tensor-emb-ext λ l r →
              ap (tensor-emb w l)
                (tensor-noy-composite x (y ⊗ z) r)
            ∙ ap (λ t → tensor-emb w l (noy x t))
                  (tensor-noy-composite y z r)

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

    identity : σ₁₄ ∙ σ₄₅ ≡ pcom (sym σ₁₂) σ₂₃ σ₃₅
    identity = is-contr→is-set E₄c pt₁ pt₅
      (σ₁₄ ∙ σ₄₅) (pcom (sym σ₁₂) σ₂₃ σ₃₅)

    private
      γ₁₂ : pt₁ ≡ pt₂
      γ₁₂ i =
        ⊗-assoc w x y i ⊗ z
        , tensor-emb-composite (⊗-assoc w x y i) z
        ∙ (λ j l r →
            assoc-σ w x y i .snd j l (noy z r))

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
              (tensor-noy-composite (x ⊗ y) z r)
              (tensor-noy-composite x y
                (noy z r))) i

      v₅ : γ₃₅-pt i1 ≡ pt₅
      v₅ i = _
        , tensor-emb-composite w (x ⊗ (y ⊗ z))
        ∙ tensor-emb-ext λ l r →
            ap-comp (tensor-emb w l)
              (tensor-noy-composite x (y ⊗ z) r)
              (ap (noy x)
                (tensor-noy-composite y z r)) i

      γ₂₃-pt : ∀ i → fiber tensor-emb (tensor-E₄ w x y z)
      γ₂₃-pt i =
        ⊗-assoc w (x ⊗ y) z i
        , assoc-σ w (x ⊗ y) z i .snd
        ∙ tensor-emb-ext λ l r →
            ap (tensor-emb w l)
              (tensor-noy-composite x y (noy z r))

      w₂ : pt₂ ≡ γ₂₃-pt i0
      w₂ i = _
        , Path.assoc
            (tensor-emb-composite (w ⊗ (x ⊗ y)) z)
            (tensor-emb-ext λ l r →
                tensor-emb-comp-pt w (x ⊗ y) l (noy z r))
            (tensor-emb-ext λ l r →
                ap (tensor-emb w l)
                  (tensor-noy-composite x y (noy z r))) i

      w₃ : γ₂₃-pt i1 ≡ pt₃
      w₃ i = _
        , sym (Path.assoc
            (tensor-emb-composite w ((x ⊗ y) ⊗ z))
            (tensor-emb-ext λ l r →
                ap (tensor-emb w l)
                  (tensor-noy-composite (x ⊗ y) z r))
            (tensor-emb-ext λ l r →
                ap (tensor-emb w l)
                  (tensor-noy-composite x y (noy z r)))) i

      γ₄₅-pt : ∀ i → fiber tensor-emb (tensor-E₄ w x y z)
      γ₄₅-pt i =
        ⊗-assoc w x (y ⊗ z) i
        , assoc-σ w x (y ⊗ z) i .snd
        ∙ tensor-emb-ext λ l r →
            ap (λ t → tensor-emb w l (noy x t))
              (tensor-noy-composite y z r)

      w₄ : pt₄ ≡ γ₄₅-pt i0
      w₄ i = _
        , Path.assoc
            (tensor-emb-composite (w ⊗ x) (y ⊗ z))
            (tensor-emb-ext λ l r →
                tensor-emb-comp-pt w x l (noy (y ⊗ z) r))
            (tensor-emb-ext λ l r →
                ap (λ t → tensor-emb w l (noy x t))
                  (tensor-noy-composite y z r)) i

      w₅ : γ₄₅-pt i1 ≡ pt₅
      w₅ i = _
        , sym (Path.assoc
            (tensor-emb-composite w (x ⊗ (y ⊗ z)))
            (tensor-emb-ext λ l r →
                ap (tensor-emb w l)
                  (tensor-noy-composite x (y ⊗ z) r))
            (tensor-emb-ext λ l r →
                ap (λ t → tensor-emb w l (noy x t))
                  (tensor-noy-composite y z r))) i

      γ₁₄-pt : ∀ i → fiber tensor-emb (tensor-E₄ w x y z)
      γ₁₄-pt i =
        ⊗-assoc (w ⊗ x) y z i
        , assoc-σ (w ⊗ x) y z i .snd
        ∙ tensor-emb-ext λ l r →
            tensor-emb-comp-pt w x l (noy y (noy z r))

      w₁ : pt₁ ≡ γ₁₄-pt i0
      w₁ i = _
        , Path.assoc
            (tensor-emb-composite ((w ⊗ x) ⊗ y) z)
            (tensor-emb-ext λ l r →
                tensor-emb-comp-pt (w ⊗ x) y l (noy z r))
            (tensor-emb-ext λ l r →
                tensor-emb-comp-pt w x l
                  (noy y (noy z r))) i

      w₁₄-nat
        : (l r : ob)
        → ap (tensor-emb (w ⊗ x) l)
              (tensor-noy-composite y z r)
          ∙ tensor-emb-comp-pt w x l (noy y (noy z r))
        ≡ tensor-emb-comp-pt w x l (noy (y ⊗ z) r)
          ∙ ap (λ t → tensor-emb w l (noy x t))
              (tensor-noy-composite y z r)
      w₁₄-nat l r = sym (Path.commutes
        (tensor-emb-comp-pt w x l (noy (y ⊗ z) r))
        (ap (λ t → tensor-emb w l (noy x t))
          (tensor-noy-composite y z r))
        (ap (tensor-emb (w ⊗ x) l)
          (tensor-noy-composite y z r))
        (tensor-emb-comp-pt w x l (noy y (noy z r)))
        (λ i j → tensor-emb-comp-pt w x l
          (tensor-noy-composite y z r i) j))

      w₁₄ : γ₁₄-pt i1 ≡ pt₄
      w₁₄ i = _
        , (sym (Path.assoc A₁₄ B₁₄ C₁₄)
          ∙ ap (A₁₄ ∙_) N₁₄) i
        where
          A₁₄ = tensor-emb-composite (w ⊗ x) (y ⊗ z)
          B₁₄ = tensor-emb-ext λ l r →
              ap (tensor-emb (w ⊗ x) l)
                (tensor-noy-composite y z r)
          C₁₄ = tensor-emb-ext λ l r →
              tensor-emb-comp-pt w x l (noy y (noy z r))
          N₁₄ : B₁₄ ∙ C₁₄
              ≡ tensor-emb-ext λ l r →
                    tensor-emb-comp-pt w x l (noy (y ⊗ z) r)
                  ∙ ap (λ t → tensor-emb w l (noy x t))
                      (tensor-noy-composite y z r)
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
      pcom (ap-comp fst σ₁₄ σ₄₅)
        (ap (ap fst) identity)
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
      pcom→∙
        : ∀ {u} {A : Type u} {a b c d : A}
          (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
        → pcom (sym p) q r ≡ p ∙ q ∙ r
      pcom→∙ p q r = pcom.unique
        (sym p) q r
        (p ∙ q ∙ r , cat.lcoh p q r)
```

## Deferred

Triangle coherence — the weak triangle from the base axioms,
the `2-coherent` record supplying `absorb-coh`, and the full
Mac Lane triangle — is the next pass and extends this
submodule, mirroring the triangle section of `Cat.Coherence`.
