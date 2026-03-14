Lane Biocini
March 2026

Pentagon and triangle coherences for virtual categories.
The pentagon identity holds from the base axioms. The weak
triangle holds from base. The full Mac Lane triangle requires
`2-coherent`, which provides `absorb-coh`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Coherence where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
open import Core.Path.Base using (ap-comp)
open import Cat.Virtual
```

## Pentagon

```agda
module _ {o h} (C : category o h) where
  open Virtual C

  private
    E₄ : ∀ {x y z w v} (f : hom x y) (g : hom y z)
        (h : hom z w) (k : hom w v)
      → ∀ w' → hom w' x → ∀ v' → hom v v' → hom w' v'
    E₄ f g h k =
      λ w a v b →
        emb f w a v (noy g v (noy h v (noy k v b)))

  E₄-contr
    : ∀ {x y z w v} (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w v)
    → is-contr (fiber emb (E₄ f g h k))
  E₄-contr f g h k .center .fst = ((f ⨾ g) ⨾ h) ⨾ k
  E₄-contr f g h k .center .snd =
    emb-composite ((f ⨾ g) ⨾ h) k
    ∙ emb-ext λ w a v b →
        emb-composite-pt (f ⨾ g) h w a v
          (noy k v b)
      ∙ emb-composite-pt f g w a v
          (noy h v (noy k v b))
  E₄-contr f g h k .paths =
    is-contr→is-prop
      (subst (is-contr ∘ fiber emb) path
        (composable-contr ((f ⨾ g) ⨾ h) k)) _
    where
      path : (λ w a v b →
                emb ((f ⨾ g) ⨾ h) w a v (noy k v b))
            ≡ E₄ f g h k
      path = emb-ext λ w a v b →
          emb-composite-pt (f ⨾ g) h w a v (noy k v b)
        ∙ emb-composite-pt f g w a v
            (noy h v (noy k v b))

  E₄-ind
    : ∀ {u} {x y z w v} (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w v)
    → (P : (s : hom x v)
         → emb s ≡ E₄ f g h k
         → Type u)
    → P (E₄-contr f g h k .center .fst)
        (E₄-contr f g h k .center .snd)
    → ∀ s q → P s q
  E₄-ind f g h k P base s q =
    contr-ind (E₄-contr f g h k)
      (λ where (s , q) → P s q)
      base (s , q)

  module pentagon-fibers
    {x y z w v}
    (f : hom x y) (g : hom y z)
    (h : hom z w) (k : hom w v)
    where
    private
      E₄c = E₄-contr f g h k

      pt₁ : fiber emb (E₄ f g h k)
      pt₁ = E₄c .center

      pt₂ : fiber emb (E₄ f g h k)
      pt₂ = (f ⨾ (g ⨾ h)) ⨾ k
          , emb-composite (f ⨾ (g ⨾ h)) k
          ∙ emb-ext λ w a v b →
              emb-composite-pt f (g ⨾ h) w a v
                (noy k v b)
            ∙ ap (emb f w a v)
                (noy-composite g h (noy k v b))

      pt₃ : fiber emb (E₄ f g h k)
      pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
          , emb-composite f ((g ⨾ h) ⨾ k)
          ∙ emb-ext λ w a v b →
              ap (emb f w a v)
                (noy-composite (g ⨾ h) k b)
            ∙ ap (emb f w a v)
                (noy-composite g h (noy k v b))

      pt₄ : fiber emb (E₄ f g h k)
      pt₄ = (f ⨾ g) ⨾ (h ⨾ k)
          , emb-composite (f ⨾ g) (h ⨾ k)
          ∙ emb-ext λ w a v b →
              emb-composite-pt f g w a v
                (noy (h ⨾ k) v b)
            ∙ ap (λ t → emb f w a v (noy g v t))
                  (noy-composite h k b)

      pt₅ : fiber emb (E₄ f g h k)
      pt₅ = f ⨾ (g ⨾ (h ⨾ k))
          , emb-composite f (g ⨾ (h ⨾ k))
          ∙ emb-ext λ w a v b →
              ap (emb f w a v)
                (noy-composite g (h ⨾ k) b)
            ∙ ap (λ t → emb f w a v (noy g v t))
                  (noy-composite h k b)

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

    α₁₄ : ((f ⨾ g) ⨾ h) ⨾ k ≡ (f ⨾ g) ⨾ (h ⨾ k)
    α₁₄ = ap fst σ₁₄

    α₄₅ : (f ⨾ g) ⨾ (h ⨾ k) ≡ f ⨾ (g ⨾ (h ⨾ k))
    α₄₅ = ap fst σ₄₅

    α₁₂ : ((f ⨾ g) ⨾ h) ⨾ k ≡ (f ⨾ (g ⨾ h)) ⨾ k
    α₁₂ = ap fst σ₁₂

    α₂₃ : (f ⨾ (g ⨾ h)) ⨾ k ≡ f ⨾ ((g ⨾ h) ⨾ k)
    α₂₃ = ap fst σ₂₃

    α₃₅ : f ⨾ ((g ⨾ h) ⨾ k) ≡ f ⨾ (g ⨾ (h ⨾ k))
    α₃₅ = ap fst σ₃₅

    identity : σ₁₄ ∙ σ₄₅ ≡ pcom (sym σ₁₂) σ₂₃ σ₃₅
    identity = is-contr→is-set E₄c pt₁ pt₅
      (σ₁₄ ∙ σ₄₅) (pcom (sym σ₁₂) σ₂₃ σ₃₅)

    private
      assoc-σ
        : ∀ {x y z w}
          (f : hom x y) (g : hom y z) (h : hom z w)
        → E₃-contr f g h .center
        ≡ (   f ⨾ (g ⨾ h)
            , emb-composite f (g ⨾ h)
            ∙ emb-ext λ w' a v' b →
                ap (emb f w' a v')
                  (noy-composite g h b))
      assoc-σ f g h =
        is-contr→is-prop (E₃-contr f g h) _ _

      γ₁₂ : pt₁ ≡ pt₂
      γ₁₂ i =
        assoc f g h i ⨾ k
        , emb-composite (assoc f g h i) k
        ∙ (λ j w' a v' b →
            assoc-σ f g h i .snd j w' a v'
              (noy k v' b))

      γ₃₅-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₃₅-pt i =
        f ⨾ assoc g h k i
        , emb-composite f (assoc g h k i)
        ∙ (λ j w' a v' b →
            emb f w' a v'
              (assoc-σ g h k i .snd j _ idn v' b))

      v₃ : pt₃ ≡ γ₃₅-pt i0
      v₃ i =
        f ⨾ ((g ⨾ h) ⨾ k)
        , emb-composite f ((g ⨾ h) ⨾ k)
        ∙ emb-ext λ w' a v' b →
            sym (ap-comp (emb f w' a v')
              (noy-composite (g ⨾ h) k b)
              (noy-composite g h (noy k v' b))) i

      v₅ : γ₃₅-pt i1 ≡ pt₅
      v₅ i =
        f ⨾ (g ⨾ (h ⨾ k))
        , emb-composite f (g ⨾ (h ⨾ k))
        ∙ emb-ext λ w' a v' b →
            ap-comp (emb f w' a v')
              (noy-composite g (h ⨾ k) b)
              (ap (noy g v') (noy-composite h k b)) i

      γ₂₃-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₂₃-pt i =
        assoc f (g ⨾ h) k i
        , assoc-σ f (g ⨾ h) k i .snd
        ∙ emb-ext λ w' a v' b →
            ap (emb f w' a v')
              (noy-composite g h (noy k v' b))

      w₂ : pt₂ ≡ γ₂₃-pt i0
      w₂ i =
        (f ⨾ (g ⨾ h)) ⨾ k
        , Path.assoc
            (emb-composite (f ⨾ (g ⨾ h)) k)
            (emb-ext λ w' a v' b →
                emb-composite-pt f (g ⨾ h) w' a v'
                  (noy k v' b))
            (emb-ext λ w' a v' b →
                ap (emb f w' a v')
                  (noy-composite g h (noy k v' b))) i

      w₃ : γ₂₃-pt i1 ≡ pt₃
      w₃ i =
        f ⨾ ((g ⨾ h) ⨾ k)
        , sym (Path.assoc
            (emb-composite f ((g ⨾ h) ⨾ k))
            (emb-ext λ w' a v' b →
                ap (emb f w' a v')
                  (noy-composite (g ⨾ h) k b))
            (emb-ext λ w' a v' b →
                ap (emb f w' a v')
                  (noy-composite g h (noy k v' b)))) i

      γ₄₅-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₄₅-pt i =
        assoc f g (h ⨾ k) i
        , assoc-σ f g (h ⨾ k) i .snd
        ∙ emb-ext λ w' a v' b →
            ap (λ t → emb f w' a v' (noy g v' t))
              (noy-composite h k b)

      w₄ : pt₄ ≡ γ₄₅-pt i0
      w₄ i =
        (f ⨾ g) ⨾ (h ⨾ k)
        , Path.assoc
            (emb-composite (f ⨾ g) (h ⨾ k))
            (emb-ext λ w' a v' b →
                emb-composite-pt f g w' a v'
                  (noy (h ⨾ k) v' b))
            (emb-ext λ w' a v' b →
                ap (λ t → emb f w' a v' (noy g v' t))
                  (noy-composite h k b)) i

      w₅ : γ₄₅-pt i1 ≡ pt₅
      w₅ i =
        f ⨾ (g ⨾ (h ⨾ k))
        , sym (Path.assoc
            (emb-composite f (g ⨾ (h ⨾ k)))
            (emb-ext λ w' a v' b →
                ap (emb f w' a v')
                  (noy-composite g (h ⨾ k) b))
            (emb-ext λ w' a v' b →
                ap (λ t → emb f w' a v' (noy g v' t))
                  (noy-composite h k b))) i

      γ₁₄-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₁₄-pt i =
        assoc (f ⨾ g) h k i
        , assoc-σ (f ⨾ g) h k i .snd
        ∙ emb-ext λ w' a v' b →
            emb-composite-pt f g w' a v'
              (noy h v' (noy k v' b))

      w₁ : pt₁ ≡ γ₁₄-pt i0
      w₁ i =
        ((f ⨾ g) ⨾ h) ⨾ k
        , Path.assoc
            (emb-composite ((f ⨾ g) ⨾ h) k)
            (emb-ext λ w' a v' b →
                emb-composite-pt (f ⨾ g) h w' a v'
                  (noy k v' b))
            (emb-ext λ w' a v' b →
                emb-composite-pt f g w' a v'
                  (noy h v' (noy k v' b))) i

      w₁₄-nat : ∀ w' (a : hom w' x) v' (b : hom v v')
        → ap (emb (f ⨾ g) w' a v') (noy-composite h k b)
          ∙ emb-composite-pt f g w' a v'
              (noy h v' (noy k v' b))
        ≡ emb-composite-pt f g w' a v' (noy (h ⨾ k) v' b)
          ∙ ap (λ t → emb f w' a v' (noy g v' t))
                (noy-composite h k b)
      w₁₄-nat w' a v' b = sym (Path.commutes
        (emb-composite-pt f g w' a v' (noy (h ⨾ k) v' b))
        (ap (λ t → emb f w' a v' (noy g v' t))
          (noy-composite h k b))
        (ap (emb (f ⨾ g) w' a v') (noy-composite h k b))
        (emb-composite-pt f g w' a v'
          (noy h v' (noy k v' b)))
        (λ i j → emb-composite-pt f g w' a v'
          (noy-composite h k b i) j))

      w₁₄ : γ₁₄-pt i1 ≡ pt₄
      w₁₄ i =
        (f ⨾ g) ⨾ (h ⨾ k)
        , (sym (Path.assoc A₁₄ B₁₄ C₁₄) ∙ ap (A₁₄ ∙_) N₁₄) i
        where
          A₁₄ = emb-composite (f ⨾ g) (h ⨾ k)
          B₁₄ = emb-ext λ w' a v' b →
              ap (emb (f ⨾ g) w' a v')
                (noy-composite h k b)
          C₁₄ = emb-ext λ w' a v' b →
              emb-composite-pt f g w' a v'
                (noy h v' (noy k v' b))
          N₁₄ : B₁₄ ∙ C₁₄
              ≡ emb-ext λ w' a v' b →
                    emb-composite-pt f g w' a v'
                      (noy (h ⨾ k) v' b)
                  ∙ ap (λ t → emb f w' a v' (noy g v' t))
                        (noy-composite h k b)
          N₁₄ j = emb-ext λ w' a v' b →
              w₁₄-nat w' a v' b j

    face₁₂ : α₁₂ ≡ ap (_⨾ k) (assoc f g h)
    face₁₂ = total-contr-unique E₄c
      α₁₂ (ap (_⨾ k) (assoc f g h))
      (ap snd σ₁₂)
      (ap snd γ₁₂)

    face₃₅ : α₃₅ ≡ ap (f ⨾_) (assoc g h k)
    face₃₅ =
      contr-face E₄c σ₃₅
        (ap snd v₃) (λ i → γ₃₅-pt i) (ap snd v₅)

    face₂₃ : α₂₃ ≡ assoc f (g ⨾ h) k
    face₂₃ =
      contr-face E₄c σ₂₃
        (ap snd w₂) (λ i → γ₂₃-pt i) (ap snd w₃)

    face₄₅ : α₄₅ ≡ assoc f g (h ⨾ k)
    face₄₅ =
      contr-face E₄c σ₄₅
        (ap snd w₄) (λ i → γ₄₅-pt i) (ap snd w₅)

    face₁₄ : α₁₄ ≡ assoc (f ⨾ g) h k
    face₁₄ =
      contr-face E₄c σ₁₄
        (ap snd w₁) (λ i → γ₁₄-pt i) (ap snd w₁₄)

  module pentagon
    {x y z w v}
    (f : hom x y) (g : hom y z)
    (h : hom z w) (k : hom w v)
    where
    open pentagon-fibers f g h k

    hom-identity
      : α₁₄ ∙ α₄₅ ≡ pcom (sym α₁₂) α₂₃ α₃₅
    hom-identity =
      pcom (ap-comp fst σ₁₄ σ₄₅)
        (ap (ap fst) identity)
        (pcom.ap (λ _ → fst) (sym σ₁₂) σ₂₃ σ₃₅)

  pentagon
    : ∀ {x y z w v}
      (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w v)
    → assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
    ≡ ap (_⨾ k) (assoc f g h)
      ∙ assoc f (g ⨾ h) k
      ∙ ap (f ⨾_) (assoc g h k)
  pentagon f g h k =
    pcom (ap (_∙ α₄₅) face₁₄
        ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
      hom-identity
      (λ i → pcom (sym (face₁₂ i)) (face₂₃ i) (face₃₅ i))
    ∙ pcom→∙
        (ap (_⨾ k) (assoc f g h))
        (assoc f (g ⨾ h) k)
        (ap (f ⨾_) (assoc g h k))
    where
      open pentagon-fibers f g h k
      open pentagon f g h k
      pcom→∙
        : ∀ {u} {A : Type u} {a b c d : A}
          (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
        → pcom (sym p) q r ≡ p ∙ q ∙ r
      pcom→∙ p q r = pcom.unique
        (sym p) q r
        (p ∙ q ∙ r , cat.lcoh p q r)
```

## Weak triangle

The weak triangle uses only `absorb-l` from `unit`,
not `absorb-coh`. The `α₂₃` edge remains abstract.

```agda
  module triangle-fibers
    {x y z} (f : hom x y) (g : hom y z)
    where
    private
      cc = composable-contr f g

      pt₁ : fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      pt₁ = (f ⨾ idn) ⨾ g
          , emb-composite (f ⨾ idn) g
          ∙ emb-ext λ w a v b →
              emb-composite-pt f idn w a v (noy g v b)
            ∙ ap (emb f w a v) (absorb-l (noy g v b))

      pt₂ : fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      pt₂ = f ⨾ (idn ⨾ g)
          , emb-composite f (idn ⨾ g)
          ∙ emb-ext λ w a v b →
              ap (emb f w a v)
                (noy-composite idn g b)
            ∙ ap (emb f w a v)
                (absorb-l (noy g v b))

      pt₃ : fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      pt₃ = f ⨾ g , emb-composite f g

    σ₁₃ : pt₁ ≡ pt₃
    σ₁₃ = is-contr→is-prop cc pt₁ pt₃

    σ₁₂ : pt₁ ≡ pt₂
    σ₁₂ = is-contr→is-prop cc pt₁ pt₂

    σ₂₃ : pt₂ ≡ pt₃
    σ₂₃ = is-contr→is-prop cc pt₂ pt₃

    α₁₃ : (f ⨾ idn) ⨾ g ≡ f ⨾ g
    α₁₃ = ap fst σ₁₃

    α₁₂ : (f ⨾ idn) ⨾ g ≡ f ⨾ (idn ⨾ g)
    α₁₂ = ap fst σ₁₂

    α₂₃ : f ⨾ (idn ⨾ g) ≡ f ⨾ g
    α₂₃ = ap fst σ₂₃

    identity : σ₁₃ ≡ σ₁₂ ∙ σ₂₃
    identity = is-contr→is-set cc pt₁ pt₃
      σ₁₃ (σ₁₂ ∙ σ₂₃)

    private
      unitr-σ
        : (   f ⨾ idn
            , emb-composite f idn
            ∙ emb-ext λ w a v b →
                ap (emb f w a v) (absorb-l b))
        ≡ (f , refl)
      unitr-σ =
        is-contr→is-prop (emb-image-contr f) _ _

      γ₁₃-pt : ∀ i → fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      γ₁₃-pt i =
        unitr f i ⨾ g
        , emb-composite (unitr f i) g
        ∙ (λ j w a v b →
            unitr-σ i .snd j w a v (noy g v b))

      v₃ : γ₁₃-pt i1 ≡ pt₃
      v₃ i =
        f ⨾ g
        , Path.unitr (emb-composite f g) i

      assoc-σ-fig
        : E₃-contr f idn g .center
        ≡ (   f ⨾ (idn ⨾ g)
            , emb-composite f (idn ⨾ g)
            ∙ emb-ext λ w' a v' b →
                ap (emb f w' a v')
                  (noy-composite idn g b))
      assoc-σ-fig =
        is-contr→is-prop (E₃-contr f idn g) _ _

      γ₁₂-pt : ∀ i → fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      γ₁₂-pt i =
        assoc f idn g i
        , assoc-σ-fig i .snd
        ∙ emb-ext λ w a v b →
            ap (emb f w a v)
              (absorb-l (noy g v b))

      w₁ : pt₁ ≡ γ₁₂-pt i0
      w₁ i =
        (f ⨾ idn) ⨾ g
        , Path.assoc
            (emb-composite (f ⨾ idn) g)
            (emb-ext λ w a v b →
                emb-composite-pt f idn w a v
                  (noy g v b))
            (emb-ext λ w a v b →
                ap (emb f w a v)
                  (absorb-l (noy g v b))) i

      w₂ : γ₁₂-pt i1 ≡ pt₂
      w₂ i =
        f ⨾ (idn ⨾ g)
        , sym (Path.assoc
            (emb-composite f (idn ⨾ g))
            (emb-ext λ w a v b →
                ap (emb f w a v)
                  (noy-composite idn g b))
            (emb-ext λ w a v b →
                ap (emb f w a v)
                  (absorb-l (noy g v b)))) i

    face₁₃ : α₁₃ ≡ ap (_⨾ g) (unitr f)
    face₁₃ =
      contr-face cc σ₁₃
        refl (λ i → γ₁₃-pt i) (ap snd v₃)

    face₁₂ : α₁₂ ≡ assoc f idn g
    face₁₂ =
      contr-face cc σ₁₂
        (ap snd w₁) (λ i → γ₁₂-pt i) (ap snd w₂)

  module triangle
    {x y z} (f : hom x y) (g : hom y z)
    where
    open triangle-fibers f g

    hom-identity
      : α₁₃ ≡ α₁₂ ∙ α₂₃
    hom-identity =
      ap (ap fst) identity
      ∙ ap-comp fst σ₁₂ σ₂₃

  triangle-weak
    : ∀ {x y z}
      (f : hom x y) (g : hom y z)
    → ap (_⨾ g) (unitr f)
    ≡ assoc f idn g ∙ triangle-fibers.α₂₃ f g
  triangle-weak f g =
    pcom face₁₃
      hom-identity
      (ap (_∙ α₂₃) face₁₂)
    where open triangle-fibers f g
          open triangle f g
```

## 2-coherence

The `absorb-coh` field is the additional coherence needed
to identify `α₂₃` with `ap (f ⨾_) (unitl g)` and obtain
the full Mac Lane triangle identity.

```agda
record 2-coherent {o h} (C : category o h) : Type (o ⊔ h) where
  open Virtual C
  field
    absorb-coh
      : ∀ {x y} (f : hom x y) v (b : hom y v)
      → absorb-l (noy f v b)
      ≡ interchange idn f _ idn v b
        ∙ ap (λ t → emb f _ t v b) (absorb-r idn)
```

## Full Mac Lane triangle

The `2-Cat` module opens both `Virtual C` and `2-coherent coh`,
then derives the full triangle
`ap (_⨾ g) (unitr f) ≡ assoc f idn g ∙ ap (f ⨾_) (unitl g)`
using `absorb-coh` to identify the abstract `α₂₃` edge.

```agda
module 2-Cat
  {o h} (C : category o h) (coh : 2-coherent C)
  where
  open Virtual C public
  open 2-coherent coh public

  absorb-l-noy-retract
    : ∀ {x y} (f : hom x y) v (b : hom y v)
    → emb-noy f _ idn v b ∙ absorb-l (noy f v b)
    ≡ refl
  absorb-l-noy-retract f v b =
    ap (emb-noy f _ idn v b ∙_)
      (absorb-coh f v b)
    ∙ Path.grp-cancel
        (ap (λ t → emb f _ t v b) (absorb-r idn))
        (interchange idn f _ idn v b)
```

### Full triangle face₂₃

The `face₂₃` identification requires `absorb-l-noy-retract`,
which in turn requires `absorb-coh`. This is what separates
the full Mac Lane triangle from the weak version.

```agda
  private
    module face₂₃-proof
      {x y z} (f : hom x y) (g : hom y z)
      where
      open triangle-fibers C f g

      private
        cc = composable-contr f g

        pt₂ : fiber emb
          (λ w a v b → emb f w a v (noy g v b))
        pt₂ = f ⨾ (idn ⨾ g)
            , emb-composite f (idn ⨾ g)
            ∙ emb-ext λ w a v b →
                ap (emb f w a v)
                  (noy-composite idn g b)
              ∙ ap (emb f w a v)
                  (absorb-l (noy g v b))

        pt₃ : fiber emb
          (λ w a v b → emb f w a v (noy g v b))
        pt₃ = f ⨾ g , emb-composite f g

        unitl-σ
          : (   idn ⨾ g
              , emb-composite idn g)
          ≡ (   g
              , emb-ext λ w a v b →
                  emb-noy g w a v b)
        unitl-σ =
          is-contr→is-prop (composable-contr idn g)
            _ _

        γ₂₃-pt : ∀ i → fiber emb
          (λ w a v b → emb f w a v (noy g v b))
        γ₂₃-pt i =
          f ⨾ (unitl g i)
          , emb-composite f (unitl g i)
          ∙ emb-ext λ w a v b →
              ap (emb f w a v)
                ((λ j → unitl-σ i .snd j _ idn v b)
                ∙ absorb-l (noy g v b))

        w₀ : pt₂ ≡ γ₂₃-pt i0
        w₀ i =
          f ⨾ (idn ⨾ g)
          , emb-composite f (idn ⨾ g)
          ∙ emb-ext λ w a v b →
              sym (ap-comp (emb f w a v)
                (noy-composite idn g b)
                (absorb-l (noy g v b))) i

        v₁ : γ₂₃-pt i1
          ≡ (f ⨾ g , emb-composite f g ∙ refl)
        v₁ i =
          f ⨾ g
          , emb-composite f g
          ∙ emb-ext λ w a v b →
              ap (ap (emb f w a v))
                (absorb-l-noy-retract g v b) i

        v₂
          : (f ⨾ g , emb-composite f g ∙ refl)
          ≡ pt₃
        v₂ i =
          f ⨾ g
          , Path.unitr (emb-composite f g) i

      face₂₃ : α₂₃ ≡ ap (f ⨾_) (unitl g)
      face₂₃ =
        contr-face cc σ₂₃
          (ap snd w₀) (λ i → γ₂₃-pt i)
          (ap snd v₁ ∙ ap snd v₂)

  triangle
    : ∀ {x y z}
      (f : hom x y) (g : hom y z)
    → ap (_⨾ g) (unitr f)
    ≡ assoc f idn g ∙ ap (f ⨾_) (unitl g)
  triangle f g =
    pcom face₁₃
      hom-identity
      (ap (_∙ α₂₃) face₁₂
      ∙ ap (assoc f idn g ∙_) face₂₃)
    where open triangle-fibers C f g
          open triangle C f g
          open face₂₃-proof f g
```
