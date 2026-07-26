Lane Biocini
March 2026

Categories via act-based composition with yon/noy-embedding axioms.
The primitive `act` is the ambient composition, each morphism
carries a unique `(yon, noy)` pair over `act`, and `yon-emb` /
`noy-emb` assert that yon-fibers and noy-fibers are contractible.
Associativity and the pentagon follow from contractibility of
higher yon-fibers.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.ActCat where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
open import Core.Function.Base
open import Core.Path.Base
open import Core.Groupoid
open import Core.Equiv.Base using (is-equiv; eqv-fibers)
```

## The category record

The record has four axiom fields: `absorb-contr` (a contractible
type packaging the identity with left absorption), `repr-contr`
(each morphism has a unique `(yon, noy)` pair satisfying
interchange), `yon-emb` (yon-fibers are contractible), and
`noy-emb` (noy-fibers are contractible). Right absorption is
derived from the other axioms in the `Cat` module.

```agda
record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    act : ∀ {x} → ∀ w → hom w x → ∀ z → hom x z → hom w z
    absorb-contr : ∀ {x} → is-contr
      (Σ e ∶ hom x x
      , ∀ {z} (h : hom x z) → act x e z h ≡ h)

  idn : ∀ {x} → hom x x
  idn = absorb-contr .center .fst

  absorb : ∀ {x z} (h : hom x z) → act x idn z h ≡ h
  absorb = absorb-contr .center .snd

  field
    repr-contr : ∀ {x y} (f : hom x y) → is-contr
      (Σ (Y , N) ∶ (∀ v → hom y v → hom x v)
                  × (∀ w → hom w x → hom w y)
      , (Y y idn ≡ f)
      × (N x idn ≡ f)
      × (∀ w (a : hom w x) v (b : hom y v)
        → act w a v (Y v b) ≡ act w (N w a) v b))

  yon : ∀ {x y} → hom x y → ∀ v → hom y v → hom x v
  yon f = repr-contr f .center .fst .fst

  noy : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  noy f = repr-contr f .center .fst .snd

  yon-base : ∀ {x y} (f : hom x y) → yon f y idn ≡ f
  yon-base f = repr-contr f .center .snd .fst

  noy-base : ∀ {x y} (f : hom x y) → noy f x idn ≡ f
  noy-base f = repr-contr f .center .snd .snd .fst

  interchange : ∀ {x y} (f : hom x y)
    → ∀ w (a : hom w x) v (b : hom y v)
    → act w a v (yon f v b) ≡ act w (noy f w a) v b
  interchange f =
    repr-contr f .center .snd .snd .snd

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = act _ f _ g
  infixr 40 _⨾_

  field
    yon-emb : ∀ {x y} (f : hom x y) → is-contr
      (Σ g ∶ hom x y , yon g ≡ yon f)
    noy-emb : ∀ {x y} (f : hom x y) → is-contr
      (Σ g ∶ hom x y , noy g ≡ noy f)

  {-# INLINE act #-}
  {-# INLINE _⨾_ #-}
```

## Derived properties

```agda
module Cat {o} {h} (C : category o h) where
  open category C public
```

### Right absorption

Evaluate interchange of `g` at `(w, idn, x, idn)` and simplify:
the left side reduces to `g` via `absorb` and `yon-base`, the
right side reduces to `g ⨾ idn` via `noy-base`.

```agda
  absorb-r : ∀ {x w} (g : hom w x) → act w g x idn ≡ g
  absorb-r g =
    sym (ap (λ t → act _ t _ idn) (noy-base g))
    ∙ sym (interchange g _ idn _ idn)
    ∙ absorb (yon g _ idn)
    ∙ yon-base g
```

### Composition equals act equals yon equals noy

Evaluate interchange of `f` at `(w=x, a=idn, v=z, b=g)` and
simplify both sides using `absorb` and `noy-base`.

```agda
  comp-yon
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → yon f z g ≡ f ⨾ g
  comp-yon f g =
    sym (absorb (yon f _ g))
    ∙ interchange f _ idn _ g
    ∙ ap (λ t → act _ t _ g) (noy-base f)

  comp-noy
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → noy g x f ≡ f ⨾ g
  comp-noy f g =
    sym (absorb-r (noy g _ f))
    ∙ sym (interchange g _ f _ idn)
    ∙ ap (λ t → act _ f _ t) (yon-base g)
```

### Composite representations

The composite `f ⨾ g` has representation
`(yon f ∘ yon g, noy g ∘ noy f)`. Construct this point in the
contractible fiber of `repr-contr (f ⨾ g)`, then project.

```agda
  private
    repr-fiber
      : ∀ {x y} (f : hom x y) → Type _
    repr-fiber {x} {y} f =
      Σ (Y , N) ∶ (∀ v → hom y v → hom x v)
                 × (∀ w → hom w x → hom w y)
      , (Y y idn ≡ f)
      × (N x idn ≡ f)
      × (∀ w (a : hom w x) v (b : hom y v)
        → act w a v (Y v b) ≡ act w (N w a) v b)

    composite-pt
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → repr-fiber (f ⨾ g)
    composite-pt f g =
      (  (λ v b → yon f v (yon g v b))
       , (λ w a → noy g w (noy f w a)))
      , ap (yon f _) (yon-base g) ∙ comp-yon f g
      , ap (noy g _) (noy-base f) ∙ comp-noy f g
      , λ w a v b →
          interchange f w a v (yon g v b)
          ∙ interchange g w (noy f w a) v b

    composite-path
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → repr-contr (f ⨾ g) .center ≡ composite-pt f g
    composite-path f g =
      is-contr→is-prop (repr-contr (f ⨾ g))
        (repr-contr (f ⨾ g) .center)
        (composite-pt f g)

  yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → yon (f ⨾ g) ≡ λ v b → yon f v (yon g v b)
  yon-composite f g i =
    composite-path f g i .fst .fst

  noy-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → noy (f ⨾ g) ≡ λ w a → noy g w (noy f w a)
  noy-composite f g i =
    composite-path f g i .fst .snd
```

### Identity representation

The identity has representation `(id, id)` — both `yon` and `noy`
are the identity.

```agda
  private
    idn-pt : ∀ {x} → repr-fiber (idn {x})
    idn-pt =
      ((λ v b → b) , (λ w a → a))
      , refl
      , refl
      , λ w a v b → refl

    idn-path : ∀ {x}
      → repr-contr (idn {x}) .center ≡ idn-pt
    idn-path =
      is-contr→is-prop (repr-contr idn)
        (repr-contr idn .center)
        idn-pt

  yon-idn : ∀ {x} → yon (idn {x}) ≡ λ v b → b
  yon-idn i = idn-path i .fst .fst

  noy-idn : ∀ {x} → noy (idn {x}) ≡ λ w a → a
  noy-idn i = idn-path i .fst .snd
```

### Injectivity

If two morphisms have the same `yon`, they are equal.

```agda
  yon-inj
    : ∀ {x y} {m₁ m₂ : hom x y}
    → yon m₁ ≡ yon m₂ → m₁ ≡ m₂
  yon-inj {m₁ = m₁} {m₂} p =
    sym (yon-base m₁)
    ∙ (λ i → p i _ idn)
    ∙ yon-base m₂

  noy-inj
    : ∀ {x y} {m₁ m₂ : hom x y}
    → noy m₁ ≡ noy m₂ → m₁ ≡ m₂
  noy-inj {m₁ = m₁} {m₂} p =
    sym (noy-base m₁)
    ∙ (λ i → p i _ idn)
    ∙ noy-base m₂
```

### Right absorption contractibility

Right absorption is a retract of `noy-emb idn`. The cancellation
`sym p ∙ (p ∙ q ∙ sym t) ∙ t ≡ q` in the retraction proof is
done by a direct hcom square.

```agda
  private
    -- sym p ∙ (p ∙ q ∙ sym t) ∙ t ≡ q
    -- via two steps of cancellation
    cancel-sandwich
      : ∀ {u} {A : Type u} {a b c d : A}
      → (p : a ≡ b) (q : b ≡ c) (t : d ≡ c)
      → sym p ∙ (p ∙ q ∙ sym t) ∙ t ≡ q
    cancel-sandwich {b = b} {c} {d} p q t =
      ap (sym p ∙_) step₁ ∙ step₂
      where
        inner : (q ∙ sym t) ∙ t ≡ q
        inner =
          sym (Path.assoc q (sym t) t)
          ∙ ap (q ∙_) (Path.invl t)
          ∙ Path.unitr q

        step₁ : (p ∙ q ∙ sym t) ∙ t ≡ p ∙ q
        step₁ =
          sym (Path.assoc p (q ∙ sym t) t)
          ∙ ap (p ∙_) inner

        step₂ : sym p ∙ p ∙ q ≡ q
        step₂ =
          Path.assoc (sym p) p q
          ∙ ap (_∙ q) (Path.invl p)
          ∙ Path.unitl q

  right-absorb-contr
    : ∀ {x} → is-contr
      (Σ e ∶ hom x x
      , ∀ {w} (a : hom w x) → act w a x e ≡ a)
  right-absorb-contr {x} = cc where
    B = Σ g ∶ hom x x , noy g ≡ noy idn

    s : (Σ e ∶ hom x x
        , ∀ {w} (a : hom w x) → a ⨾ e ≡ a)
      → B
    s (e , abs) =
      e , λ i w a →
        (comp-noy a e
        ∙ abs a
        ∙ sym (λ j → noy-idn j w a)) i

    r : B → Σ e ∶ hom x x
          , ∀ {w} (a : hom w x) → a ⨾ e ≡ a
    r (e , q) =
      e , λ {w} a →
        sym (comp-noy a e)
        ∙ (λ i → q i w a)
        ∙ (λ i → noy-idn i w a)

    retract
      : (x₁ : Σ e ∶ hom x x
              , ∀ {w} (a : hom w x) → a ⨾ e ≡ a)
      → r (s x₁) ≡ x₁
    retract (e , abs) = λ i → e , λ {w} a →
      cancel-sandwich
        (comp-noy a e) (abs a)
        (λ j → noy-idn j w a) i

    cc : is-contr _
    cc .center = r (noy-emb idn .center)
    cc .paths x₁ =
      ap r (noy-emb idn .paths (s x₁))
      ∙ retract x₁
```

### Unit laws

```agda
  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  unitr f = yon-inj path where
    path : yon (f ⨾ idn) ≡ yon f
    path =
      yon-composite f idn
      ∙ (λ i v b → yon f v (yon-idn i v b))

  unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  unitl f = yon-inj path where
    path : yon (idn ⨾ f) ≡ yon f
    path =
      yon-composite idn f
      ∙ (λ i v b → yon-idn i v (yon f v b))
```

### Yon-fibers and associativity

The yon-fiber of a morphism over a given precomposition family.

```agda
  yon-fiber
    : ∀ {x y} → (∀ v → hom y v → hom x v) → Type _
  yon-fiber {x} {y} Y = Σ m ∶ hom x y , yon m ≡ Y

  private
    Y₃ : ∀ {x y z w} (f : hom x y) (g : hom y z)
        (h : hom z w)
      → ∀ v → hom w v → hom x v
    Y₃ f g h =
      λ v b → yon f v (yon g v (yon h v b))

  E₃-contr
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → is-contr (yon-fiber (Y₃ f g h))
  E₃-contr f g h =
    subst (is-contr ∘ yon-fiber) path
      (yon-emb ((f ⨾ g) ⨾ h))
    where
      path
        : yon ((f ⨾ g) ⨾ h)
        ≡ Y₃ f g h
      path =
        yon-composite (f ⨾ g) h
        ∙ (λ i v b →
            yon-composite f g i v (yon h v b))

  private
    assoc-lhs
      : ∀ {x y z w} (f : hom x y) (g : hom y z)
        (h : hom z w)
      → yon-fiber (Y₃ f g h)
    assoc-lhs f g h =
      (f ⨾ g) ⨾ h
      , yon-composite (f ⨾ g) h
      ∙ (λ i v b →
          yon-composite f g i v (yon h v b))

    assoc-rhs
      : ∀ {x y z w} (f : hom x y) (g : hom y z)
        (h : hom z w)
      → yon-fiber (Y₃ f g h)
    assoc-rhs f g h =
      f ⨾ (g ⨾ h)
      , yon-composite f (g ⨾ h)
      ∙ (λ i v b →
          yon f v (yon-composite g h i v b))

    assoc-σ
      : ∀ {x y z w} (f : hom x y) (g : hom y z)
        (h : hom z w)
      → assoc-lhs f g h ≡ assoc-rhs f g h
    assoc-σ f g h =
      is-contr→is-prop (E₃-contr f g h)
        (assoc-lhs f g h) (assoc-rhs f g h)

  assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (assoc-σ f g h)
```

### Pentagon

```agda
  private
    Y₄ : ∀ {x y z w u} (f : hom x y)
        (g : hom y z) (h : hom z w) (k : hom w u)
      → ∀ v → hom u v → hom x v
    Y₄ f g h k =
      λ v b →
        yon f v (yon g v (yon h v (yon k v b)))

  E₄-contr
    : ∀ {x y z w u} (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w u)
    → is-contr (yon-fiber (Y₄ f g h k))
  E₄-contr f g h k =
    subst (is-contr ∘ yon-fiber) path
      (yon-emb (((f ⨾ g) ⨾ h) ⨾ k))
    where
      path
        : yon (((f ⨾ g) ⨾ h) ⨾ k)
        ≡ Y₄ f g h k
      path =
        yon-composite ((f ⨾ g) ⨾ h) k
        ∙ (λ i v b →
            yon-composite (f ⨾ g) h i v
              (yon k v b))
        ∙ (λ i v b →
            yon-composite f g i v
              (yon h v (yon k v b)))

  module pentagon-fibers
    {x y z w u}
    (f : hom x y) (g : hom y z)
    (h : hom z w) (k : hom w u)
    where
    private
      E₄c = E₄-contr f g h k

      pt₁ : yon-fiber (Y₄ f g h k)
      pt₁ = ((f ⨾ g) ⨾ h) ⨾ k
          , yon-composite ((f ⨾ g) ⨾ h) k
          ∙ (λ i v b →
              yon-composite (f ⨾ g) h i v
                (yon k v b))
          ∙ (λ i v b →
              yon-composite f g i v
                (yon h v (yon k v b)))

      pt₂ : yon-fiber (Y₄ f g h k)
      pt₂ = (f ⨾ (g ⨾ h)) ⨾ k
          , yon-composite (f ⨾ (g ⨾ h)) k
          ∙ (λ i v b →
              yon-composite f (g ⨾ h) i v
                (yon k v b))
          ∙ (λ i v b →
              yon f v
                (yon-composite g h i v
                  (yon k v b)))

      pt₃ : yon-fiber (Y₄ f g h k)
      pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
          , yon-composite f ((g ⨾ h) ⨾ k)
          ∙ (λ i v b →
              yon f v
                (yon-composite (g ⨾ h) k i v b))
          ∙ (λ i v b →
              yon f v
                (yon-composite g h i v
                  (yon k v b)))

      pt₄ : yon-fiber (Y₄ f g h k)
      pt₄ = (f ⨾ g) ⨾ (h ⨾ k)
          , yon-composite (f ⨾ g) (h ⨾ k)
          ∙ (λ i v b →
              yon-composite f g i v
                (yon (h ⨾ k) v b))
          ∙ (λ i v b →
              yon f v (yon g v
                (yon-composite h k i v b)))

      pt₅ : yon-fiber (Y₄ f g h k)
      pt₅ = f ⨾ (g ⨾ (h ⨾ k))
          , yon-composite f (g ⨾ (h ⨾ k))
          ∙ (λ i v b →
              yon f v
                (yon-composite g (h ⨾ k) i v b))
          ∙ (λ i v b →
              yon f v (yon g v
                (yon-composite h k i v b)))

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

    identity : σ₁₄ ∙ σ₄₅ ≡ σ₁₂ ∙ σ₂₃ ∙ σ₃₅
    identity = is-contr→is-set E₄c pt₁ pt₅
      (σ₁₄ ∙ σ₄₅) (σ₁₂ ∙ σ₂₃ ∙ σ₃₅)

    private
      γ₁₂ : pt₁ ≡ pt₂
      γ₁₂ i =
        assoc f g h i ⨾ k
        , yon-composite (assoc-σ f g h i .fst) k
        ∙ (λ j v b →
            assoc-σ f g h i .snd j v
              (yon k v b))

      -- γ₃₅ sweeps f ⨾ assoc g h k along the interval.
      -- The bookend paths v₃ and v₅ reconcile the witness
      -- chains using ap-comp to distribute ap (yon f v)
      -- over a path concatenation.

      γ₃₅-pt : ∀ i → yon-fiber (Y₄ f g h k)
      γ₃₅-pt i =
        f ⨾ assoc g h k i
        , yon-composite f (assoc g h k i)
        ∙ (λ j v b →
            yon f v
              (assoc-σ g h k i .snd j v b))

      v₃ : pt₃ ≡ γ₃₅-pt i0
      v₃ i =
        f ⨾ ((g ⨾ h) ⨾ k)
        , yon-composite f ((g ⨾ h) ⨾ k)
        ∙ funext λ v → funext λ b →
            sym (ap-comp (yon f v)
              (λ j →
                yon-composite (g ⨾ h) k j v b)
              (λ j →
                yon-composite g h j v
                  (yon k v b))) i

      v₅ : γ₃₅-pt i1 ≡ pt₅
      v₅ i =
        f ⨾ (g ⨾ (h ⨾ k))
        , yon-composite f (g ⨾ (h ⨾ k))
        ∙ funext λ v → funext λ b →
            ap-comp (yon f v)
              (λ j →
                yon-composite g (h ⨾ k) j v b)
              (λ j →
                yon g v
                  (yon-composite h k j v b)) i

      γ₃₅-full : pt₃ ≡ pt₅
      γ₃₅-full = v₃ ∙ (λ i → γ₃₅-pt i) ∙ v₅

      γ₂₃-pt : ∀ i → yon-fiber (Y₄ f g h k)
      γ₂₃-pt i =
        assoc f (g ⨾ h) k i
        , assoc-σ f (g ⨾ h) k i .snd
        ∙ funext λ v → funext λ b →
            ap (yon f v)
              (λ j →
                yon-composite g h j v
                  (yon k v b))

      w₂ : pt₂ ≡ γ₂₃-pt i0
      w₂ i =
        (f ⨾ (g ⨾ h)) ⨾ k
        , Path.assoc
            (yon-composite (f ⨾ (g ⨾ h)) k)
            (funext λ v → funext λ b →
              (λ j →
                yon-composite f (g ⨾ h) j v
                  (yon k v b)))
            (funext λ v → funext λ b →
              ap (yon f v)
                (λ j →
                  yon-composite g h j v
                    (yon k v b))) i

      w₃ : γ₂₃-pt i1 ≡ pt₃
      w₃ i =
        f ⨾ ((g ⨾ h) ⨾ k)
        , sym (Path.assoc
            (yon-composite f ((g ⨾ h) ⨾ k))
            (funext λ v → funext λ b →
              ap (yon f v)
                (λ j →
                  yon-composite (g ⨾ h) k j v b))
            (funext λ v → funext λ b →
              ap (yon f v)
                (λ j →
                  yon-composite g h j v
                    (yon k v b)))) i

      γ₂₃-full : pt₂ ≡ pt₃
      γ₂₃-full = w₂ ∙ (λ i → γ₂₃-pt i) ∙ w₃

      γ₄₅-pt : ∀ i → yon-fiber (Y₄ f g h k)
      γ₄₅-pt i =
        assoc f g (h ⨾ k) i
        , assoc-σ f g (h ⨾ k) i .snd
        ∙ funext λ v → funext λ b →
            ap (λ t → yon f v (yon g v t))
              (λ j → yon-composite h k j v b)

      w₄ : pt₄ ≡ γ₄₅-pt i0
      w₄ i =
        (f ⨾ g) ⨾ (h ⨾ k)
        , Path.assoc
            (yon-composite (f ⨾ g) (h ⨾ k))
            (funext λ v → funext λ b →
              (λ j →
                yon-composite f g j v
                  (yon (h ⨾ k) v b)))
            (funext λ v → funext λ b →
              ap (λ t → yon f v (yon g v t))
                (λ j →
                  yon-composite h k j v b)) i

      w₅ : γ₄₅-pt i1 ≡ pt₅
      w₅ i =
        f ⨾ (g ⨾ (h ⨾ k))
        , sym (Path.assoc
            (yon-composite f (g ⨾ (h ⨾ k)))
            (funext λ v → funext λ b →
              ap (yon f v)
                (λ j →
                  yon-composite g (h ⨾ k) j v b))
            (funext λ v → funext λ b →
              ap (λ t → yon f v (yon g v t))
                (λ j →
                  yon-composite h k j v b))) i

      γ₄₅-full : pt₄ ≡ pt₅
      γ₄₅-full = w₄ ∙ (λ i → γ₄₅-pt i) ∙ w₅

      γ₁₄-pt : ∀ i → yon-fiber (Y₄ f g h k)
      γ₁₄-pt i =
        assoc (f ⨾ g) h k i
        , assoc-σ (f ⨾ g) h k i .snd
        ∙ funext λ v → funext λ b →
            (λ j →
              yon-composite f g j v
                (yon h v (yon k v b)))

      w₁ : pt₁ ≡ γ₁₄-pt i0
      w₁ i =
        ((f ⨾ g) ⨾ h) ⨾ k
        , Path.assoc
            (yon-composite ((f ⨾ g) ⨾ h) k)
            (funext λ v → funext λ b →
              (λ j →
                yon-composite (f ⨾ g) h j v
                  (yon k v b)))
            (funext λ v → funext λ b →
              (λ j →
                yon-composite f g j v
                  (yon h v (yon k v b)))) i

      w₁₄-nat : ∀ v (b : hom u v)
        → ap (yon (f ⨾ g) v)
              (λ j → yon-composite h k j v b)
          ∙ (λ j →
              yon-composite f g j v
                (yon h v (yon k v b)))
        ≡ (λ j →
              yon-composite f g j v
                (yon (h ⨾ k) v b))
          ∙ ap (λ t → yon f v (yon g v t))
                (λ j → yon-composite h k j v b)
      w₁₄-nat v b = sym (Path.commutes
        (λ j →
            yon-composite f g j v
              (yon (h ⨾ k) v b))
        (ap (λ t → yon f v (yon g v t))
          (λ j → yon-composite h k j v b))
        (ap (yon (f ⨾ g) v)
          (λ j → yon-composite h k j v b))
        (λ j →
            yon-composite f g j v
              (yon h v (yon k v b)))
        (λ i j →
            yon-composite f g j v
              (yon-composite h k i v b)))

      w₁₄ : γ₁₄-pt i1 ≡ pt₄
      w₁₄ i =
        (f ⨾ g) ⨾ (h ⨾ k)
        , (sym (Path.assoc A₁₄ B₁₄ C₁₄)
          ∙ ap (A₁₄ ∙_) N₁₄) i
        where
          A₁₄ = yon-composite (f ⨾ g) (h ⨾ k)
          B₁₄ = funext λ v → funext λ b →
            ap (yon (f ⨾ g) v)
              (λ j → yon-composite h k j v b)
          C₁₄ = funext λ v → funext λ b →
            (λ j →
              yon-composite f g j v
                (yon h v (yon k v b)))
          N₁₄ : B₁₄ ∙ C₁₄
              ≡ (funext λ v → funext λ b →
                  (λ j →
                    yon-composite f g j v
                      (yon (h ⨾ k) v b))
                ∙ ap (λ t → yon f v (yon g v t))
                      (λ j →
                        yon-composite h k j v b))
          N₁₄ j = funext λ v → funext λ b →
            w₁₄-nat v b j

      γ₁₄-full : pt₁ ≡ pt₄
      γ₁₄-full = w₁ ∙ (λ i → γ₁₄-pt i) ∙ w₁₄

    face₁₂ : α₁₂ ≡ ap (_⨾ k) (assoc f g h)
    face₁₂ = total-contr-unique E₄c
      α₁₂ (ap (_⨾ k) (assoc f g h))
      (ap snd σ₁₂)
      (ap snd γ₁₂)

    face₃₅ : α₃₅ ≡ ap (f ⨾_) (assoc g h k)
    face₃₅ =
      total-contr-unique E₄c
        α₃₅ (ap fst γ₃₅-full)
        (ap snd σ₃₅)
        (ap snd γ₃₅-full)
      ∙ ap-comp fst v₃ ((λ i → γ₃₅-pt i) ∙ v₅)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₃₅-pt i) v₅
          ∙ Path.unitr
              (ap (f ⨾_) (assoc g h k)))
      ∙ Path.unitl
          (ap (f ⨾_) (assoc g h k))

    face₂₃ : α₂₃ ≡ assoc f (g ⨾ h) k
    face₂₃ =
      total-contr-unique E₄c
        α₂₃ (ap fst γ₂₃-full)
        (ap snd σ₂₃)
        (ap snd γ₂₃-full)
      ∙ ap-comp fst w₂
          ((λ i → γ₂₃-pt i) ∙ w₃)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₂₃-pt i) w₃
          ∙ Path.unitr (assoc f (g ⨾ h) k))
      ∙ Path.unitl (assoc f (g ⨾ h) k)

    face₄₅ : α₄₅ ≡ assoc f g (h ⨾ k)
    face₄₅ =
      total-contr-unique E₄c
        α₄₅ (ap fst γ₄₅-full)
        (ap snd σ₄₅)
        (ap snd γ₄₅-full)
      ∙ ap-comp fst w₄
          ((λ i → γ₄₅-pt i) ∙ w₅)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₄₅-pt i) w₅
          ∙ Path.unitr (assoc f g (h ⨾ k)))
      ∙ Path.unitl (assoc f g (h ⨾ k))

    face₁₄ : α₁₄ ≡ assoc (f ⨾ g) h k
    face₁₄ =
      total-contr-unique E₄c
        α₁₄ (ap fst γ₁₄-full)
        (ap snd σ₁₄)
        (ap snd γ₁₄-full)
      ∙ ap-comp fst w₁
          ((λ i → γ₁₄-pt i) ∙ w₁₄)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₁₄-pt i) w₁₄
          ∙ Path.unitr (assoc (f ⨾ g) h k))
      ∙ Path.unitl (assoc (f ⨾ g) h k)

  module pentagon
    {x y z w u}
    (f : hom x y) (g : hom y z)
    (h : hom z w) (k : hom w u)
    where
    open pentagon-fibers f g h k

    hom-identity
      : α₁₄ ∙ α₄₅ ≡ α₁₂ ∙ α₂₃ ∙ α₃₅
    hom-identity =
      sym (ap-comp fst σ₁₄ σ₄₅)
      ∙ ap (ap fst) identity
      ∙ ap-comp fst σ₁₂ (σ₂₃ ∙ σ₃₅)
      ∙ ap (α₁₂ ∙_) (ap-comp fst σ₂₃ σ₃₅)

  pentagon
    : ∀ {x y z w u}
      (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w u)
    → assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
    ≡ ap (_⨾ k) (assoc f g h)
      ∙ assoc f (g ⨾ h) k ∙ ap (f ⨾_) (assoc g h k)
  pentagon f g h k =
    sym (ap (_∙ α₄₅) face₁₄
        ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
    ∙ hom-identity
    ∙ ap (_∙ (α₂₃ ∙ α₃₅)) face₁₂
    ∙ ap (ap (_⨾ k) (assoc f g h) ∙_)
        (ap (_∙ α₃₅) face₂₃
        ∙ ap (assoc f (g ⨾ h) k ∙_) face₃₅)
    where open pentagon-fibers f g h k
          open pentagon f g h k
```

### Triangle (stub)

```agda
  -- TODO: Triangle coherence
  -- The triangle should follow from unit laws and
  -- associativity, analogous to Cat.Virtual's triangle.
```

## Opposite category

Reverse the direction of morphisms: `hom_op x y = C.hom y x` and
`act_op w a z b = C.act z b w a`. Left absorption in op is right
absorption in C, which we derived above. The repr-contr fiber
swaps `(yon, noy)` to `(noy, yon)` with reversed interchange.

```agda
module _ {o h} (C : category o h) where
  private module C = Cat C

  op : category o h
  op .category.ob = C.ob
  op .category.hom x y = C.hom y x
  op .category.act {x} w a z b = C.act {x} z b w a
  -- Use C.idn as the center so idn_op ≡ C.idn definitionally.
  op .category.absorb-contr {x} = ac where
    ac : is-contr _
    ac .center = C.idn , λ a → C.absorb-r a
    ac .paths y =
      sym (C.right-absorb-contr .paths
            (C.idn , λ a → C.absorb-r a))
      ∙ C.right-absorb-contr .paths y

  op .category.repr-contr {x} {y} f = cc where
    cc : is-contr _
    cc .center =
      ((λ v b → C.noy f v b)
      , (λ w a → C.yon f w a))
      , C.noy-base f
      , C.yon-base f
      , λ w a v b → sym (C.interchange f v b w a)
    cc .paths pt =
      let
        Y' = pt .fst .fst
        N' = pt .fst .snd
        yb' = pt .snd .fst
        nb' = pt .snd .snd .fst
        ic' = pt .snd .snd .snd
        RF = C.repr-contr f
        to-C₀ = RF .center
        to-C =
          ((N' , Y')
          , nb' , yb'
          , λ w a v b → sym (ic' v b w a))
        p = is-contr→is-prop RF to-C₀ to-C
      in λ i →
        ((λ v b → p i .fst .snd v b)
        , (λ w a → p i .fst .fst w a))
        , p i .snd .snd .fst
        , p i .snd .fst
        , λ w a v b →
            sym (p i .snd .snd .snd v b w a)
  op .category.yon-emb f = C.noy-emb f
  op .category.noy-emb f = C.yon-emb f
```

## Opposite involution

After double reversal the structural fields are definitionally
equal. The axiom fields (`absorb-contr`, `repr-contr`, `yon-emb`,
`noy-emb`) are all `is-contr` valued, hence propositions, so
`is-prop→PathP` fills them.

```agda
module _ {o h} (C : category o h) where
  private module C = Cat C

  -- ob, hom, act are definitionally constant after double
  -- reversal. Each axiom field is is-contr valued (a prop).
  -- The type of repr-contr depends on idn (from
  -- absorb-contr), so we define the path for absorb-contr
  -- first, then refer to it for dependent type families.
  private
    ac : ∀ {x} (j : I)
      → is-contr (Σ e ∶ C.hom x x
                  , ∀ {z} (h : C.hom x z)
                  → C.act x e z h ≡ h)
    ac j = is-contr-is-prop _
      (category.absorb-contr (op (op C)))
      C.absorb-contr j

    e : ∀ {x} → I → C.hom x x
    e j = ac j .center .fst

    RC : ∀ {x y} → C.hom x y → I → Type _
    RC {x} {y} f j = is-contr
      (Σ (Y , N) ∶ (∀ v → C.hom y v → C.hom x v)
                 × (∀ w → C.hom w x → C.hom w y)
      , (Y y (e j) ≡ f)
      × (N x (e j) ≡ f)
      × (∀ w (a : C.hom w x) v (b : C.hom y v)
        → C.act w a v (Y v b)
        ≡ C.act w (N w a) v b))

    rc : ∀ {x y} (f : C.hom x y)
      → PathP (λ j → RC f j)
          (category.repr-contr (op (op C)) f)
          (C.repr-contr f)
    rc f = is-prop→PathP (λ j → is-contr-is-prop _)
      (category.repr-contr (op (op C)) f)
      (C.repr-contr f)

    yf : ∀ {x y} (f : C.hom x y) (j : I)
      → ∀ v → C.hom y v → C.hom x v
    yf f j = rc f j .center .fst .fst

    nf : ∀ {x y} (f : C.hom x y) (j : I)
      → ∀ w → C.hom w x → C.hom w y
    nf f j = rc f j .center .fst .snd

    ye : ∀ {x y} (f : C.hom x y)
      → PathP (λ j → is-contr
          (Σ g ∶ C.hom x y , yf g j ≡ yf f j))
          (category.yon-emb (op (op C)) f)
          (C.yon-emb f)
    ye f = is-prop→PathP (λ _ → is-contr-is-prop _)
      (category.yon-emb (op (op C)) f)
      (C.yon-emb f)

    ne : ∀ {x y} (f : C.hom x y)
      → PathP (λ j → is-contr
          (Σ g ∶ C.hom x y , nf g j ≡ nf f j))
          (category.noy-emb (op (op C)) f)
          (C.noy-emb f)
    ne f = is-prop→PathP (λ _ → is-contr-is-prop _)
      (category.noy-emb (op (op C)) f)
      (C.noy-emb f)

  op-invol : op (op C) ≡ C
  op-invol i .category.ob = C.ob
  op-invol i .category.hom x y = C.hom x y
  op-invol i .category.act {x} w a z b =
    C.act {x} w a z b
  op-invol i .category.absorb-contr {x} = ac i
  op-invol i .category.repr-contr {x} {y} f = rc f i
  op-invol i .category.yon-emb {x} {y} f = ye f i
  op-invol i .category.noy-emb {x} {y} f = ne f i
```
