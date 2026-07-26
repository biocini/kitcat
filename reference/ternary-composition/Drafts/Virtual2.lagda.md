Lane Biocini
March 2026

Categories via ternary composition with interchange and absorption
coherence. This is a revised version of `Cat.Virtual` where the
`category` record includes an additional coherence axiom `absorb-coh`
relating left absorption to interchange followed by right absorption.
This coherence enables the full classical Mac Lane triangle identity,
identifying the third edge `α₂₃` with `ap (f ⨾_) (unitl g)`.

The triangle identity states:

    ap (_⨾ g) (unitr f) ≡ assoc f idn g ∙ ap (f ⨾_) (unitl g)

Without `absorb-coh`, we can only show the weaker statement with
`triangle-fibers.α₂₃` in place of `ap (f ⨾_) (unitl g)`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Virtual2 where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
open import Core.Function.Base
open import Core.Path.Base
```

## The category record

The record includes `absorb-r`, `absorb-l`, `noy`, and `yon` as
derived definitions inside the record (before the `absorb-coh` field),
so that `absorb-coh` can reference them.

```agda
record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    emb : ∀ {x y} → hom x y
        → ∀ w → hom w x → ∀ z → hom y z → hom w z
    idn-contr
      : ∀ {x}
      → is-contr
          (Σ e ∶ hom x x
          , (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
          × (∀ {z} (h : hom x z) → emb e x e z h ≡ h))

  idn : ∀ {x} → hom x x
  idn = idn-contr .center .fst

  absorb-r : ∀ {x} {w : ob} (g : hom w x)
    → emb idn w g x idn ≡ g
  absorb-r = idn-contr .center .snd .fst

  absorb-l : ∀ {x} {z : ob} (h : hom x z)
    → emb idn x idn z h ≡ h
  absorb-l = idn-contr .center .snd .snd

  noy : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  noy f z h = emb f _ idn z h

  yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  yon f w g = emb f w g _ idn

  field
    composable-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr
          (fiber (emb {x} {z})
            (λ w a v b → emb f w a v (noy g v b)))
    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        w (a : hom w x) v (b : hom z v)
      → emb f w a v (noy g v b)
      ≡ emb g w (yon f w a) v b

  -- Left absorption decomposes as interchange followed by right
  -- absorption in the left slot. That is, `absorb-l (noy f v b)`
  -- going directly from `emb idn _ idn v (noy f v b)` to
  -- `noy f v b` equals the two-step route through interchange
  -- then `absorb-r idn` in the left slot.
  field
    absorb-coh
      : ∀ {x y} (f : hom x y) v (b : hom y v)
      → absorb-l (noy f v b)
      ≡ interchange idn f _ idn v b
        ∙ ap (λ t → emb f _ t v b) (absorb-r idn)

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = composable-contr f g .center .fst
  infixr 40 _⨾_

  {-# INLINE emb #-}
  {-# INLINE _⨾_ #-}
```

## Derived operations

```agda
module Cat {o} {h} (C : category o h) where
  open category C public
```

### Embedding property

`composable-contr idn f` gives `is-contr (fiber emb target)` where
`target w a v b = emb idn w a v (noy f v b)`. By interchange,
this equals `emb f w (yon idn w a) v b = emb f w a v b` via
right absorption. So `fiber emb (emb f)` is contractible for
every `f`, making `emb` an embedding.

```agda
  emb-image-contr
    : ∀ {x y} (f : hom x y)
    → is-contr (fiber emb (emb f))
  emb-image-contr f =
    subst (is-contr ∘ fiber emb) path
      (composable-contr idn f)
    where
      path
        : (λ w a v b → emb idn w a v (noy f v b))
        ≡ emb f
      path = funext λ w → funext λ a → funext λ v →
        funext λ b →
          interchange idn f w a v b
          ∙ ap (λ t → emb f w t v b) (absorb-r a)

  composable-yon
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr
        (fiber emb
          (λ w a v b → emb g w (yon f w a) v b))
  composable-yon f g =
    subst (is-contr ∘ fiber emb) path
      (composable-contr f g)
    where
      path
        : (λ w a v b → emb f w a v (noy g v b))
        ≡ (λ w a v b → emb g w (yon f w a) v b)
      path = funext λ w → funext λ a → funext λ v →
        funext λ b → interchange f g w a v b

  composable-swap
    : ∀ {x y}
      {target : ∀ w → hom w x → ∀ v → hom y v
        → hom w v}
    → is-contr (fiber emb target)
    → is-contr
        (fiber
          {B = ∀ w → hom y w → ∀ v → hom v x
            → hom v w}
          (λ s w a v b → emb s v b w a)
          (λ w a v b → target v b w a))
  composable-swap c .center .fst =
    c .center .fst
  composable-swap c .center .snd i w a v b =
    c .center .snd i v b w a
  composable-swap {target = target}
    c .paths (s' , q') i .fst =
    c .paths (s' , q'') i .fst
    where
      q'' : emb s' ≡ target
      q'' i w a v b = q' i v b w a
  composable-swap {target = target}
    c .paths (s' , q') i .snd j w a v b =
    c .paths (s' , q'') i .snd j v b w a
    where
      q'' : emb s' ≡ target
      q'' i w a v b = q' i v b w a
```

### Composite equations

```agda
  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite f g =
    composable-contr f g .center .snd

  emb-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb f w a v (noy g v b)
  emb-composite-pt f g w a v b i =
    emb-composite f g i w a v b

  emb-yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb g w (yon f w a) v b)
  emb-yon-composite f g =
    emb-composite f g
    ∙ funext λ w → funext λ a → funext λ v →
      funext λ b → interchange f g w a v b
```

### Induction principles

Each contractible fiber yields an induction principle via
`contr-ind`: to prove something about all inhabitants of the
fiber, it suffices to prove it for the canonical center.

The identity is the unique endomorphism absorbing from both
sides. `idn-ind` eliminates any `(e, r, l)` satisfying the
absorption laws back to the canonical triple
`(idn, absorb-r, absorb-l)`.

```agda
  private
    idn-fiber : ∀ {x} → Type _
    idn-fiber {x} = Σ e ∶ hom x x ,
        (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
      × (∀ {z} (h : hom x z) → emb e x e z h ≡ h)

  idn-ind
    : ∀ {u} {x}
    → (P : (e : hom x x)
         → (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
         → (∀ {z} (h : hom x z)
            → emb e x e z h ≡ h)
         → Type u)
    → P idn absorb-r absorb-l
    → (a : idn-fiber)
    → P (a .fst) (a .snd .fst) (a .snd .snd)
  idn-ind P base a =
    coe01
      (λ i → P (p i .fst)
        (p i .snd .fst) (p i .snd .snd))
      base
    where p = idn-contr .paths a

  idn-unique
    : ∀ {x} (e : hom x x)
    → (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
    → (∀ {z} (h : hom x z) → emb e x e z h ≡ h)
    → idn ≡ e
  idn-unique e r l =
    idn-ind (λ e _ _ → idn ≡ e) refl (e , r , l)
```

Composition is the unique morphism whose embedding equals the
composite target. `emb-ind` eliminates any `(s, q)` in the
composable fiber back to `(f ⨾ g, emb-composite f g)`.

```agda
  emb-ind
    : ∀ {u} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z)
         → emb s
           ≡ (λ w a v b → emb f w a v (noy g v b))
         → Type u)
    → P (f ⨾ g) (emb-composite f g)
    → ∀ s q → P s q
  emb-ind f g P base s q =
    contr-ind (composable-contr f g)
      (λ where (s , q) → P s q)
      base (s , q)

  ⨾-η
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → (s : hom x z)
    → emb s
      ≡ (λ w a v b → emb f w a v (noy g v b))
    → f ⨾ g ≡ s
  ⨾-η f g = emb-ind f g (λ s _ → f ⨾ g ≡ s) refl
```

The embedding is faithful: `emb n ≡ emb m` implies `n ≡ m`.
`emb-image-ind` eliminates any `(n, q)` in the image fiber back
to `(m, refl)`.

```agda
  emb-image-ind
    : ∀ {u} {x y} (m : hom x y)
    → (P : (n : hom x y) → emb n ≡ emb m → Type u)
    → P m refl
    → ∀ n q → P n q
  emb-image-ind m P base n q =
    coe01 (λ i → P (path i .fst) (path i .snd)) base
    where
      path : (m , refl) ≡ (n , q)
      path =
        sym (emb-image-contr m .paths (m , refl))
        ∙ emb-image-contr m .paths (n , q)

  emb-inj
    : ∀ {x y} {f g : hom x y}
    → emb f ≡ emb g → f ≡ g
  emb-inj {f = f} {g} p =
    emb-image-ind f (λ n _ → f ≡ n) refl g (sym p)
```

The yon-characterized composite: interchange swaps `noy` for
`yon` in the composite target, giving a dual fiber with the
same center. `emb-yon-ind` eliminates over this alternative
characterization.

```agda
  emb-yon-ind
    : ∀ {u} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z)
         → emb s
           ≡ (λ w a v b → emb g w (yon f w a) v b)
         → Type u)
    → P (f ⨾ g) (emb-yon-composite f g)
    → ∀ s q → P s q
  emb-yon-ind f g P base s q =
    coe01 (λ i → P (path i .fst) (path i .snd)) base
    where
      path
        : (f ⨾ g , emb-yon-composite f g) ≡ (s , q)
      path =
        sym (composable-yon f g .paths _)
        ∙ composable-yon f g .paths (s , q)
```

### Distribution and decomposition

`noy` and `yon` distribute over composition. `noy-composite`
follows from the composite equation at `a = idn`;
`yon-composite` uses the composite equation and interchange.
Both `yon` and `noy` are injective, following from interchange
and `emb-inj`. The `emb-yon` and `emb-noy` lemmas express
`emb f` in terms of `yon` and `noy`.

```agda
  noy-composite
    : ∀ {x y z} (g : hom x y) (h : hom y z)
      {v : ob} (b : hom z v)
    → noy (g ⨾ h) v b ≡ noy g v (noy h v b)
  noy-composite g h {v} b i =
    emb-composite g h i _ idn v b

  yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x)
    → yon (f ⨾ g) w a ≡ yon g w (yon f w a)
  yon-composite f g w a =
    emb-composite-pt f g w a _ idn
    ∙ interchange f g w a _ idn

  yon-inj
    : ∀ {x y} {f g : hom x y}
    → yon f ≡ yon g → f ≡ g
  yon-inj {f = f} {g} p = emb-inj
    (funext λ w → funext λ a → funext λ v →
      funext λ b →
        ap (emb f w a v) (sym (absorb-l b))
        ∙ interchange f idn w a v b
        ∙ ap (λ t → emb idn w t v b) (λ i → p i w a)
        ∙ sym (interchange g idn w a v b)
        ∙ ap (emb g w a v) (absorb-l b))

  noy-inj
    : ∀ {x y} {f g : hom x y}
    → noy f ≡ noy g → f ≡ g
  noy-inj {f = f} {g} p = emb-inj
    (funext λ w → funext λ a → funext λ v →
      funext λ b →
        ap (λ t → emb f w t v b) (sym (absorb-r a))
        ∙ sym (interchange idn f w a v b)
        ∙ ap (λ t → emb idn w a v t) (λ i → p i v b)
        ∙ interchange idn g w a v b
        ∙ ap (λ t → emb g w t v b) (absorb-r a))

  emb-yon
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w (yon f w a) v b
  emb-yon f w a v b =
    ap (emb f w a v) (sym (absorb-l b))
    ∙ interchange f idn w a v b

  emb-noy
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w a v (noy f v b)
  emb-noy f w a v b =
    ap (λ t → emb f w t v b) (sym (absorb-r a))
    ∙ sym (interchange idn f w a v b)
```

### Coherent unit laws and associativity

The unit laws and associativity are defined as projections from
contractible fibers. Each law is `ap fst` of the unique path
between two points in a contractible fiber of `emb`. This gives
control over the emb-image at every intermediate point along
the path, which is needed for triangle coherence.

```agda
  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  unitr f =
    ap fst
      (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = f ⨾ idn
          , emb-composite f idn
          ∙ funext λ w → funext λ a → funext λ v →
            funext λ b →
              ap (emb f w a v) (absorb-l b)

      rhs : fiber emb (emb f)
      rhs = f , refl

  unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  unitl f =
    ap fst
      (is-contr→is-prop (composable-contr idn f)
        lhs rhs)
    where
      lhs : fiber emb
        (λ w a v b → emb idn w a v (noy f v b))
      lhs = idn ⨾ f , emb-composite idn f

      rhs : fiber emb
        (λ w a v b → emb idn w a v (noy f v b))
      rhs = f , funext λ w → funext λ a →
        funext λ v → funext λ b →
          emb-noy f w a v b

  private
    E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z)
        (h : hom z w)
      → ∀ w' → hom w' x → ∀ v → hom w v → hom w' v
    E₃ f g h =
      λ w a v b →
        emb f w a v (noy g v (noy h v b))

  E₃-contr
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → is-contr (fiber emb (E₃ f g h))
  E₃-contr f g h =
    subst (is-contr ∘ fiber emb) path
      (composable-contr (f ⨾ g) h)
    where
      path
        : (λ w a v b →
            emb (f ⨾ g) w a v (noy h v b))
        ≡ E₃ f g h
      path = funext λ w → funext λ a →
        funext λ v → funext λ b →
          emb-composite-pt f g w a v (noy h v b)

  assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h =
    ap fst
      (is-contr→is-prop (E₃-contr f g h) lhs rhs)
    where
      lhs : fiber emb (E₃ f g h)
      lhs = (f ⨾ g) ⨾ h
          , emb-composite (f ⨾ g) h
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt f g w a v (noy h v b)

      rhs : fiber emb (E₃ f g h)
      rhs = f ⨾ (g ⨾ h)
          , emb-composite f (g ⨾ h)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v)
                (noy-composite g h b)
```

### Absorption coherence lemma

The `absorb-coh` axiom says `absorb-l (noy f v b)` equals
`interchange ∙ ap ... (absorb-r idn)`. Expanding `emb-noy`,
we see `sym (emb-noy f _ idn v b) = interchange ∙ ap ...
(absorb-r idn)`. So `absorb-coh` identifies `absorb-l` with
`sym emb-noy`, giving us a retraction.

The goal `emb-noy ∙ absorb-l ≡ refl` reduces, after
substituting `absorb-coh`, to `(ap F (sym p) ∙ sym q) ∙ (q ∙
ap F p) ≡ refl` where `p = absorb-r idn`, `q = interchange`,
and `F t = emb f _ t v b`.

```agda
  private
    -- (ap F (sym p) ∙ sym q) ∙ (q ∙ ap F p) ≡ refl
    -- by reassociating and cancelling q⁻¹∙q and (ap F p⁻¹)∙(ap F p)
    grp-cancel
      : ∀ {u} {A : Type u} {a b c : A}
        (p : b ≡ a) (q : c ≡ b)
      → (sym p ∙ sym q) ∙ (q ∙ p) ≡ refl
    grp-cancel p q =
      Path.assoc (sym p ∙ sym q) q p
      ∙ ap (_∙ p)
          (sym (Path.assoc (sym p) (sym q) q)
          ∙ ap (sym p ∙_) (Path.invl q)
          ∙ Path.unitr (sym p))
      ∙ Path.invl p

  absorb-l-noy-retract
    : ∀ {x y} (f : hom x y) v (b : hom y v)
    → emb-noy f _ idn v b ∙ absorb-l (noy f v b)
    ≡ refl
  absorb-l-noy-retract f v b =
    ap (emb-noy f _ idn v b ∙_)
      (absorb-coh f v b)
    ∙ grp-cancel
        (ap (λ t → emb f _ t v b) (absorb-r idn))
        (interchange idn f _ idn v b)
```

### Triangle fibers

The three fiber points in `composable-contr f g`, connected by
sigma paths via contractibility. The fiber identity gives us
`σ₁₃ ≡ σ₁₂ ∙ σ₂₃` at the sigma level.

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
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt f idn w a v (noy g v b)
            ∙ ap (emb f w a v) (absorb-l (noy g v b))

      pt₂ : fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      pt₂ = f ⨾ (idn ⨾ g)
          , emb-composite f (idn ⨾ g)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
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
      -- Full sigma path underlying unitr f, living in
      -- emb-image-contr f (fiber emb (emb f)).
      unitr-σ
        : (   f ⨾ idn
            , emb-composite f idn
            ∙ funext λ w → funext λ a →
              funext λ v → funext λ b →
                ap (emb f w a v) (absorb-l b))
        ≡ (f , refl)
      unitr-σ =
        is-contr→is-prop (emb-image-contr f) _ _

      -- Lift unitr-σ from emb-image-contr f to
      -- composable-contr f g by specializing the
      -- witness at noy g v b.
      γ₁₃-pt : ∀ i → fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      γ₁₃-pt i =
        unitr f i ⨾ g
        , emb-composite (unitr f i) g
        ∙ (λ j w a v b →
            unitr-σ i .snd j w a v (noy g v b))

      -- At i=1 the inner path is refl, leaving
      -- emb-composite f g ∙ refl.
      v₃ : γ₁₃-pt i1 ≡ pt₃
      v₃ i =
        f ⨾ g
        , Path.unitr (emb-composite f g) i

      γ₁₃-full : pt₁ ≡ pt₃
      γ₁₃-full = (λ i → γ₁₃-pt i) ∙ v₃

      -- Full sigma path underlying assoc f idn g,
      -- living in E₃-contr f idn g.
      assoc-σ-fig
        : (   (f ⨾ idn) ⨾ g
            , emb-composite (f ⨾ idn) g
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f idn w' a v'
                  (noy g v' b))
        ≡ (   f ⨾ (idn ⨾ g)
            , emb-composite f (idn ⨾ g)
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite idn g b))
      assoc-σ-fig =
        is-contr→is-prop (E₃-contr f idn g) _ _

      -- Lift assoc f idn g from E₃-contr to
      -- composable-contr f g by postcomposing with
      -- ap (emb f ...) (absorb-l (noy g v b)).
      γ₁₂-pt : ∀ i → fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      γ₁₂-pt i =
        assoc f idn g i
        , assoc-σ-fig i .snd
        ∙ funext λ w → funext λ a →
          funext λ v → funext λ b →
            ap (emb f w a v)
              (absorb-l (noy g v b))

      -- At i=0: pt₁ has witness A ∙ (B ∙ C), γ₁₂-pt i0
      -- has (A ∙ B) ∙ C.
      w₁ : pt₁ ≡ γ₁₂-pt i0
      w₁ i =
        (f ⨾ idn) ⨾ g
        , Path.assoc
            (emb-composite (f ⨾ idn) g)
            (funext λ w → funext λ a →
              funext λ v → funext λ b →
                emb-composite-pt f idn w a v
                  (noy g v b))
            (funext λ w → funext λ a →
              funext λ v → funext λ b →
                ap (emb f w a v)
                  (absorb-l (noy g v b))) i

      -- At i=1: same reassociation in the other
      -- direction.
      w₂ : γ₁₂-pt i1 ≡ pt₂
      w₂ i =
        f ⨾ (idn ⨾ g)
        , sym (Path.assoc
            (emb-composite f (idn ⨾ g))
            (funext λ w → funext λ a →
              funext λ v → funext λ b →
                ap (emb f w a v)
                  (noy-composite idn g b))
            (funext λ w → funext λ a →
              funext λ v → funext λ b →
                ap (emb f w a v)
                  (absorb-l (noy g v b)))) i

      γ₁₂-full : pt₁ ≡ pt₂
      γ₁₂-full = w₁ ∙ (λ i → γ₁₂-pt i) ∙ w₂

      -- Full sigma path underlying unitl g in
      -- composable-contr idn g.
      unitl-σ
        : (   idn ⨾ g
            , emb-composite idn g)
        ≡ (   g
            , funext λ w → funext λ a →
              funext λ v → funext λ b →
                emb-noy g w a v b)
      unitl-σ =
        is-contr→is-prop (composable-contr idn g) _ _

      -- Lift unitl g from composable-contr idn g to
      -- composable-contr f g by precomposing with f.
      γ₂₃-pt : ∀ i → fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      γ₂₃-pt i =
        f ⨾ (unitl g i)
        , emb-composite f (unitl g i)
        ∙ funext λ w → funext λ a →
          funext λ v → funext λ b →
            ap (emb f w a v)
              ((λ j → unitl-σ i .snd j _ idn v b)
              ∙ absorb-l (noy g v b))

      -- At i=0: the inner path at (_ idn v b) is
      -- noy-composite idn g b ∙ absorb-l (noy g v b).
      -- The γ₂₃-pt i0 witness has
      --   ap F (noy-composite ∙ absorb-l)
      -- while pt₂ has
      --   ap F noy-composite ∙ ap F absorb-l.
      -- These differ by sym (ap-comp F ...).
      w₀ : pt₂ ≡ γ₂₃-pt i0
      w₀ i =
        f ⨾ (idn ⨾ g)
        , emb-composite f (idn ⨾ g)
        ∙ funext λ w → funext λ a →
          funext λ v → funext λ b →
            sym (ap-comp (emb f w a v)
              (noy-composite idn g b)
              (absorb-l (noy g v b))) i

      -- At i=1: the inner path is
      -- emb-noy g _ idn v b ∙ absorb-l (noy g v b)
      -- which equals refl by absorb-l-noy-retract.
      v₁ : γ₂₃-pt i1
        ≡ (f ⨾ g , emb-composite f g ∙ refl)
      v₁ i =
        f ⨾ g
        , emb-composite f g
        ∙ funext λ w → funext λ a →
          funext λ v → funext λ b →
            ap (ap (emb f w a v))
              (absorb-l-noy-retract g v b) i

      v₂
        : (f ⨾ g , emb-composite f g ∙ refl)
        ≡ pt₃
      v₂ i =
        f ⨾ g
        , Path.unitr (emb-composite f g) i

      γ₂₃-full : pt₂ ≡ pt₃
      γ₂₃-full =
        w₀ ∙ (λ i → γ₂₃-pt i) ∙ v₁ ∙ v₂

    face₁₃ : α₁₃ ≡ ap (_⨾ g) (unitr f)
    face₁₃ =
      total-contr-unique cc
        α₁₃ (ap fst γ₁₃-full)
        (ap snd σ₁₃)
        (ap snd γ₁₃-full)
      ∙ ap-comp fst (λ i → γ₁₃-pt i) v₃
      ∙ Path.unitr (ap (_⨾ g) (unitr f))

    face₁₂ : α₁₂ ≡ assoc f idn g
    face₁₂ =
      total-contr-unique cc
        α₁₂ (ap fst γ₁₂-full)
        (ap snd σ₁₂)
        (ap snd γ₁₂-full)
      ∙ ap-comp fst w₁ ((λ i → γ₁₂-pt i) ∙ w₂)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₁₂-pt i) w₂
          ∙ Path.unitr (assoc f idn g))
      ∙ Path.unitl (assoc f idn g)

    face₂₃ : α₂₃ ≡ ap (f ⨾_) (unitl g)
    face₂₃ =
      total-contr-unique cc
        α₂₃ (ap fst γ₂₃-full)
        (ap snd σ₂₃)
        (ap snd γ₂₃-full)
      ∙ ap-comp fst w₀
          ((λ i → γ₂₃-pt i) ∙ v₁ ∙ v₂)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₂₃-pt i) (v₁ ∙ v₂)
          ∙ ap (ap (f ⨾_) (unitl g) ∙_)
              (ap-comp fst v₁ v₂
              ∙ Path.unitr refl)
          ∙ Path.unitr (ap (f ⨾_) (unitl g)))
      ∙ Path.unitl (ap (f ⨾_) (unitl g))
```

### Hom-level coherences

```agda
  module triangle
    {x y z} (f : hom x y) (g : hom y z)
    where
    open triangle-fibers f g

    hom-identity
      : α₁₃ ≡ α₁₂ ∙ α₂₃
    hom-identity =
      ap (ap fst) identity
      ∙ ap-comp fst σ₁₂ σ₂₃

  triangle
    : ∀ {x y z}
      (f : hom x y) (g : hom y z)
    → ap (_⨾ g) (unitr f)
    ≡ assoc f idn g ∙ ap (f ⨾_) (unitl g)
  triangle f g =
    sym face₁₃
    ∙ hom-identity
    ∙ ap (_∙ α₂₃) face₁₂
    ∙ ap (assoc f idn g ∙_) face₂₃
    where open triangle-fibers f g
          open triangle f g
```
