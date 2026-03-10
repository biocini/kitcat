Lane Biocini
March 2026

Categories via ternary composition with interchange. The basic data
is a ternary sandwich embedding `emb f w g z h` representing the
composite `g . f . h`. Two binary compositions arise from
specializing the two outer slots to `idn`:

    yon f w g  =  emb f w g y idn    -- covariant face
    noy f z h  =  emb f x idn z h   -- contravariant face

These yield two a priori distinct compositions — `⨾₁` feeds `g`'s
contravariant face into `f`'s right slot, while `⨾₂` feeds `f`'s
covariant face into `g`'s left slot. Each has one free unit law and
free associativity. The interchange axiom equates them, supplying
the missing unit laws.

The embedding property of `emb` is derived, not assumed:
`composable-contr idn f` gives a contractible fiber over the
composite target, and interchange + absorption collapses that
target to `emb f`, making `fiber emb (emb f)` contractible for
every `f`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Virtual where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
open import Core.Function.Base
open import Core.Path.Base

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

  field
    composable-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr
          (fiber (emb {x} {z})
            (λ w a v b →
              emb f w a v (emb g _ idn v b)))
    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        w (a : hom w x) v (b : hom z v)
      → emb f w a v (emb g _ idn v b)
      ≡ emb g w (emb f w a _ idn) v b

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

  absorb-r
    : ∀ {x} {w : ob} (g : hom w x)
    → emb idn w g x idn ≡ g
  absorb-r = idn-contr .center .snd .fst

  absorb-l
    : ∀ {x} {z : ob} (h : hom x z)
    → emb idn x idn z h ≡ h
  absorb-l = idn-contr .center .snd .snd

  yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  yon f w g = emb f w g _ idn

  noy : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  noy f z h = emb f _ idn z h
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
    subst (is-contr ∘ fiber emb) path (composable-contr idn f)
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
    subst (is-contr ∘ fiber emb) path (composable-contr f g)
    where
      path
        : (λ w a v b → emb f w a v (noy g v b))
        ≡ (λ w a v b → emb g w (yon f w a) v b)
      path = funext λ w → funext λ a → funext λ v →
        funext λ b → interchange f g w a v b

  composable-swap
    : ∀ {x y}
      {target : ∀ w → hom w x → ∀ v → hom y v → hom w v}
    → is-contr (fiber emb target)
    → is-contr
        (fiber {B = ∀ w → hom y w → ∀ v → hom v x → hom v w}
          (λ s w a v b → emb s v b w a)
          (λ w a v b → target v b w a))
  composable-swap c .center .fst = c .center .fst
  composable-swap c .center .snd i w a v b =
    c .center .snd i v b w a
  composable-swap {target = target} c .paths (s' , q') i .fst =
    c .paths (s' , q'') i .fst
    where
      q'' : emb s' ≡ target
      q'' i w a v b = q' i v b w a
  composable-swap {target = target} c .paths (s' , q') i .snd j w a v b =
    c .paths (s' , q'') i .snd j v b w a
    where
      q'' : emb s' ≡ target
      q'' i w a v b = q' i v b w a
```

### Composite equations

```agda
  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g) ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite f g = composable-contr f g .center .snd

  emb-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b ≡ emb f w a v (noy g v b)
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
         → (∀ {z} (h : hom x z) → emb e x e z h ≡ h)
         → Type u)
    → P idn absorb-r absorb-l
    → (a : idn-fiber) → P (a .fst) (a .snd .fst) (a .snd .snd)
  idn-ind P base a =
    coe01 (λ i → P (p i .fst) (p i .snd .fst) (p i .snd .snd)) base
    where p = idn-contr .paths a

  idn-unique
    : ∀ {x} (e : hom x x)
    → (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
    → (∀ {z} (h : hom x z) → emb e x e z h ≡ h)
    → idn ≡ e
  idn-unique e r l = idn-ind (λ e _ _ → idn ≡ e) refl (e , r , l)
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
      path = sym (emb-image-contr m .paths (m , refl))
           ∙ emb-image-contr m .paths (n , q)

  emb-inj
    : ∀ {x y} {f g : hom x y}
    → emb f ≡ emb g → f ≡ g
  emb-inj {f = f} {g} p =
    emb-image-ind f (λ n _ → f ≡ n) refl g (sym p)
```

The yon-characterized composite: interchange swaps `noy` for `yon`
in the composite target, giving a dual fiber with the same center.
`emb-yon-ind` eliminates over this alternative characterization.

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
      path : (f ⨾ g , emb-yon-composite f g) ≡ (s , q)
      path = sym (composable-yon f g .paths _)
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
    (funext λ w → funext λ a → funext λ v → funext λ b →
      ap (emb f w a v) (sym (absorb-l b))
      ∙ interchange f idn w a v b
      ∙ ap (λ t → emb idn w t v b) (λ i → p i w a)
      ∙ sym (interchange g idn w a v b)
      ∙ ap (emb g w a v) (absorb-l b))

  noy-inj
    : ∀ {x y} {f g : hom x y}
    → noy f ≡ noy g → f ≡ g
  noy-inj {f = f} {g} p = emb-inj
    (funext λ w → funext λ a → funext λ v → funext λ b →
      ap (λ t → emb f w t v b) (sym (absorb-r a))
      ∙ sym (interchange idn f w a v b)
      ∙ ap (λ t → emb idn w a v t) (λ i → p i v b)
      ∙ interchange idn g w a v b
      ∙ ap (λ t → emb g w t v b) (absorb-r a))

  emb-yon
    : ∀ {x y} (f : hom x y) w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w (yon f w a) v b
  emb-yon f w a v b =
    ap (emb f w a v) (sym (absorb-l b))
    ∙ interchange f idn w a v b

  emb-noy
    : ∀ {x y} (f : hom x y) w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w a v (noy f v b)
  emb-noy f w a v b =
    ap (λ t → emb f w t v b) (sym (absorb-r a))
    ∙ sym (interchange idn f w a v b)
```

### Coherent unit laws and associativity

The unit laws and associativity are defined as projections from
contractible fibers rather than via `emb-inj` / `⨾-η`. Each
law is `ap fst` of the unique path between two points in a
contractible fiber of `emb`. This gives control over the
emb-image at every intermediate point along the path, which is
needed for pentagon and triangle coherences.

```agda
  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  unitr f =
    ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
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
    ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = idn ⨾ f
          , emb-composite idn f
          ∙ sym (funext λ w → funext λ a → funext λ v →
              funext λ b → emb-noy f w a v b)

      rhs : fiber emb (emb f)
      rhs = f , refl

  private
    E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z)
        (h : hom z w)
      → ∀ w' → hom w' x → ∀ v → hom w v → hom w' v
    E₃ f g h =
      λ w a v b → emb f w a v (noy g v (noy h v b))

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
    ap fst (is-contr→is-prop (E₃-contr f g h) lhs rhs)
    where
      lhs : fiber emb (E₃ f g h)
      lhs = (f ⨾ g) ⨾ h
          , emb-composite (f ⨾ g) h
          ∙ funext λ w → funext λ a → funext λ v →
            funext λ b →
              emb-composite-pt f g w a v (noy h v b)

      rhs : fiber emb (E₃ f g h)
      rhs = f ⨾ (g ⨾ h)
          , emb-composite f (g ⨾ h)
          ∙ funext λ w → funext λ a → funext λ v →
            funext λ b →
              ap (emb f w a v) (noy-composite g h b)
```

### Coherences

The pentagon and triangle identities are stated at the fiber
level. Each bracketing of a composite sits in a contractible
fiber of `emb`; the coherences follow from `is-contr→is-set`
— any two paths between the same fiber points are equal.
The hom-level edges are the `ap fst` projections of the
fiber-level edges.

```agda
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
  E₄-contr f g h k =
    subst (is-contr ∘ fiber emb) path
      (composable-contr ((f ⨾ g) ⨾ h) k)
    where
      path
        : (λ w a v b →
            emb ((f ⨾ g) ⨾ h) w a v (noy k v b))
        ≡ E₄ f g h k
      path = funext λ w → funext λ a →
        funext λ v → funext λ b →
          emb-composite-pt (f ⨾ g) h w a v (noy k v b)
        ∙ emb-composite-pt f g w a v
            (noy h v (noy k v b))

  module pentagon-fibers
    {x y z w v}
    (f : hom x y) (g : hom y z)
    (h : hom z w) (k : hom w v)
    where
    private
      E₄c = E₄-contr f g h k

      pt₁ : fiber emb (E₄ f g h k)
      pt₁ = ((f ⨾ g) ⨾ h) ⨾ k
          , emb-composite ((f ⨾ g) ⨾ h) k
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt (f ⨾ g) h w a v
                (noy k v b)
            ∙ emb-composite-pt f g w a v
                (noy h v (noy k v b))

      pt₂ : fiber emb (E₄ f g h k)
      pt₂ = (f ⨾ (g ⨾ h)) ⨾ k
          , emb-composite (f ⨾ (g ⨾ h)) k
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt f (g ⨾ h) w a v
                (noy k v b)
            ∙ ap (emb f w a v)
                (noy-composite g h (noy k v b))

      pt₃ : fiber emb (E₄ f g h k)
      pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
          , emb-composite f ((g ⨾ h) ⨾ k)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v)
                (noy-composite (g ⨾ h) k b)
            ∙ ap (emb f w a v)
                (noy-composite g h (noy k v b))

      pt₄ : fiber emb (E₄ f g h k)
      pt₄ = (f ⨾ g) ⨾ (h ⨾ k)
          , emb-composite (f ⨾ g) (h ⨾ k)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt f g w a v
                (noy (h ⨾ k) v b)
            ∙ ap (λ t → emb f w a v (noy g v t))
                  (noy-composite h k b)

      pt₅ : fiber emb (E₄ f g h k)
      pt₅ = f ⨾ (g ⨾ (h ⨾ k))
          , emb-composite f (g ⨾ (h ⨾ k))
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
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

    identity : σ₁₄ ∙ σ₄₅ ≡ σ₁₂ ∙ σ₂₃ ∙ σ₃₅
    identity = is-contr→is-set E₄c pt₁ pt₅
      (σ₁₄ ∙ σ₄₅) (σ₁₂ ∙ σ₂₃ ∙ σ₃₅)

    -- The full E₃ fiber path underlying assoc, giving
    -- access to the snd component (the witness path).
    private
      assoc-σ
        : ∀ {x y z w}
          (f : hom x y) (g : hom y z) (h : hom z w)
        → (   (f ⨾ g) ⨾ h
            , emb-composite (f ⨾ g) h
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f g w' a v'
                  (noy h v' b))
        ≡ (   f ⨾ (g ⨾ h)
            , emb-composite f (g ⨾ h)
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite g h b))
      assoc-σ f g h =
        is-contr→is-prop (E₃-contr f g h) _ _

      -- Lift the assoc f g h fiber path to E₄ via _⨾ k.
      -- At each i, the morphism is assoc f g h i ⨾ k and
      -- the witness composes emb-composite with the E₃
      -- witness specialized at noy k v b.
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
        ∙ funext λ w' → funext λ a →
          funext λ v' → funext λ b →
            sym (ap-comp (emb f w' a v')
              (noy-composite (g ⨾ h) k b)
              (noy-composite g h (noy k v' b))) i

      v₅ : γ₃₅-pt i1 ≡ pt₅
      v₅ i =
        f ⨾ (g ⨾ (h ⨾ k))
        , emb-composite f (g ⨾ (h ⨾ k))
        ∙ funext λ w' → funext λ a →
          funext λ v' → funext λ b →
            ap-comp (emb f w' a v')
              (noy-composite g (h ⨾ k) b)
              (ap (noy g v') (noy-composite h k b)) i

      γ₃₅-full : pt₃ ≡ pt₅
      γ₃₅-full = v₃ ∙ (λ i → γ₃₅-pt i) ∙ v₅

      -- Lift assoc f (g⨾h) k from E₃ to E₄ by postcomposing
      -- each fiber witness with ap (emb f ...) (noy-composite g h ...).
      -- Both boundary corrections are Path.assoc: the E₃ witness
      -- and the correction concatenate as (X ∙ Y) ∙ Z while the
      -- pentagon fiber points have X ∙ (Y ∙ Z).
      γ₂₃-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₂₃-pt i =
        assoc f (g ⨾ h) k i
        , assoc-σ f (g ⨾ h) k i .snd
        ∙ funext λ w' → funext λ a →
          funext λ v' → funext λ b →
            ap (emb f w' a v')
              (noy-composite g h (noy k v' b))

      w₂ : pt₂ ≡ γ₂₃-pt i0
      w₂ i =
        (f ⨾ (g ⨾ h)) ⨾ k
        , Path.assoc
            (emb-composite (f ⨾ (g ⨾ h)) k)
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f (g ⨾ h) w' a v'
                  (noy k v' b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite g h (noy k v' b))) i

      w₃ : γ₂₃-pt i1 ≡ pt₃
      w₃ i =
        f ⨾ ((g ⨾ h) ⨾ k)
        , sym (Path.assoc
            (emb-composite f ((g ⨾ h) ⨾ k))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite (g ⨾ h) k b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite g h (noy k v' b)))) i

      γ₂₃-full : pt₂ ≡ pt₃
      γ₂₃-full = w₂ ∙ (λ i → γ₂₃-pt i) ∙ w₃

      -- Lift assoc f g (h⨾k) from E₃ to E₄ by postcomposing
      -- with ap (emb f ... noy g ...) (noy-composite h k b).
      -- Both boundaries are Path.assoc.
      γ₄₅-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₄₅-pt i =
        assoc f g (h ⨾ k) i
        , assoc-σ f g (h ⨾ k) i .snd
        ∙ funext λ w' → funext λ a →
          funext λ v' → funext λ b →
            ap (λ t → emb f w' a v' (noy g v' t))
              (noy-composite h k b)

      w₄ : pt₄ ≡ γ₄₅-pt i0
      w₄ i =
        (f ⨾ g) ⨾ (h ⨾ k)
        , Path.assoc
            (emb-composite (f ⨾ g) (h ⨾ k))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f g w' a v'
                  (noy (h ⨾ k) v' b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (λ t → emb f w' a v' (noy g v' t))
                  (noy-composite h k b)) i

      w₅ : γ₄₅-pt i1 ≡ pt₅
      w₅ i =
        f ⨾ (g ⨾ (h ⨾ k))
        , sym (Path.assoc
            (emb-composite f (g ⨾ (h ⨾ k)))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite g (h ⨾ k) b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (λ t → emb f w' a v' (noy g v' t))
                  (noy-composite h k b))) i

      γ₄₅-full : pt₄ ≡ pt₅
      γ₄₅-full = w₄ ∙ (λ i → γ₄₅-pt i) ∙ w₅

      -- Lift assoc (f⨾g) h k from E₃ to E₄ by postcomposing
      -- with emb-composite-pt f g ... (noy h (noy k ...)).
      -- The i=i0 boundary is Path.assoc. The i=i1 boundary
      -- requires a naturality correction: the square
      --   emb-composite-pt f g w a v (noy-composite h k b i) j
      -- relates ap (emb (f⨾g)) (noy-composite) ∙ emb-composite-pt
      -- to emb-composite-pt ∙ ap (emb f ... noy g ...) (noy-composite).
      γ₁₄-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₁₄-pt i =
        assoc (f ⨾ g) h k i
        , assoc-σ (f ⨾ g) h k i .snd
        ∙ funext λ w' → funext λ a →
          funext λ v' → funext λ b →
            emb-composite-pt f g w' a v'
              (noy h v' (noy k v' b))

      w₁ : pt₁ ≡ γ₁₄-pt i0
      w₁ i =
        ((f ⨾ g) ⨾ h) ⨾ k
        , Path.assoc
            (emb-composite ((f ⨾ g) ⨾ h) k)
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt (f ⨾ g) h w' a v'
                  (noy k v' b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f g w' a v'
                  (noy h v' (noy k v' b))) i

      -- Naturality of emb-composite-pt f g with respect to
      -- noy-composite h k: applying emb-composite-pt to
      -- noy-composite gives a square, and Path.commutes
      -- extracts the commuting equation.
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
          B₁₄ = funext λ w' → funext λ a →
            funext λ v' → funext λ b →
              ap (emb (f ⨾ g) w' a v')
                (noy-composite h k b)
          C₁₄ = funext λ w' → funext λ a →
            funext λ v' → funext λ b →
              emb-composite-pt f g w' a v'
                (noy h v' (noy k v' b))
          N₁₄ : B₁₄ ∙ C₁₄
              ≡ (funext λ w' → funext λ a →
                  funext λ v' → funext λ b →
                    emb-composite-pt f g w' a v'
                      (noy (h ⨾ k) v' b)
                  ∙ ap (λ t → emb f w' a v' (noy g v' t))
                        (noy-composite h k b))
          N₁₄ j = funext λ w' → funext λ a →
            funext λ v' → funext λ b →
              w₁₄-nat w' a v' b j

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
          ∙ Path.unitr (ap (f ⨾_) (assoc g h k)))
      ∙ Path.unitl (ap (f ⨾_) (assoc g h k))

    face₂₃ : α₂₃ ≡ assoc f (g ⨾ h) k
    face₂₃ =
      total-contr-unique E₄c
        α₂₃ (ap fst γ₂₃-full)
        (ap snd σ₂₃)
        (ap snd γ₂₃-full)
      ∙ ap-comp fst w₂ ((λ i → γ₂₃-pt i) ∙ w₃)
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
      ∙ ap-comp fst w₄ ((λ i → γ₄₅-pt i) ∙ w₅)
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
      ∙ ap-comp fst w₁ ((λ i → γ₁₄-pt i) ∙ w₁₄)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₁₄-pt i) w₁₄
          ∙ Path.unitr (assoc (f ⨾ g) h k))
      ∙ Path.unitl (assoc (f ⨾ g) h k)

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
            ∙ ap (emb f w a v) (absorb-l (noy g v b))

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
```

### Hom-level coherences

The fiber-level pentagon and triangle identities project to
hom-level identities via `ap (ap fst)` and `ap-comp fst`. Each
edge `αᵢⱼ = ap fst σᵢⱼ` of the pentagon is then identified with
its classical counterpart (whiskered associator or plain
associator) by lifting the E₃-level fiber path to E₄ and
appealing to contractibility.

```agda
  module pentagon
    {x y z w v}
    (f : hom x y) (g : hom y z)
    (h : hom z w) (k : hom w v)
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
    : ∀ {x y z w v}
      (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w v)
    → assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k) ≡ ap (_⨾ k) (assoc f g h) ∙ assoc f (g ⨾ h) k ∙ ap (f ⨾_) (assoc g h k)
  pentagon f g h k =
    sym (ap (_∙ α₄₅) face₁₄ ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
    ∙ hom-identity
    ∙ ap (_∙ (α₂₃ ∙ α₃₅)) face₁₂
    ∙ ap (ap (_⨾ k) (assoc f g h) ∙_)
        (ap (_∙ α₃₅) face₂₃
        ∙ ap (assoc f (g ⨾ h) k ∙_) face₃₅)
    where open pentagon-fibers f g h k
          open pentagon f g h k


  -- TODO
  module triangle
    {x y z} (f : hom x y) (g : hom y z)
    where
    open triangle-fibers f g

    hom-identity
      : α₁₃ ≡ α₁₂ ∙ α₂₃
    hom-identity =
      ap (ap fst) identity
      ∙ ap-comp fst σ₁₂ σ₂₃

```

### Edge identifications

Each pentagon edge `αᵢⱼ` equals a classical associator or
whiskered associator. The E₃ fiber path underlying `assoc`
lifts to an E₄ fiber path whose first projection is the
classical edge, and `total-contr-unique` on the E₄ fiber
identifies it with `αᵢⱼ`. The whiskered edges `α₁₂` and
`α₃₅` lift directly; the un-whiskered edges `α₁₄`, `α₂₃`,
`α₄₅` require `Path.assoc` corrections at both boundaries
(reassociating the concatenation of witness paths), and
`α₁₄` additionally requires a naturality correction for
`emb-composite-pt f g` applied to `noy-composite h k`.
All five edge identifications and the hom-level pentagon
and triangle are defined inside the pentagon/triangle
modules above.

## Opposite category

The opposite category swaps morphism direction. For the ternary
embedding, `op.emb f w a v b = C.emb f v b w a` — the two
(object, morphism) pairs are exchanged.

The identity is the same `C.idn`, with the two absorption
conditions swapped. For composition, `op`'s composable fiber at
`(f, g)` corresponds to C's composable fiber at `(g, f)` after
applying interchange and swapping the four bound variables.

```agda
module _ {o h} (C : category o h) where
  private module C = Cat C

  op : category o h
  op .category.ob = C.ob
  op .category.hom x y = C.hom y x
  op .category.emb f w a v b = C.emb f v b w a
  op .category.idn-contr .center =
    C.idn , C.absorb-l , C.absorb-r
  op .category.idn-contr .paths (e' , l' , r') i =
    let q = C.idn-contr .paths (e' , r' , l') i
    in q .fst , q .snd .snd , q .snd .fst
  op .category.composable-contr {x} {y} {z} f g =
    C.composable-swap {x = z} {y = x} (C.composable-yon g f)
  op .category.interchange f g w a v b =
    sym (C.interchange g f v b w a)
```

### Opposite involution

`op (op C) .idn-contr` and `C.idn-contr` agree definitionally on both
`.center` and `.paths` — the double swap on `(absorb-r, absorb-l)` in
`.center` cancels, and the double swap of argument order in `.paths`
cancels. This lets us define the `idn-contr` path by constant
copatterns, keeping `idn` definitionally constant along the path and
making all downstream fields (`composable-contr`, `interchange`)
straightforward.

```agda
module _ {o h} (C : category o h) where
  private module C = Cat C

  -- The double swap on idn-contr is definitionally the identity:
  -- op swaps (absorb-r, absorb-l) in .center, and swaps
  -- argument order in .paths. Doing this twice cancels out.
  -- We define ic by constant copatterns rather than is-prop→PathP
  -- so that ic i .center .fst = C.idn definitionally for all i.
  private
    ic : ∀ {x}
      → category.idn-contr (op (op C)) {x} ≡ C.idn-contr {x}
    ic i .center = C.idn-contr .center
    ic i .paths = C.idn-contr .paths

  op-invol : op (op C) ≡ C
  op-invol i .category.ob = C.ob
  op-invol i .category.hom = C.hom
  op-invol i .category.emb = C.emb
  op-invol i .category.idn-contr {x} = ic {x} i
  op-invol i .category.composable-contr
    {x} {y} {z} f g =
    is-prop→PathP
      {A = λ _ → is-contr
        (fiber (C.emb {x} {z})
          (λ w a v b →
            C.emb f w a v
              (C.emb g _ C.idn v b)))}
      (λ _ → is-contr-is-prop _)
      (category.composable-contr (op (op C)) f g)
      (C.composable-contr f g) i
  op-invol i .category.interchange f g w a v b =
    C.interchange f g w a v b
```

## Ternary functors

A functor between ternary categories preserves the embedding
operation. The primitive field `emb-natural` says that `hmap`
commutes with the ternary embedding: applying `hmap` to each
argument of `D.emb` equals applying `hmap` to the result of
`C.emb`.

```agda
module _
  {o h o' h'}
  (C : category o h)
  (D : category o' h')
  where
  private
    module C = Cat C
    module D = Cat D

  record functor : Type (o ⊔ h ⊔ o' ⊔ h') where
    no-eta-equality

    field
      map  : C.ob → D.ob
      hmap : ∀ {x y}
        → C.hom x y → D.hom (map x) (map y)
      emb-natural
        : ∀ {x y} (f : C.hom x y)
          w (a : C.hom w x) v (b : C.hom y v)
        → D.emb (hmap f) (map w) (hmap a)
            (map v) (hmap b)
        ≡ hmap (C.emb f w a v b)

  {-# INLINE functor.constructor #-}
```

Derived naturality conditions arise from specializing the outer
slots of `emb-natural`. Since `C.yon f w a = C.emb f w a _ C.idn`
and `C.noy f v b = C.emb f _ C.idn v b` hold definitionally, the
right-hand sides simplify directly.

```agda
  module Functor (F : functor) where
    open functor F public

    yon-natural-F
      : ∀ {x y} (f : C.hom x y)
        w (a : C.hom w x)
      → D.emb (hmap f) (map w) (hmap a)
          (map y) (hmap C.idn)
      ≡ hmap (C.yon f w a)
    yon-natural-F f w a =
      emb-natural f w a _ C.idn

    noy-natural-F
      : ∀ {x y} (f : C.hom x y)
        v (b : C.hom y v)
      → D.emb (hmap f) (map x) (hmap C.idn)
          (map v) (hmap b)
      ≡ hmap (C.noy f v b)
    noy-natural-F f v b =
      emb-natural f _ C.idn v b

    absorb-r-F
      : ∀ {x} {w : C.ob} (a : C.hom w x)
      → D.emb (hmap C.idn) (map w) (hmap a)
          (map x) (hmap C.idn)
      ≡ hmap a
    absorb-r-F a =
      emb-natural C.idn _ a _ C.idn
      ∙ ap hmap (C.absorb-r a)

    absorb-l-F
      : ∀ {x} {v : C.ob} (b : C.hom x v)
      → D.emb (hmap C.idn) (map x) (hmap C.idn)
          (map v) (hmap b)
      ≡ hmap b
    absorb-l-F b =
      emb-natural C.idn _ C.idn _ b
      ∙ ap hmap (C.absorb-l b)
```

### Identity functor

Both `map` and `hmap` are the identity, so `emb-natural` holds by
`refl` — the two sides are definitionally equal.

```agda
idn-functor
  : ∀ {o h} (C : category o h)
  → functor C C
idn-functor C .functor.map  = id
idn-functor C .functor.hmap = id
idn-functor C .functor.emb-natural _ _ _ _ _ = refl
```

### Functor composition

The `emb-natural` proof for `G ∘F F` applies `G.emb-natural` to
reduce the outer embedding in `E`, then `ap G.hmap` of
`F.emb-natural` to reduce the inner one.

```agda
module _
  {o h o' h' o'' h''}
  {C : category o h}
  {D : category o' h'}
  {E : category o'' h''}
  (F : functor C D)
  (G : functor D E)
  where
  private
    module F = Functor C D F
    module G = Functor D E G

  _∘F_ : functor C E
  _∘F_ .functor.map  = G.map ∘ F.map
  _∘F_ .functor.hmap = G.hmap ∘ F.hmap
  _∘F_ .functor.emb-natural f w a v b =
    G.emb-natural (F.hmap f)
      (F.map w) (F.hmap a) (F.map v) (F.hmap b)
    ∙ ap G.hmap (F.emb-natural f w a v b)
```
