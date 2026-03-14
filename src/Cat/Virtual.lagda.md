Lane Biocini
March 2026

Categories via ternary composition. The `compose-contr` field
bundles only the noy-characterization of the composite into a
contractible type. The `interchange` field separately links the
noy and yon views of composition.

The base `category` record has no coherence axioms beyond
`unit` (neutrality + idempotency of the identity),
`compose-contr`, and `interchange`. All standard categorical
structure (unit laws, associativity, pentagon) follows from
these.

The triangle identity
`ap (_⨾ g) (unitr f) ≡ assoc f idn g ∙ ap (f ⨾_) (unitl g)`
separates into a weak form (provable from the base) and the
full Mac Lane form (requiring `2-coherent`, which provides the
`absorb-coh` coherence).

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
open import Core.Groupoid
open import Core.Equiv.Base using (is-equiv; eqv-fibers)
open import Core.Function.Embedding using (equiv→lc)
```

## The category record

The record includes `absorb-r`, `absorb-l`, `noy`, and `yon` as
derived definitions inside the record, so that `compose-contr`
can reference them. The `compose-contr` field bundles only the
noy-characterization. The `interchange` field connects the noy
and yon views pointwise.

```agda
record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    emb : ∀ {x y} → hom x y
        → ∀ w → hom w x → ∀ z → hom y z → hom w z
    unit : ∀ {x} →
      Σ e ∶ hom x x
      , ( (∀ {z} → is-equiv (λ (h : hom x z) → emb e x e z h))
        × (∀ {w} → is-equiv (λ (g : hom w x) → emb e w g x e)))
      × (∀ {z} (h : hom x z) → emb e x e z (emb e x e z h) ≡ emb e x e z h)
      × (∀ {w} (g : hom w x) → emb e w (emb e w g x e) x e ≡ emb e w g x e)

  idn : ∀ {x} → hom x x
  idn = unit .fst

  absorb-l : ∀ {x} {z : ob} (h : hom x z)
    → emb idn x idn z h ≡ h
  absorb-l h = equiv→lc (unit .snd .fst .fst) (unit .snd .snd .fst h)

  absorb-r : ∀ {x} {w : ob} (g : hom w x)
    → emb idn w g x idn ≡ g
  absorb-r g = equiv→lc (unit .snd .fst .snd) (unit .snd .snd .snd g)

  noy : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  noy f z h = emb f _ idn z h

  yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  yon f w g = emb f w g _ idn

  field
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr
          (Σ s ∶ hom x z
          , emb s
            ≡ (λ w a v b → emb f w a v (noy g v b)))

    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        w (a : hom w x) v (b : hom z v)
      → emb f w a v (noy g v b)
      ≡ emb g w (yon f w a) v b

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst
  infixr 40 _⨾_

  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite f g =
    compose-contr f g .center .snd

  emb-yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb g w (yon f w a) v b)
  emb-yon-composite f g =
    emb-composite f g
    ∙ funext λ w → funext λ a → funext λ v →
      funext λ b → interchange f g w a v b

  emb-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb f w a v (noy g v b)
  emb-composite-pt f g w a v b i =
    emb-composite f g i w a v b

  emb-yon-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb g w (yon f w a) v b
  emb-yon-composite-pt f g w a v b i =
    emb-yon-composite f g i w a v b

  {-# INLINE emb #-}
  {-# INLINE _⨾_ #-}

```


## Derived operations

```agda
module Virtual {o} {h} (C : category o h) where
  open category C public
```

### Composable fiber and its eliminators

`composable-contr` restates the contractibility of the composite
fiber with `(f ⨾ g, emb-composite f g)` as center. `emb-ind`
eliminates any `(s, q)` in the fiber back to the canonical center,
and `⨾-η` witnesses that the composite is unique.

```agda
  composable-contr
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr
        (fiber (emb {x} {z})
          (λ w a v b → emb f w a v (noy g v b)))
  composable-contr f g .center =
    f ⨾ g , emb-composite f g
  composable-contr f g .paths (s , p) =
    compose-contr f g .paths (s , p)

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

### Embedding property and its eliminators

`composable-contr idn f` gives `is-contr (fiber emb target)` where
`target w a v b = emb idn w a v (noy f v b)`. By interchange,
this equals `emb f w (yon idn w a) v b = emb f w a v b` via
right absorption. So `fiber emb (emb f)` is contractible for
every `f`, making `emb` an embedding.

`emb-image-ind` eliminates any `(n, q)` in the image fiber back
to `(m, refl)`, and `emb-inj` is faithful: `emb n ≡ emb m`
implies `n ≡ m`.

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

### Yon-characterized composite and its eliminator

Interchange swaps `noy` for `yon` in the composite target,
giving a dual fiber with the same center. `emb-yon-ind`
eliminates over this alternative characterization.

```agda
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

### Argument swap

```agda
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
  E₃-contr f g h .center .fst = (f ⨾ g) ⨾ h
  E₃-contr f g h .center .snd =
    emb-composite (f ⨾ g) h
    ∙ funext λ w → funext λ a →
      funext λ v → funext λ b →
        emb-composite-pt f g w a v (noy h v b)
  E₃-contr f g h .paths =
    is-contr→is-prop
      (subst (is-contr ∘ fiber emb) path
        (composable-contr (f ⨾ g) h)) _
    where
      path : (λ w a v b →
                emb (f ⨾ g) w a v (noy h v b))
            ≡ E₃ f g h
      path = funext λ w → funext λ a →
        funext λ v → funext λ b →
          emb-composite-pt f g w a v (noy h v b)

  E₃-ind
    : ∀ {u} {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (P : (s : hom x w)
         → emb s ≡ E₃ f g h
         → Type u)
    → P (E₃-contr f g h .center .fst)
        (E₃-contr f g h .center .snd)
    → ∀ s q → P s q
  E₃-ind f g h P base s q =
    contr-ind (E₃-contr f g h)
      (λ where (s , q) → P s q)
      base (s , q)

  assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h =
    ap fst
      (is-contr→is-prop (E₃-contr f g h)
        (E₃-contr f g h .center) rhs)
    where
      rhs : fiber emb (E₃ f g h)
      rhs = f ⨾ (g ⨾ h)
          , emb-composite f (g ⨾ h)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v)
                (noy-composite g h b)
```

### Pentagon

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
  E₄-contr f g h k .center .fst = ((f ⨾ g) ⨾ h) ⨾ k
  E₄-contr f g h k .center .snd =
    emb-composite ((f ⨾ g) ⨾ h) k
    ∙ funext λ w → funext λ a →
      funext λ v → funext λ b →
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
      path = funext λ w → funext λ a →
        funext λ v → funext λ b →
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
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
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
    ≡ pcom (sym (ap (_⨾ k) (assoc f g h)))
           (assoc f (g ⨾ h) k)
           (ap (f ⨾_) (assoc g h k))
  pentagon f g h k =
    pcom (ap (_∙ α₄₅) face₁₄
        ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
      hom-identity
      (λ i → pcom (sym (face₁₂ i)) (face₂₃ i) (face₃₅ i))
    where open pentagon-fibers f g h k
          open pentagon f g h k
```

### Weak triangle

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
      unitr-σ
        : (   f ⨾ idn
            , emb-composite f idn
            ∙ funext λ w → funext λ a →
              funext λ v → funext λ b →
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
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite idn g b))
      assoc-σ-fig =
        is-contr→is-prop (E₃-contr f idn g) _ _

      γ₁₂-pt : ∀ i → fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      γ₁₂-pt i =
        assoc f idn g i
        , assoc-σ-fig i .snd
        ∙ funext λ w → funext λ a →
          funext λ v → funext λ b →
            ap (emb f w a v)
              (absorb-l (noy g v b))

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

The `2-Cat` module opens both `Cat C` and `2-coherent coh`,
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
      open Virtual.triangle-fibers C f g

      private
        cc = composable-contr f g

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

        unitl-σ
          : (   idn ⨾ g
              , emb-composite idn g)
          ≡ (   g
              , funext λ w → funext λ a →
                funext λ v → funext λ b →
                  emb-noy g w a v b)
        unitl-σ =
          is-contr→is-prop (composable-contr idn g)
            _ _

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

        w₀ : pt₂ ≡ γ₂₃-pt i0
        w₀ i =
          f ⨾ (idn ⨾ g)
          , emb-composite f (idn ⨾ g)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              sym (ap-comp (emb f w a v)
                (noy-composite idn g b)
                (absorb-l (noy g v b))) i

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
    where open Virtual.triangle-fibers C f g
          open Virtual.triangle C f g
          open face₂₃-proof f g
```

## Opposite category

Swapping the two `(object, morphism)` pairs in `emb` reverses the
direction of all hom-types. The identity is unchanged; left and
right absorption/idempotency swap roles. Composition in `op` uses
`composable-swap ∘ composable-yon` to reverse the composite fiber.

```agda
module _ {o h} (C : category o h) where
  private module C = Virtual C

  op : category o h
  op .category.ob = C.ob
  op .category.hom x y = C.hom y x
  op .category.emb f w a v b = C.emb f v b w a
  op .category.unit =
    C.idn
    , (C.unit .snd .fst .snd
      , C.unit .snd .fst .fst)
    , C.unit .snd .snd .snd
    , C.unit .snd .snd .fst
  op .category.compose-contr f g =
    C.composable-swap (C.composable-yon g f)
  op .category.interchange f g w a v b =
    sym (C.interchange g f v b w a)
```

### Opposite involution

Double op is the identity on categories. The `ob`, `hom`, `emb`,
and `interchange` fields are definitionally invariant (double swap
is identity for both argument pairs and `sym`). The `unit` field
uses Σ-eta: swapping `(a, b)` twice recovers `(a, b)`.
The `compose-contr` field uses `is-prop→PathP` since
contractibility is propositional.

```agda
module _ {o h} (C : category o h) where
  private module C = Virtual C

  private
    uc : ∀ {x}
      → category.unit (op (op C)) {x} ≡ C.unit {x}
    uc i = C.unit

  op-invol : op (op C) ≡ C
  op-invol i .category.ob = C.ob
  op-invol i .category.hom = C.hom
  op-invol i .category.emb = C.emb
  op-invol i .category.unit {x} = uc {x} i
  op-invol i .category.compose-contr {x} {y} {z} f g =
    is-prop→PathP
      {A = λ _ → is-contr
        (Σ s ∶ C.hom x z
        , C.emb s
          ≡ (λ w a v b →
              C.emb f w a v (C.noy g v b)))}
      (λ _ → is-contr-is-prop _)
      (category.compose-contr (op (op C)) f g)
      (C.compose-contr f g) i
  op-invol i .category.interchange f g w a v b =
    C.interchange f g w a v b
```
