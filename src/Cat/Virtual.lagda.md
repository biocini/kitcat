Lane Biocini
March 2026

Categories via ternary composition. The `compose-contr` field
bundles only the noy-characterization of the composite into a
contractible type. The `interchange` field separately links the
noy and yon views of composition. The `yon-eval` field
establishes `yon f x idn ≡ f`.

The base `category` record has no coherence axioms beyond
`unit` (neutrality + yon-idempotency of the identity),
`compose-contr`, `interchange`, and `yon-eval`. All standard
categorical structure (unit laws, associativity, pentagon)
follows from these. The identity is unique (`unit-is-prop`).

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

The record includes `noy` and `yon` as derived definitions
inside the record, so that `compose-contr` can reference them.
The `compose-contr` field bundles only the
noy-characterization. The `interchange` field connects the noy
and yon views pointwise. The `yon-eval` field establishes that
`yon f x idn ≡ f`. Absorption (`absorb-l`, `absorb-r`) is
derived from yon-idempotency + composition + left cancellation.

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
      × (emb e x e x e ≡ e)

  idn : ∀ {x} → hom x x
  idn = unit .fst

  noy : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  noy f z h = emb f _ idn z h

  yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  yon f w g = emb f w g _ idn

  unit-eqvl : ∀ {x} {z : ob}
    → is-equiv (λ (h : hom x z) → noy idn z h)
  unit-eqvl = unit .snd .fst .fst

  unit-eqvr : ∀ {x} {w : ob}
    → is-equiv (λ (g : hom w x) → yon idn w g)
  unit-eqvr = unit .snd .fst .snd

  yon-idpt : ∀ {x} → yon (idn {x}) x idn ≡ idn
  yon-idpt = unit .snd .snd

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

    yon-eval
      : ∀ {x y} (f : hom x y) → yon f x idn ≡ f

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst
  infixr 40 _⨾_

  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite f g =
    compose-contr f g .center .snd

  {-# INLINE emb #-}
  {-# INLINE _⨾_ #-}

```


## Derived operations

```agda
module Virtual {o} {h} (C : category o h) where
  open category C public

  emb-ext
    : ∀ {x y} {F G : ∀ w → hom w x → ∀ v → hom y v → hom w v}
    → (∀ w (a : hom w x) v (b : hom y v) → F w a v b ≡ G w a v b)
    → F ≡ G
  emb-ext h =
    funext λ w → funext λ a → funext λ v → funext λ b → h w a v b

  emb-yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb g w (yon f w a) v b)
  emb-yon-composite f g =
    emb-composite f g
    ∙ emb-ext λ w a v b → interchange f g w a v b

  emb-yon-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb g w (yon f w a) v b
  emb-yon-composite-pt f g w a v b i =
    emb-yon-composite f g i w a v b

  emb-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb f w a v (noy g v b)
  emb-composite-pt f g w a v b i =
    emb-composite f g i w a v b

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

  comp-eq
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → f ⨾ g ≡ yon g _ f
  comp-eq f g =
    sym (yon-eval (f ⨾ g))
    ∙ yon-composite f g _ idn
    ∙ ap (yon g _) (yon-eval f)

  idem : ∀ {x} → idn {x} ⨾ idn ≡ idn
  idem = comp-eq idn idn ∙ yon-idpt

  absorb-l : ∀ {x} {z : ob} (h : hom x z)
    → noy idn z h ≡ h
  absorb-l {x} h = equiv→lc unit-eqvl noy-idn-idpt
    where
      noy-idn-idpt : noy idn _ (noy idn _ h) ≡ noy idn _ h
      noy-idn-idpt =
        sym (subst (λ t → noy t _ h ≡ noy idn _ (noy idn _ h))
          idem (noy-composite idn idn h))

  absorb-r : ∀ {x} {w : ob} (g : hom w x)
    → yon idn w g ≡ g
  absorb-r {x} g = equiv→lc unit-eqvr yon-idn-idpt
    where
      yon-idn-idpt : yon idn _ (yon idn _ g) ≡ yon idn _ g
      yon-idn-idpt =
        sym (subst (λ t → yon t _ g ≡ yon idn _ (yon idn _ g))
          idem (yon-composite idn idn _ g))
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
      path = emb-ext λ w a v b →
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
      path = emb-ext λ w a v b →
        interchange f g w a v b

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

### Injectivity and decomposition

Both `yon` and `noy` are injective, following from interchange
and `emb-inj`. The `emb-yon` and `emb-noy` lemmas express
`emb f` in terms of `yon` and `noy`.

```agda
  yon-inj
    : ∀ {x y} {f g : hom x y}
    → yon f ≡ yon g → f ≡ g
  yon-inj {f = f} {g} p = emb-inj
    (emb-ext λ w a v b →
        ap (emb f w a v) (sym (absorb-l b))
        ∙ interchange f idn w a v b
        ∙ ap (λ t → emb idn w t v b) (λ i → p i w a)
        ∙ sym (interchange g idn w a v b)
        ∙ ap (emb g w a v) (absorb-l b))

  noy-inj
    : ∀ {x y} {f g : hom x y}
    → noy f ≡ noy g → f ≡ g
  noy-inj {f = f} {g} p = emb-inj
    (emb-ext λ w a v b →
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

### Identity uniqueness

Any morphism satisfying the unit axioms equals `idn`. The
right equiv factors as `(yon e w)²` via interchange and
absorption. Since `yon e w` is idempotent (from yon-composite
and the yon-idempotency axiom), left-cancelling by the right
equiv gives `yon e w g ≡ g` for all `g`, hence `e ≡ idn`
via `yon-eval`.

```agda
  unit-is-prop
    : ∀ {x} (e : hom x x)
    → (∀ {z} → is-equiv (λ (h : hom x z) → emb e x e z h))
    → (∀ {w} → is-equiv (λ (g : hom w x) → emb e w g x e))
    → yon e x e ≡ e
    → e ≡ idn
  unit-is-prop {x} e le re idpt =
    sym (yon-eval e) ∙ yon-e-absorb idn
    where
      e-idem : e ⨾ e ≡ e
      e-idem = comp-eq e e ∙ idpt

      yon-e-idpt : ∀ w (g : hom w x)
        → yon e w (yon e w g) ≡ yon e w g
      yon-e-idpt w g =
        sym (sym (ap (λ t → yon t w g) e-idem)
          ∙ yon-composite e e w g)

      -- emb e w g x e ≡ (yon e w)²(g) via emb-yon + interchange
      yon-e-squared : ∀ {w} (g : hom w x)
        → emb e w g x e ≡ yon e w (yon e w g)
      yon-e-squared {w} g =
        emb-yon e w g x e
        ∙ sym (ap (emb idn w (yon e w g) x) (yon-eval e))
        ∙ interchange idn e w (yon e w g) x idn
        ∙ ap (yon e w) (absorb-r (yon e w g))

      yon-e-absorb : ∀ {w} (g : hom w x) → yon e w g ≡ g
      yon-e-absorb {w} g = equiv→lc re
        (yon-e-squared (yon e w g)
        ∙ yon-e-idpt w (yon e w g)
        ∙ sym (yon-e-squared g))
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
          ∙ emb-ext λ w a v b →
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
      rhs = f , emb-ext λ w a v b →
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
    ∙ emb-ext λ w a v b →
        emb-composite-pt f g w a v (noy h v b)
  E₃-contr f g h .paths =
    is-contr→is-prop
      (subst (is-contr ∘ fiber emb) path
        (composable-contr (f ⨾ g) h)) _
    where
      path : (λ w a v b →
                emb (f ⨾ g) w a v (noy h v b))
            ≡ E₃ f g h
      path = emb-ext λ w a v b →
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
          ∙ emb-ext λ w a v b →
              ap (emb f w a v)
                (noy-composite g h b)
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
    , C.unit .snd .snd
  op .category.compose-contr f g =
    C.composable-swap (C.composable-yon g f)
  op .category.interchange f g w a v b =
    sym (C.interchange g f v b w a)
  op .category.yon-eval f = C.yon-eval f
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
  op-invol i .category.yon-eval f = C.yon-eval f
```
