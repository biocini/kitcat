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
open import Core.Groupoid.Virtual
open import Core.Equiv.Base using (is-equiv; eqv-fibers; Equiv)
open import Core.Function.Embedding
  using (equiv→lc; is-embedding; is-embedding→ap-equiv)
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
      , (∀ {z} → is-equiv (λ (h : hom x z) → emb e x e z h))
      × (∀ {w} → is-equiv (λ (g : hom w x) → emb e w g x e))

  idn : ∀ {x} → hom x x
  idn = unit .fst

  noy : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  noy f z h = emb f _ idn z h

  yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  yon f w g = emb f w g _ idn

  unit-eqvl : ∀ {x} {z : ob}
    → is-equiv (λ (h : hom x z) → noy idn z h)
  unit-eqvl = unit .snd .fst

  unit-eqvr : ∀ {x} {w : ob}
    → is-equiv (λ (g : hom w x) → yon idn w g)
  unit-eqvr = unit .snd .snd

  field
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr
          (Σ s ∶ hom x z
          , ∀ w (a : hom w x) v (b : hom z v)
            → emb s w a v b
            ≡ emb f w a v (noy g v b))

    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        w (a : hom w x) v (b : hom z v)
      → emb f w a v (noy g v b)
      ≡ emb g w (yon f w a) v b

    yon-eval
      : ∀ {x y} (f : hom x y) → yon f x idn ≡ f

  yon-idpt : ∀ {x} → yon (idn {x}) x idn ≡ idn
  yon-idpt = yon-eval idn

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst
  infixr 40 _⨾_

  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb f w a v (noy g v b)
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

  emb-composite-ext
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite-ext f g =
    emb-ext (emb-composite f g)

  emb-yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb g w (yon f w a) v b)
  emb-yon-composite f g =
    emb-composite-ext f g
    ∙ emb-ext λ w a v b → interchange f g w a v b

  emb-yon-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb g w (yon f w a) v b
  emb-yon-composite-pt f g w a v b =
    emb-composite f g w a v b
    ∙ interchange f g w a v b

  noy-composite
    : ∀ {x y z} (g : hom x y) (h : hom y z)
      {v : ob} (b : hom z v)
    → noy (g ⨾ h) v b ≡ noy g v (noy h v b)
  noy-composite g h {v} b =
    emb-composite g h _ idn v b

  yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x)
    → yon (f ⨾ g) w a ≡ yon g w (yon f w a)
  yon-composite f g w a =
    emb-composite f g w a _ idn
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
        (Σ s ∶ hom x z
        , ∀ w (a : hom w x) v (b : hom z v)
          → emb s w a v b
          ≡ emb f w a v (noy g v b))
  composable-contr f g .center =
    f ⨾ g , emb-composite f g
  composable-contr f g .paths (s , p) =
    compose-contr f g .paths (s , p)

  emb-ind
    : ∀ {u} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z)
         → (∀ w (a : hom w x) v (b : hom z v)
             → emb s w a v b
             ≡ emb f w a v (noy g v b))
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
    → (∀ w (a : hom w x) v (b : hom z v)
        → emb s w a v b
        ≡ emb f w a v (noy g v b))
    → f ⨾ g ≡ s
  ⨾-η f g = emb-ind f g (λ s _ → f ⨾ g ≡ s) refl
```

### Embedding property

`composable-contr idn f` gives a contractible pointwise fiber
over the noy-target. By interchange and right absorption, the
target equals `emb f`, so `emb` is injective: pointwise
equality `∀ w a v b → emb f w a v b ≡ emb g w a v b` implies
`f ≡ g`. The function-extensional variant `emb-inj-ext` wraps
this via `happly`. `emb-image-contr-ext` converts to the
`fiber emb (emb f)` form for the embedding property.

```agda
  emb-image-contr
    : ∀ {x y} (f : hom x y)
    → is-contr
        (Σ s ∶ hom x y
        , ∀ w (a : hom w x) v (b : hom y v)
          → emb s w a v b ≡ emb f w a v b)
  emb-image-contr {x} {y} f = c'
    where
      c : is-contr
        (Σ s ∶ hom x y
        , ∀ w (a : hom w x) v (b : hom y v)
          → emb s w a v b
          ≡ emb idn w a v (noy f v b))
      c = composable-contr idn f

      path
        : (λ w (a : hom w x) v (b : hom y v)
            → emb idn w a v (noy f v b))
        ≡ (λ w (a : hom w x) v (b : hom y v)
            → emb f w a v b)
      path = funext λ w → funext λ a →
        funext λ v → funext λ b →
          interchange idn f w a v b
          ∙ ap (λ t → emb f w t v b) (absorb-r a)

      c' : is-contr
        (Σ s ∶ hom _ _
        , ∀ w a v b → emb s w a v b ≡ emb f w a v b)
      c' = subst (λ T → is-contr
        (Σ s ∶ hom _ _
        , ∀ w a v b → emb s w a v b ≡ T w a v b))
        path c

  emb-image-contr-ext
    : ∀ {x y} (f : hom x y)
    → is-contr (fiber emb (emb f))
  emb-image-contr-ext {x} {y} f = c'
    where
      PW = Σ s ∶ hom x y
         , ∀ w (a : hom w x) v (b : hom y v)
           → emb s w a v b ≡ emb f w a v b

      to-ext : PW → fiber emb (emb f)
      to-ext (s , q) = s , emb-ext q

      c = emb-image-contr f

      c' : is-contr (fiber emb (emb f))
      c' .center = to-ext (c .center)
      c' .paths (s , p) =
        ap to-ext
          (c .paths
            (s , λ w a v b i → p i w a v b))

  emb-inj
    : ∀ {x y} {f g : hom x y}
    → (∀ w (a : hom w x) v (b : hom y v)
        → emb f w a v b ≡ emb g w a v b)
    → f ≡ g
  emb-inj {f = f} {g} pw =
    ap fst (sym p₁ ∙ p₂)
    where
      p₁ = emb-image-contr f .paths
        (f , λ _ _ _ _ → refl)
      p₂ = emb-image-contr f .paths
        (g , λ w a v b → sym (pw w a v b))

  emb-inj-ext
    : ∀ {x y} {f g : hom x y}
    → emb f ≡ emb g → f ≡ g
  emb-inj-ext {f = f} {g} p =
    emb-inj λ w a v b i → p i w a v b

  emb-is-embedding
    : ∀ {x y} → is-embedding (emb {x} {y})
  emb-is-embedding t (f , p) (g , q) =
    is-contr→is-prop
      (subst (is-contr ∘ fiber emb) p
        (emb-image-contr-ext f))
      (f , p) (g , q)

  emb-section
    : ∀ {x y} {f g : hom x y}
    → (p : f ≡ g) → emb-inj-ext (ap emb p) ≡ p
  emb-section {f = f} =
    J (λ g p → emb-inj-ext (ap emb p) ≡ p) emb-inj-ext-refl
    where
      pw-center = emb-image-contr f .paths
        (f , λ _ _ _ _ → refl)

      loop
        : Path (Σ s ∶ hom _ _
              , ∀ w a v b → emb s w a v b ≡ emb f w a v b)
            (f , λ _ _ _ _ → refl)
            (f , λ _ _ _ _ → refl)
      loop = sym pw-center ∙ pw-center

      loop≡refl : loop ≡ refl
      loop≡refl =
        is-contr→is-set (emb-image-contr f) _ _ loop refl

      emb-inj-ext-refl : emb-inj-ext {f = f} refl ≡ refl
      emb-inj-ext-refl =
        ap (ap fst) loop≡refl

  emb-retraction
    : ∀ {x y} {f g : hom x y}
    → (q : emb f ≡ emb g) → ap emb (emb-inj-ext q) ≡ q
  emb-retraction {f = f} {g} q =
    ap (ap emb) emb-inj-ext≡inv ∙ counit q
    where
      ap-emb-equiv : is-equiv (ap emb {x = f} {y = g})
      ap-emb-equiv = is-embedding→ap-equiv emb-is-embedding

      module E = Equiv (ap emb , ap-emb-equiv)

      counit : (q : emb f ≡ emb g) → ap emb (E.inv q) ≡ q
      counit = E.counit

      emb-inj-ext≡inv : emb-inj-ext q ≡ E.inv q
      emb-inj-ext≡inv =
        ap emb-inj-ext (sym (counit q))
        ∙ emb-section (E.inv q)
```

### Yon-characterized composite and its eliminator

Interchange swaps `noy` for `yon` in the composite target,
giving a dual fiber with the same center. `emb-yon-ind`
eliminates over this alternative characterization.

```agda
  composable-contr-ext
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr
        (fiber (emb {x} {z})
          (λ w a v b → emb f w a v (noy g v b)))
  composable-contr-ext {x} {z} f g = c'
    where
      target = λ w a v b → emb f w a v (noy g v b)

      PW = Σ s ∶ hom x z
         , ∀ w (a : hom w x) v (b : hom z v)
           → emb s w a v b ≡ target w a v b

      to-ext : PW → fiber emb target
      to-ext (s , q) = s , emb-ext q

      c = composable-contr f g

      c' : is-contr (fiber emb target)
      c' .center = to-ext (c .center)
      c' .paths (s , p) =
        ap to-ext
          (c .paths
            (s , λ w a v b i → p i w a v b))

  composable-yon
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr
        (fiber emb
          (λ w a v b → emb g w (yon f w a) v b))
  composable-yon f g =
    subst (is-contr ∘ fiber emb) path
      (composable-contr-ext f g)
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
        (Σ s ∶ hom x y
        , ∀ w (a : hom y w) v (b : hom v x)
          → emb s v b w a ≡ target v b w a)
  composable-swap c .center .fst =
    c .center .fst
  composable-swap c .center .snd w a v b i =
    c .center .snd i v b w a
  composable-swap {target = target}
    c .paths (s' , q') i .fst =
    c .paths (s' , q'') i .fst
    where
      q'' : emb s' ≡ target
      q'' i w a v b = q' v b w a i
  composable-swap {target = target}
    c .paths (s' , q') i .snd w a v b j =
    c .paths (s' , q'') i .snd j v b w a
    where
      q'' : emb s' ≡ target
      q'' i w a v b = q' v b w a i
```

### Injectivity and decomposition

Both `yon` and `noy` are injective, following from interchange
and `emb-inj`. The `emb-yon` and `emb-noy` lemmas express
`emb f` in terms of `yon` and `noy`.

```agda
  yon-inj
    : ∀ {x y} {f g : hom x y}
    → yon f ≡ yon g → f ≡ g
  yon-inj {f = f} {g} p = emb-inj λ w a v b →
    ap (emb f w a v) (sym (absorb-l b))
    ∙ interchange f idn w a v b
    ∙ ap (λ t → emb idn w t v b) (λ i → p i w a)
    ∙ sym (interchange g idn w a v b)
    ∙ ap (emb g w a v) (absorb-l b)

  noy-inj
    : ∀ {x y} {f g : hom x y}
    → noy f ≡ noy g → f ≡ g
  noy-inj {f = f} {g} p = emb-inj λ w a v b →
    ap (λ t → emb f w t v b) (sym (absorb-r a))
    ∙ sym (interchange idn f w a v b)
    ∙ ap (λ t → emb idn w a v t) (λ i → p i v b)
    ∙ interchange idn g w a v b
    ∙ ap (λ t → emb g w t v b) (absorb-r a)

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
      lhs : Σ s ∶ hom _ _
          , ∀ w a v b → emb s w a v b ≡ emb f w a v b
      lhs = f ⨾ idn
          , λ w a v b →
              emb-composite f idn w a v b
              ∙ ap (emb f w a v) (absorb-l b)

      rhs : Σ s ∶ hom _ _
          , ∀ w a v b → emb s w a v b ≡ emb f w a v b
      rhs = f , λ _ _ _ _ → refl

  unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  unitl f =
    ap fst
      (is-contr→is-prop (composable-contr idn f)
        lhs rhs)
    where
      lhs : Σ s ∶ hom _ _
          , ∀ w a v b
            → emb s w a v b
            ≡ emb idn w a v (noy f v b)
      lhs = idn ⨾ f , emb-composite idn f

      rhs : Σ s ∶ hom _ _
          , ∀ w a v b
            → emb s w a v b
            ≡ emb idn w a v (noy f v b)
      rhs = f , emb-noy f

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
    → is-contr
        (Σ s ∶ hom x w
        , ∀ w' (a : hom w' x) v (b : hom w v)
          → emb s w' a v b ≡ E₃ f g h w' a v b)
  E₃-contr f g h .center .fst = (f ⨾ g) ⨾ h
  E₃-contr f g h .center .snd w' a v b =
    emb-composite (f ⨾ g) h w' a v b
    ∙ emb-composite f g w' a v (noy h v b)
  E₃-contr f g h .paths =
    is-contr→is-prop
      (subst (λ T → is-contr
        (Σ s ∶ hom _ _
        , ∀ w' a v b → emb s w' a v b ≡ T w' a v b))
        path
        (composable-contr (f ⨾ g) h)) _
    where
      path
        : (λ w' a v b →
            emb (f ⨾ g) w' a v (noy h v b))
        ≡ E₃ f g h
      path = funext λ w' → funext λ a →
        funext λ v → funext λ b →
          emb-composite f g w' a v (noy h v b)

  E₃-contr-ext
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → is-contr (fiber emb (E₃ f g h))
  E₃-contr-ext {x} {w = w} f g h = c'
    where
      PW = Σ s ∶ hom x w
         , ∀ w' (a : hom w' x) v (b : hom w v)
           → emb s w' a v b ≡ E₃ f g h w' a v b

      to-ext : PW → fiber emb (E₃ f g h)
      to-ext (s , q) = s , emb-ext q

      c = E₃-contr f g h

      c' : is-contr (fiber emb (E₃ f g h))
      c' .center = to-ext (c .center)
      c' .paths (s , p) =
        ap to-ext
          (c .paths
            (s , λ w' a v b i → p i w' a v b))

  E₃-ind
    : ∀ {u} {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (P : (s : hom x w)
         → emb s ≡ E₃ f g h
         → Type u)
    → P (E₃-contr-ext f g h .center .fst)
        (E₃-contr-ext f g h .center .snd)
    → ∀ s q → P s q
  E₃-ind f g h P base s q =
    contr-ind (E₃-contr-ext f g h)
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
      rhs : Σ s ∶ hom _ _
          , ∀ w' a v b
            → emb s w' a v b ≡ E₃ f g h w' a v b
      rhs = f ⨾ (g ⨾ h)
          , λ w' a v b →
              emb-composite f (g ⨾ h) w' a v b
              ∙ ap (emb f w' a v)
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
    , C.unit .snd .snd
    , C.unit .snd .fst
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
        , ∀ w (a : C.hom w x) v (b : C.hom z v)
          → C.emb s w a v b
          ≡ C.emb f w a v (C.noy g v b))}
      (λ _ → is-contr-is-prop _)
      (category.compose-contr (op (op C)) f g)
      (C.compose-contr f g) i
  op-invol i .category.interchange f g w a v b =
    C.interchange f g w a v b
  op-invol i .category.yon-eval f = C.yon-eval f
```
