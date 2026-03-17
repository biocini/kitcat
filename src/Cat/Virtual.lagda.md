Lane Biocini
March 2026

Virtual categories. Composition is gated by a propositional
classifier on composable pairs. The `compose-classified`
field gives a contractible `fiber emb target` when the
classifier holds. Interchange equates the noy and yon views
for classified pairs. The combinator `⟨ f , g , c ⟩` is
derived as the noy-side target.

Cat.Type.category is the special case where every pair
composes (classifier is trivially ⊤).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Virtual where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding using (equiv→lc)
open import Core.HLevel.Base using (⊤-is-prop)
import Cat.Type as T
```

## The virtual-category record

```agda
record virtual-category o h p : Type₊ (o ⊔ h ⊔ p) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    emb : ∀ {x y} → hom x y
        → ∀ w → hom w x → ∀ v → hom y v → hom w v
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
    yon-eval : ∀ {x y} (f : hom x y) → yon f x idn ≡ f

    classifier : ∀ {x y z} → hom x y → hom y z → Type p
    classifier-prop
      : ∀ {x y z} {f : hom x y} {g : hom y z}
      → is-prop (classifier f g)

    compose-classified
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → classifier f g
      → is-contr
          (fiber (emb {x} {z})
            (λ w a v b → emb f w a v (noy g v b)))

    interchange-classified
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → classifier f g
      → ∀ w (a : hom w x) v (b : hom z v)
      → emb f w a v (noy g v b)
      ≡ emb g w (yon f w a) v b

    classifier-idn-l
      : ∀ {x y} (f : hom x y) → classifier idn f
    classifier-idn-r
      : ∀ {x y} (f : hom x y) → classifier f idn

  yon-idpt : ∀ {x} → yon (idn {x}) x idn ≡ idn
  yon-idpt = yon-eval idn

  comp : ∀ {x y z} (f : hom x y) (g : hom y z)
    → classifier f g → hom x z
  comp f g c = compose-classified f g c .center .fst

  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → (c : classifier f g)
    → emb (comp f g c)
    ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite f g c =
    compose-classified f g c .center .snd

  emb-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → (c : classifier f g)
    → ∀ w (a : hom w x) v (b : hom z v)
    → emb (comp f g c) w a v b
    ≡ emb f w a v (noy g v b)
  emb-composite-pt f g c w a v b i =
    emb-composite f g c i w a v b

  field
    classifier-assoc
      : ∀ {x y z w}
        {f : hom x y} {g : hom y z} {h : hom z w}
      → (cfg : classifier f g) → (cgh : classifier g h)
      → classifier (comp f g cfg) h
      × classifier f (comp g h cgh)

{-# INLINE virtual-category.constructor #-}
```

## Derived operations

The combinator `⟨ f , g , c ⟩` is derived as the noy-side
composition target. Both combinator-at-identity laws follow
from absorb, which is derived from the standard chain:
yon-composite → comp-eq → idem → absorb via left cancellation.

```agda
module Classified
  {o h p} (C : virtual-category o h p) where
  open virtual-category C public

  ⟨_,_,_⟩ : ∀ {x y z} (f : hom x y) (g : hom y z)
    → classifier f g
    → ∀ w → hom w x → ∀ v → hom z v → hom w v
  ⟨ f , g , c ⟩ w a v b = emb f w a v (noy g v b)

  emb-ext
    : ∀ {x y}
      {F G : ∀ w → hom w x → ∀ v → hom y v → hom w v}
    → (∀ w (a : hom w x) v (b : hom y v)
        → F w a v b ≡ G w a v b)
    → F ≡ G
  emb-ext h =
    funext λ w → funext λ a → funext λ v → funext λ b →
      h w a v b

  private
    idn-class : ∀ {x} → classifier (idn {x}) idn
    idn-class = classifier-idn-l idn

    noy-composite-idn
      : ∀ {x} {v : ob} (b : hom x v)
      → noy (comp idn idn idn-class) v b
      ≡ noy idn v (noy idn v b)
    noy-composite-idn {x} b =
      emb-composite-pt idn idn idn-class x idn _ b

    yon-composite-idn
      : ∀ {x} {w : ob} (a : hom w x)
      → yon (comp idn idn idn-class) w a
      ≡ yon idn w (yon idn w a)
    yon-composite-idn {x} {w} a =
      emb-composite-pt idn idn idn-class w a x idn
      ∙ interchange-classified idn idn
          idn-class w a x idn

    comp-eq-idn
      : ∀ {x}
      → comp (idn {x}) idn idn-class ≡ yon idn x idn
    comp-eq-idn =
      sym (yon-eval (comp idn idn idn-class))
      ∙ yon-composite-idn idn
      ∙ ap (yon idn _) (yon-eval idn)

    idem : ∀ {x} → comp (idn {x}) idn idn-class ≡ idn
    idem = comp-eq-idn ∙ yon-idpt

  absorb-l : ∀ {x} {v : ob} (h : hom x v)
    → noy idn v h ≡ h
  absorb-l {x} h = equiv→lc unit-eqvl noy-idn-idpt
    where
      noy-idn-idpt
        : noy idn _ (noy idn _ h) ≡ noy idn _ h
      noy-idn-idpt =
        sym (subst
          (λ t → noy t _ h
            ≡ noy idn _ (noy idn _ h))
          (idem {x}) (noy-composite-idn h))

  absorb-r : ∀ {x} {w : ob} (g : hom w x)
    → yon idn w g ≡ g
  absorb-r {x} g = equiv→lc unit-eqvr yon-idn-idpt
    where
      yon-idn-idpt
        : yon idn _ (yon idn _ g) ≡ yon idn _ g
      yon-idn-idpt =
        sym (subst
          (λ t → yon t _ g
            ≡ yon idn _ (yon idn _ g))
          (idem {x}) (yon-composite-idn g))

  combinator-idn-l
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → ⟨ idn , f , classifier-idn-l f ⟩ w a v b
    ≡ emb f w a v b
  combinator-idn-l f w a v b =
    interchange-classified idn f
      (classifier-idn-l f) w a v b
    ∙ ap (λ t → emb f w t v b) (absorb-r a)

  combinator-idn-r
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → ⟨ f , idn , classifier-idn-r f ⟩ w a v b
    ≡ emb f w a v b
  combinator-idn-r f w a v b =
    ap (emb f w a v) (absorb-l b)
```

### Composable fiber and its eliminators

`composable-contr` restates `compose-classified` with a
pointwise equation. `emb-ind` eliminates any `(s, q)` in
the fiber back to the canonical center.

```agda
  composable-contr
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → (c : classifier f g)
    → is-contr
        (Σ s ∶ hom x z
        , ∀ w (a : hom w x) v (b : hom z v)
          → emb s w a v b
          ≡ emb f w a v (noy g v b))
  composable-contr f g c .center =
    comp f g c , emb-composite-pt f g c
  composable-contr f g c .paths (s , p) i =
    let ep = compose-classified f g c .paths
              (s , emb-ext p)
    in ep i .fst
     , λ w a v b j → ep i .snd j w a v b

  emb-ind
    : ∀ {u} {x y z} (f : hom x y) (g : hom y z)
      (c : classifier f g)
    → (P : (s : hom x z)
         → (∀ w (a : hom w x) v (b : hom z v)
             → emb s w a v b
             ≡ emb f w a v (noy g v b))
         → Type u)
    → P (comp f g c) (emb-composite-pt f g c)
    → ∀ s q → P s q
  emb-ind f g c P base s q =
    contr-ind (composable-contr f g c)
      (λ where (s , q) → P s q)
      base (s , q)
```

### Injectivity and decomposition

`emb-noy` and `emb-yon` express `emb f` in terms of `noy`
and `yon` with the identity. `emb-image-contr` shows the
emb-fiber is contractible. `emb-inj` derives injectivity
of `emb`.

```agda
  emb-noy
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w a v (noy f v b)
  emb-noy f w a v b =
    ap (λ t → emb f w t v b) (sym (absorb-r a))
    ∙ sym (interchange-classified idn f
        (classifier-idn-l f) w a v b)

  emb-yon
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w (yon f w a) v b
  emb-yon f w a v b =
    ap (emb f w a v) (sym (absorb-l b))
    ∙ interchange-classified f idn
        (classifier-idn-r f) w a v b

  emb-image-contr
    : ∀ {x y} (f : hom x y)
    → is-contr
        (Σ s ∶ hom x y
        , ∀ w (a : hom w x) v (b : hom y v)
          → emb s w a v b ≡ emb f w a v b)
  emb-image-contr {x} {y} f = c' where
    c : is-contr
      (Σ s ∶ hom x y
      , ∀ w (a : hom w x) v (b : hom y v)
        → emb s w a v b
        ≡ emb idn w a v (noy f v b))
    c = composable-contr idn f (classifier-idn-l f)

    path
      : (λ w (a : hom w x) v (b : hom y v)
          → emb idn w a v (noy f v b))
      ≡ (λ w (a : hom w x) v (b : hom y v)
          → emb f w a v b)
    path = emb-ext λ w a v b →
      combinator-idn-l f w a v b

    c' : is-contr
      (Σ s ∶ hom _ _
      , ∀ w a v b
        → emb s w a v b ≡ emb f w a v b)
    c' = subst (λ T → is-contr
      (Σ s ∶ hom _ _
      , ∀ w a v b
        → emb s w a v b ≡ T w a v b))
      path c

  emb-inj
    : ∀ {x y} {f g : hom x y}
    → (∀ w (a : hom w x) v (b : hom y v)
        → emb f w a v b ≡ emb g w a v b)
    → f ≡ g
  emb-inj {f = f} {g} pw =
    ap fst (sym p₁ ∙ p₂) where
    p₁ = emb-image-contr f .paths
      (f , λ _ _ _ _ → refl)
    p₂ = emb-image-contr f .paths
      (g , λ w a v b → sym (pw w a v b))
```

### Composite characterizations

`noy-composite` and `yon-composite` specialize the
composite characterization to the noy and yon views.

```agda
  emb-composite-ext
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → (c : classifier f g)
    → emb (comp f g c)
    ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite-ext f g c = emb-composite f g c

  noy-composite
    : ∀ {x y z} (g : hom x y) (h : hom y z)
      (c : classifier g h)
      {v : ob} (b : hom z v)
    → noy (comp g h c) v b ≡ noy g v (noy h v b)
  noy-composite g h c b =
    emb-composite-pt g h c _ idn _ b

  yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      (c : classifier f g)
      w (a : hom w x)
    → yon (comp f g c) w a ≡ yon g w (yon f w a)
  yon-composite f g c w a =
    emb-composite-pt f g c w a _ idn
    ∙ interchange-classified f g c w a _ idn

  comp-eq
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → (c : classifier f g)
    → comp f g c ≡ yon g _ f
  comp-eq f g c =
    sym (yon-eval (comp f g c))
    ∙ yon-composite f g c _ idn
    ∙ ap (yon g _) (yon-eval f)
```

### Unit laws and associativity

The unit laws are projections from contractible fibers.
`unitr` uses `emb-image-contr`, `unitl` uses
`composable-contr`.

```agda
  unitr
    : ∀ {x y} (f : hom x y)
    → comp f idn (classifier-idn-r f) ≡ f
  unitr f =
    ap fst
      (is-contr→is-prop (emb-image-contr f)
        lhs rhs)
    where
      lhs : Σ s ∶ hom _ _
          , ∀ w a v b
            → emb s w a v b ≡ emb f w a v b
      lhs = comp f idn (classifier-idn-r f)
          , λ w a v b →
              emb-composite-pt f idn
                (classifier-idn-r f) w a v b
              ∙ ap (emb f w a v) (absorb-l b)

      rhs : Σ s ∶ hom _ _
          , ∀ w a v b
            → emb s w a v b ≡ emb f w a v b
      rhs = f , λ _ _ _ _ → refl

  unitl
    : ∀ {x y} (f : hom x y)
    → comp idn f (classifier-idn-l f) ≡ f
  unitl f =
    ap fst
      (is-contr→is-prop
        (composable-contr idn f (classifier-idn-l f))
        lhs rhs)
    where
      lhs : Σ s ∶ hom _ _
          , ∀ w a v b
            → emb s w a v b
            ≡ emb idn w a v (noy f v b)
      lhs = comp idn f (classifier-idn-l f)
          , emb-composite-pt idn f
              (classifier-idn-l f)

      rhs : Σ s ∶ hom _ _
          , ∀ w a v b
            → emb s w a v b
            ≡ emb idn w a v (noy f v b)
      rhs = f , emb-noy f
```

The ternary fiber `E₃` is the common target for both
association directions. Its contractibility follows from
`composable-contr` transported along the expansion of
`emb (comp f g cfg)`.

```agda
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
      (cfg : classifier f g) (cgh : classifier g h)
    → is-contr
        (Σ s ∶ hom x w
        , ∀ w' (a : hom w' x) v (b : hom w v)
          → emb s w' a v b
          ≡ E₃ f g h w' a v b)
  E₃-contr f g h cfg cgh .center .fst =
    comp (comp f g cfg) h
      (classifier-assoc cfg cgh .fst)
  E₃-contr f g h cfg cgh .center .snd w' a v b =
    emb-composite-pt (comp f g cfg) h
      (classifier-assoc cfg cgh .fst) w' a v b
    ∙ emb-composite-pt f g cfg w' a v (noy h v b)
  E₃-contr f g h cfg cgh .paths =
    is-contr→is-prop
      (subst (λ T → is-contr
        (Σ s ∶ hom _ _
        , ∀ w' a v b
          → emb s w' a v b ≡ T w' a v b))
        path
        (composable-contr (comp f g cfg) h
          (classifier-assoc cfg cgh .fst))) _
    where
      path
        : (λ w' a v b →
            emb (comp f g cfg) w' a v (noy h v b))
        ≡ E₃ f g h
      path = funext λ w' → funext λ a →
        funext λ v → funext λ b →
          emb-composite-pt f g cfg
            w' a v (noy h v b)

  assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
      (cfg : classifier f g) (cgh : classifier g h)
    → comp (comp f g cfg) h
        (classifier-assoc cfg cgh .fst)
    ≡ comp f (comp g h cgh)
        (classifier-assoc cfg cgh .snd)
  assoc f g h cfg cgh =
    ap fst
      (is-contr→is-prop (E₃-contr f g h cfg cgh)
        (E₃-contr f g h cfg cgh .center) rhs)
    where
      rhs : Σ s ∶ hom _ _
          , ∀ w' a v b
            → emb s w' a v b
            ≡ E₃ f g h w' a v b
      rhs = comp f (comp g h cgh)
              (classifier-assoc cfg cgh .snd)
          , λ w' a v b →
              emb-composite-pt f (comp g h cgh)
                (classifier-assoc cfg cgh .snd)
                w' a v b
              ∙ ap (emb f w' a v)
                  (noy-composite g h cgh b)
```

## From Cat.Type

Every `T.category` gives a virtual-category whose classifier
is `⊤` — every pair composes.

```agda
module _ {o h} (C : T.category o h) where
  private module C = T.Virtual C

  from-category : virtual-category o h 0ℓ
  from-category .virtual-category.ob = C.ob
  from-category .virtual-category.hom = C.hom
  from-category .virtual-category.emb = C.emb
  from-category .virtual-category.unit = C.unit
  from-category .virtual-category.yon-eval = C.yon-eval
  from-category .virtual-category.classifier _ _ = ⊤
  from-category .virtual-category.classifier-prop =
    ⊤-is-prop
  from-category .virtual-category.compose-classified
    f g _ = C.compose-contr f g
  from-category .virtual-category.interchange-classified
    f g _ = C.interchange f g
  from-category .virtual-category.classifier-idn-l _ = tt
  from-category .virtual-category.classifier-idn-r _ = tt
  from-category .virtual-category.classifier-assoc _ _ =
    tt , tt
```

## To Cat.Type

A virtual-category with a total classifier (every pair is
classified) gives a `T.category`: composition and interchange
are available unconditionally.

```agda
module _ {o h p} (C : virtual-category o h p) where
  private module C' = Classified C

  to-category
    : (total : ∀ {x y z} (f : C'.hom x y)
        (g : C'.hom y z) → C'.classifier f g)
    → T.category o h
  to-category total .T.category.ob = C'.ob
  to-category total .T.category.hom = C'.hom
  to-category total .T.category.emb = C'.emb
  to-category total .T.category.unit = C'.unit
  to-category total .T.category.compose-contr f g =
    C'.compose-classified f g (total f g)
  to-category total .T.category.interchange f g =
    C'.interchange-classified f g (total f g)
  to-category total .T.category.yon-eval = C'.yon-eval
```

### Round-trip

Applying `to-category` to `from-category V` with the trivial
witness recovers `V`. Each field is definitionally equal, so
the path is constant.

```agda
module _ {o h} (V : T.category o h) where
  private module C = T.Virtual V

  to-category-from-category
    : to-category (from-category V) (λ _ _ → tt) ≡ V
  to-category-from-category i .T.category.ob = C.ob
  to-category-from-category i .T.category.hom = C.hom
  to-category-from-category i .T.category.emb = C.emb
  to-category-from-category i .T.category.unit = C.unit
  to-category-from-category i .T.category.compose-contr =
    C.compose-contr
  to-category-from-category i .T.category.interchange =
    C.interchange
  to-category-from-category i .T.category.yon-eval =
    C.yon-eval
```

### Set-valued classifiers

A set-valued classifier (h-level 2) would break interchange.
With `is-set (classifier f g)`, distinct witnesses `c₁ c₂`
could yield different composites via `compose-classified`,
making the interchange equation depend on which witness is
chosen. But `interchange` in `T.category` quantifies
uniformly over all contexts — it cannot vary with the
classifier value. Propositionally, `c₁ ≡ c₂` forces the
composite to be unique regardless of witness, which is
exactly what `classifier-prop` guarantees.
