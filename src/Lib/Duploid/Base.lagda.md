Lane Biocini
March 2026

Duploids as virtual categories with polarized composition.
A duploid has unconditional interchange but composition is
gated by `is-thunkable f ⋆ is-linear g`. Object polarity
(every object is positive or negative) subsumes the virtual
category classifier axioms.

Attribution: Sterling (TypeTopology/source/Duploids/),
Munch-Maccagnoni (FoSSaCS 2014).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Duploid.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport using (contr-ind)
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding using (equiv→lc)
open import Core.HLevel.Base using (Π-is-prop)
open import Core.Transport.Properties
  using (is-contr-is-prop)

open import HData.Join.Type using (_⋆_; inl; inr; push)
open import HData.Join.Base using (rec)
open import HData.Join.Properties using (Join-is-prop)

import Cat.Virtual as V
```


## The duploid record

Binary composition `f ⨾ g = yon g _ f` is always defined but
not always associative. The classifier `is-thunkable f ⋆
is-linear g` gates when the emb-fiber is contractible (giving
associativity). The `is-thunkable`/`is-linear` quantifiers use
explicit object arguments to avoid implicit-visibility mismatch
when `is-positive`/`is-negative` re-quantify with `∀ {B}`.

```agda
record duploid o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    emb : ∀ {x y} → hom x y
        → ∀ w → hom w x → ∀ v → hom y v → hom w v
    unit : ∀ {x} →
      Σ e ∶ hom x x
      , (∀ {z} →
          is-equiv (λ (h : hom x z) → emb e x e z h))
      × (∀ {w} →
          is-equiv (λ (g : hom w x) → emb e w g x e))

  idn : ∀ {x} → hom x x
  idn = unit .fst

  noy : ∀ {x y} → hom x y
    → ∀ z → hom y z → hom x z
  noy f z h = emb f _ idn z h

  yon : ∀ {x y} → hom x y
    → ∀ w → hom w x → hom w y
  yon f w g = emb f w g _ idn

  unit-eqvl : ∀ {x} {z : ob}
    → is-equiv (λ (h : hom x z) → noy idn z h)
  unit-eqvl = unit .snd .fst

  unit-eqvr : ∀ {x} {w : ob}
    → is-equiv (λ (g : hom w x) → yon idn w g)
  unit-eqvr = unit .snd .snd

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = yon g _ f
  infixr 40 _⨾_

  composable : ∀ {x y z} → hom x y → hom y z
    → Type _
  composable {z = z} f g =
    is-contr
      (fiber (emb {_} {z})
        (λ w a v b → emb f w a v (noy g v b)))

  is-thunkable : ∀ {x y} → hom x y → Type _
  is-thunkable {x} {y} f =
    ∀ z (g : hom y z) → composable f g

  is-linear : ∀ {x y} → hom x y → Type _
  is-linear {x} {y} g =
    ∀ w (f : hom w x) → composable f g

  is-positive : ob → Type _
  is-positive A =
    ∀ {B} (f : hom A B) → is-linear f

  is-negative : ob → Type _
  is-negative A =
    ∀ {B} (f : hom B A) → is-thunkable f

  classifier : ∀ {x y z} → hom x y → hom y z
    → Type _
  classifier f g = is-thunkable f ⋆ is-linear g

  field
    yon-eval : ∀ {x y} (f : hom x y) → yon f x idn ≡ f

    interchange : ∀ {x y z} (f : hom x y) (g : hom y z)
      → ∀ w (a : hom w x) v (b : hom z v)
      → emb f w a v (noy g v b)
      ≡ emb g w (yon f w a) v b

    compose-classified : ∀ {x y z}
      (f : hom x y) (g : hom y z)
      → classifier f g
      → is-contr
          (fiber (emb {x} {z})
            (λ w a v b → emb f w a v (noy g v b)))

    polarity : ∀ A → is-positive A ⋆ is-negative A

{-# INLINE duploid.constructor #-}
```


## Derived operations

```agda
module Duploid {o h} (D : duploid o h) where
  open duploid D public
```


### Composite and emb-composite

```agda
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

  emb-ext
    : ∀ {x y}
      {F G : ∀ w → hom w x → ∀ v → hom y v → hom w v}
    → (∀ w (a : hom w x) v (b : hom y v)
        → F w a v b ≡ G w a v b)
    → F ≡ G
  emb-ext h =
    funext λ w → funext λ a →
      funext λ v → funext λ b → h w a v b
```


### Classifier derivations via polarity

```agda
  classifier-idn-l : ∀ {x y} (f : hom x y)
    → classifier idn f
  classifier-idn-l {x} {y} f = rec
    {X = classifier idn f}
    (λ pos → inr (pos f))
    (λ neg → inl (neg idn))
    (λ pos neg → sym (push (neg idn) (pos f)))
    (polarity x)

  classifier-idn-r : ∀ {x y} (f : hom x y)
    → classifier f idn
  classifier-idn-r {x} {y} f = rec
    {X = classifier f idn}
    (λ pos → inr (pos idn))
    (λ neg → inl (neg f))
    (λ pos neg → sym (push (neg f) (pos idn)))
    (polarity y)

  classifier-assoc
    : ∀ {x y z w}
      {f : hom x y} {g : hom y z} {h : hom z w}
    → (cfg : classifier f g)
    → (cgh : classifier g h)
    → classifier (comp f g cfg) h
    × classifier f (comp g h cgh)
  classifier-assoc {z = z} {f = f} {g} {h}
    cfg cgh = cl , cr
    where
      cl : classifier (comp f g cfg) h
      cl = rec
        (λ pos → inr (pos h))
        (λ neg → inl (neg (comp f g cfg)))
        (λ pos neg →
          sym (push (neg (comp f g cfg)) (pos h)))
        (polarity z)

      cr : classifier f (comp g h cgh)
      cr = rec
        (λ pos → inr (pos (comp g h cgh)))
        (λ neg → inl (neg f))
        (λ pos neg →
          sym (push (neg f) (pos (comp g h cgh))))
        (polarity _)
```


### Composable fiber and combinators

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
    ∙ interchange f g w a _ idn

  comp-eq
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → (c : classifier f g)
    → comp f g c ≡ yon g _ f
  comp-eq f g c =
    sym (yon-eval (comp f g c))
    ∙ yon-composite f g c _ idn
    ∙ ap (yon g _) (yon-eval f)
```


### Absorb

The absorb laws follow from idempotency of identity
composition, via left-cancellation from the unit
equivalences.

```agda
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
      ∙ interchange idn idn w a x idn

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
```


### Combinator identities

```agda
  combinator-idn-l
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb idn w a v (noy f v b)
    ≡ emb f w a v b
  combinator-idn-l f w a v b =
    interchange idn f w a v b
    ∙ ap (λ t → emb f w t v b) (absorb-r a)

  combinator-idn-r
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb f w a v (noy idn v b)
    ≡ emb f w a v b
  combinator-idn-r f w a v b =
    ap (emb f w a v) (absorb-l b)
```


### Embedding properties

`emb-noy` and `emb-yon` decompose `emb f` using the
identity. `emb-image-contr` shows the emb-fiber is
contractible.

```agda
  emb-noy
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w a v (noy f v b)
  emb-noy f w a v b =
    ap (λ t → emb f w t v b) (sym (absorb-r a))
    ∙ sym (interchange idn f w a v b)

  emb-yon
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w (yon f w a) v b
  emb-yon f w a v b =
    ap (emb f w a v) (sym (absorb-l b))
    ∙ interchange f idn w a v b

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

  emb-inj-ext
    : ∀ {x y} {f g : hom x y}
    → emb f ≡ emb g → f ≡ g
  emb-inj-ext {f = f} {g} p =
    emb-inj λ w a v b i → p i w a v b
```


### Injectivity of yon and noy

```agda
  yon-inj
    : ∀ {x y} {f g : hom x y}
    → yon f ≡ yon g → f ≡ g
  yon-inj {f = f} {g} p = emb-inj λ w a v b →
    emb-yon f w a v b
    ∙ ap (λ t → emb idn w t v b)
        (λ i → p i w a)
    ∙ sym (emb-yon g w a v b)

  noy-inj
    : ∀ {x y} {f g : hom x y}
    → noy f ≡ noy g → f ≡ g
  noy-inj {f = f} {g} p = emb-inj λ w a v b →
    emb-noy f w a v b
    ∙ ap (λ t → emb idn w a v t)
        (λ i → p i v b)
    ∙ sym (emb-noy g w a v b)

```


### Composable-is-prop and classifier-prop

`composable f g` is `is-contr (fiber emb ...)`, which is
propositional by `is-contr-is-prop`.

```agda
  composable-is-prop
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-prop (composable f g)
  composable-is-prop f g = is-contr-is-prop _

  is-thunkable-is-prop : ∀ {x y} (f : hom x y)
    → is-prop (is-thunkable f)
  is-thunkable-is-prop f =
    Π-is-prop λ _ → Π-is-prop λ g →
      composable-is-prop f g

  is-linear-is-prop : ∀ {x y} (g : hom x y)
    → is-prop (is-linear g)
  is-linear-is-prop g =
    Π-is-prop λ _ → Π-is-prop λ f →
      composable-is-prop f g

  classifier-prop
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-prop (classifier f g)
  classifier-prop = Join-is-prop
    (is-thunkable-is-prop _)
    (is-linear-is-prop _)
```


### Unit laws and associativity

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

The ternary fiber E₃ and its contractibility.

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


### Virtual category extraction

```agda
  to-virtual-category : V.virtual-category o h (o ⊔ h)
  to-virtual-category .V.virtual-category.ob = ob
  to-virtual-category .V.virtual-category.hom = hom
  to-virtual-category .V.virtual-category.emb = emb
  to-virtual-category .V.virtual-category.unit = unit
  to-virtual-category .V.virtual-category.yon-eval =
    yon-eval
  to-virtual-category .V.virtual-category.classifier =
    classifier
  to-virtual-category
    .V.virtual-category.classifier-prop =
    classifier-prop
  to-virtual-category
    .V.virtual-category.compose-classified =
    compose-classified
  to-virtual-category
    .V.virtual-category.interchange-classified
    f g _ = interchange f g
  to-virtual-category
    .V.virtual-category.classifier-idn-l =
    classifier-idn-l
  to-virtual-category
    .V.virtual-category.classifier-idn-r =
    classifier-idn-r
  to-virtual-category
    .V.virtual-category.classifier-assoc
    cfg cgh = classifier-assoc cfg cgh
```
