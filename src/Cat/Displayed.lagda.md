Displayed categories over virtual categories. A displayed category
over C fibers each field of the `category` record: objects, homs,
`emb`, `unit`, `compose-contr`, `interchange`, and `yon-eval`. The
total category `∫ D` assembles the base and displayed data into a
`category`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Type

module Cat.Displayed {o h} (C : category o h) where

open Virtual C

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv.Base using (is-equiv)
```

## The displayed record

Each field fibers over its counterpart in the base `category`.
`ob-d` and `hom-d` give displayed types, `emb-d` gives a displayed
ternary operation. The `unit-d` field packages a displayed identity
with fiberwise equivalences (quantified over a base morphism) and
a displayed yon-idempotency PathP. The `compose-contr-d` field
gives contractibility of the displayed composite fiber at the base
center, and `interchange-d` and `yon-eval-d` are PathP over their
base counterparts.

The displayed unit equivalences quantify over a base morphism `h`
(resp. `g`) and state that the fiberwise map
`λ hd → emb-d ed idn ed h hd` from `hom-d h xd zd` to
`hom-d (noy idn z h) xd zd` is an equivalence. This fibers the
base `unit-eqvl` which says `λ h → noy idn z h` is an equiv on
`hom x z`.

```agda
record displayed o' h' : Type₊ (o ⊔ h ⊔ o' ⊔ h') where
  no-eta-equality
  field
    ob-d  : ob → Type o'
    hom-d : ∀ {x y} → hom x y → ob-d x → ob-d y → Type h'
    emb-d
      : ∀ {x y w z}
        {xd : ob-d x} {yd : ob-d y}
        {wd : ob-d w} {zd : ob-d z}
      → {f : hom x y} → hom-d f xd yd
      → (a : hom w x) → hom-d a wd xd
      → (b : hom y z) → hom-d b yd zd
      → hom-d (emb f w a z b) wd zd
    unit-d : ∀ {x} (xd : ob-d x) →
      Σ ed ∶ hom-d idn xd xd
      , ( (∀ {z} {zd : ob-d z} (h : hom x z)
          → is-equiv
              (λ (hd : hom-d h xd zd) →
                emb-d ed idn ed h hd))
        × (∀ {w} {wd : ob-d w} (g : hom w x)
          → is-equiv
              (λ (gd : hom-d g wd xd) →
                emb-d ed g gd idn ed)))
      × PathP (λ i → hom-d (yon-idpt i) xd xd)
            (emb-d ed idn ed idn ed) ed
```

### Derived displayed operations

```agda
  idn-d : ∀ {x} {xd : ob-d x} → hom-d idn xd xd
  idn-d {xd = xd} = unit-d xd .fst

  unit-eqvl-d
    : ∀ {x z} {xd : ob-d x} {zd : ob-d z}
      (h : hom x z)
    → is-equiv
        (λ (hd : hom-d h xd zd) →
          emb-d idn-d idn idn-d h hd)
  unit-eqvl-d {xd = xd} = unit-d xd .snd .fst .fst

  unit-eqvr-d
    : ∀ {x w} {xd : ob-d x} {wd : ob-d w}
      (g : hom w x)
    → is-equiv
        (λ (gd : hom-d g wd xd) →
          emb-d idn-d g gd idn idn-d)
  unit-eqvr-d {xd = xd} = unit-d xd .snd .fst .snd

  yon-idpt-d
    : ∀ {x} {xd : ob-d x}
    → PathP (λ i → hom-d (yon-idpt i) xd xd)
        (emb-d (idn-d {xd = xd}) idn idn-d idn idn-d)
        idn-d
  yon-idpt-d {xd = xd} = unit-d xd .snd .snd

  noy-d
    : ∀ {x y z}
      {xd : ob-d x} {yd : ob-d y} {zd : ob-d z}
    → {f : hom x y} → hom-d f xd yd
    → (b : hom y z) → hom-d b yd zd
    → hom-d (noy f z b) xd zd
  noy-d fd b bd = emb-d fd idn idn-d b bd

  yon-d
    : ∀ {x y w}
      {xd : ob-d x} {yd : ob-d y} {wd : ob-d w}
    → {f : hom x y} → hom-d f xd yd
    → (a : hom w x) → hom-d a wd xd
    → hom-d (yon f w a) wd yd
  yon-d fd a ad = emb-d fd a ad idn idn-d

  field
    compose-contr-d
      : ∀ {x y z} {f : hom x y} {g : hom y z}
        {xd : ob-d x} {yd : ob-d y} {zd : ob-d z}
      → (fd : hom-d f xd yd) (gd : hom-d g yd zd)
      → is-contr
          (Σ sd ∶ hom-d (f ⨾ g) xd zd
          , (∀ {w v} {wd : ob-d w} {vd : ob-d v}
              (a : hom w x) (ad : hom-d a wd xd)
              (b : hom z v) (bd : hom-d b zd vd)
            → PathP
                (λ i → hom-d
                  (emb-composite-pt f g w a v b i)
                  wd vd)
                (emb-d sd a ad b bd)
                (emb-d fd a ad
                  (noy g v b) (noy-d gd b bd))))

    interchange-d
      : ∀ {x y z} {f : hom x y} {g : hom y z}
        {xd : ob-d x} {yd : ob-d y} {zd : ob-d z}
      → (fd : hom-d f xd yd) (gd : hom-d g yd zd)
      → ∀ {w v} (a : hom w x) {wd : ob-d w}
          (ad : hom-d a wd xd)
          (b : hom z v) {vd : ob-d v}
          (bd : hom-d b zd vd)
      → PathP
          (λ i → hom-d
            (interchange f g w a v b i) wd vd)
          (emb-d fd a ad (noy g v b)
            (noy-d gd b bd))
          (emb-d gd (yon f w a) (yon-d fd a ad)
            b bd)

    yon-eval-d
      : ∀ {x y} {f : hom x y}
        {xd : ob-d x} {yd : ob-d y}
      → (fd : hom-d f xd yd)
      → PathP (λ i → hom-d (yon-eval f i) xd yd)
          (yon-d fd idn idn-d)
          fd
```

### Displayed composition

```agda
  _⨾d_
    : ∀ {x y z} {f : hom x y} {g : hom y z}
      {xd : ob-d x} {yd : ob-d y} {zd : ob-d z}
    → hom-d f xd yd → hom-d g yd zd
    → hom-d (f ⨾ g) xd zd
  fd ⨾d gd = compose-contr-d fd gd .center .fst
  infixr 40 _⨾d_

  emb-composite-d
    : ∀ {x y z} {f : hom x y} {g : hom y z}
      {xd : ob-d x} {yd : ob-d y} {zd : ob-d z}
    → (fd : hom-d f xd yd) (gd : hom-d g yd zd)
    → ∀ {w v} {wd : ob-d w} {vd : ob-d v}
        (a : hom w x) (ad : hom-d a wd xd)
        (b : hom z v) (bd : hom-d b zd vd)
    → PathP
        (λ i → hom-d
          (emb-composite-pt f g w a v b i) wd vd)
        (emb-d (fd ⨾d gd) a ad b bd)
        (emb-d fd a ad (noy g v b)
          (noy-d gd b bd))
  emb-composite-d fd gd =
    compose-contr-d fd gd .center .snd
```

## Total category

The total category `∫ D` has `ob = Σ ob-d`,
`hom (x,xd) (y,yd) = Σ (f : hom x y), hom-d f xd yd`,
and `emb` pairs the base and displayed operations.

The unit equivalences lift via `Σ-dep-map-is-equiv`: the base
equiv (`unit-eqvl`/`unit-eqvr`) pairs with the fiberwise displayed
equiv (`unit-eqvl-d`/`unit-eqvr-d`). The `interchange` and
`yon-eval` fields lift componentwise via PathP.

For `compose-contr`, the center is `(f ⨾ g , fd ⨾d gd)` with
total equation built from `emb-composite` and
`emb-composite-d`. The contraction (`.paths`) requires
extracting a base fiber element from the total path.

The total path `eq : ∫D.emb (s,sd) ≡ target-total` lives
in a function space over total args `(w,wd)(a,ad)(v,vd)(b,bd)`.
Extracting a base path `emb s ≡ target-base` requires
evaluating `eq` at displayed args, but `ob-d w` may be empty
for some base objects w. At such w, the total equation is
vacuously satisfied and places no constraint on `emb s w`.
When the base hom-types `hom w x` are non-empty at these
points, `emb s` can disagree with `target-base` there. The
total fiber then contains elements outside the base fiber,
and the Sigma-decomposition breaks down.

This is a genuine structural obstruction, not a proof
difficulty: the total `compose-contr` fiber may fail to be
contractible when `ob-d` has empty fibers and the base
category has morphisms at those points.

```agda
module _ {o' h'} (D : displayed o' h') where
  open displayed D

  open import Core.Equiv.Properties
    using (Σ-dep-map-is-equiv)

  ∫D : category (o ⊔ o') (h ⊔ h')
  ∫D .category.ob = Σ ob-d
  ∫D .category.hom (x , xd) (y , yd) =
    Σ f ∶ hom x y , hom-d f xd yd
  ∫D .category.emb (f , fd)
    (w , wd) (a , ad) (z , zd) (b , bd) =
    emb f w a z b , emb-d fd a ad b bd

  ∫D .category.unit {x , xd} =
    (idn , idn-d)
    , Σ-dep-map-is-equiv unit-eqvl
          (λ h → unit-eqvl-d h)
    , Σ-dep-map-is-equiv unit-eqvr
          (λ g → unit-eqvr-d g)

  ∫D .category.compose-contr
    (f , fd) (g , gd) .center .fst =
    f ⨾ g , fd ⨾d gd
  ∫D .category.compose-contr
    (f , fd) (g , gd) .center .snd i
    (w , wd) (a , ad) (v , vd) (b , bd) =
    emb-composite f g i w a v b
    , emb-composite-d fd gd a ad b bd i
  ∫D .category.compose-contr
    (f , fd) (g , gd) .paths
    ((s , sd) , eq) = {!!}
    -- BLOCKED: genuine structural obstruction.
    -- See prose above for the analysis.

  ∫D .category.interchange
    (f , fd) (g , gd)
    (w , wd) (a , ad) (v , vd) (b , bd) i =
    interchange f g w a v b i
    , interchange-d fd gd a ad b bd i

  ∫D .category.yon-eval (f , fd) i =
    yon-eval f i , yon-eval-d fd i
```
