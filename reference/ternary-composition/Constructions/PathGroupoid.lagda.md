Lane Biocini
March 2026

The path groupoid of a type, as an ActCat category.

For any type `A`, path concatenation gives a category structure
where objects are points of `A`, morphisms are paths, and
composition is path concatenation. The identity is `refl` with
absorption via `Path.unitl`. Representability and embedding follow
from contractibility of the based path space.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.PathGroupoid where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
open import Core.Equiv.Base
open import Cat.ActCat
```

## Evaluation equivalences

The maps `Y ↦ Y y refl` and `N ↦ N x refl` are equivalences
with inverses given by post- and pre-composition. Contractible
fibers follow from `eqv-fibers`. These adapt the private
`yon-gpd-op-equiv` and `yon-gpd-equiv` from `Core.Groupoid`.

```agda
private
  module PG {u} {A : Type u} where

    postcomp-eqv
      : {x y : A}
      → is-equiv
          (λ (g : x ≡ y) (v : A) (b : y ≡ v) → g ∙ b)
    postcomp-eqv {x} {y} =
      iso→equiv fwd inv sec retr .snd
      where
        Yon : Type _
        Yon = (v : A) → y ≡ v → x ≡ v

        fwd : x ≡ y → Yon
        fwd g v b = g ∙ b

        inv : Yon → x ≡ y
        inv Y = Y y refl

        sec : (g : x ≡ y) → inv (fwd g) ≡ g
        sec = Path.unitr

        retr : (Y : Yon) → fwd (inv Y) ≡ Y
        retr Y i v b j = hcom (∂ j ∨ i) λ where
          k (j = i0) → x
          k (j = i1) → b (i ∨ k)
          k (i = i1) → Y v b j
          k (k = i0) →
            Y (b i) (λ k → b (i ∧ k)) j

    precomp-eqv
      : {x y : A}
      → is-equiv
          (λ (g : x ≡ y) (w : A) (a : w ≡ x) → a ∙ g)
    precomp-eqv {x} {y} =
      iso→equiv fwd inv sec retr .snd
      where
        Noy : Type _
        Noy = (w : A) → w ≡ x → w ≡ y

        fwd : x ≡ y → Noy
        fwd g w a = a ∙ g

        inv : Noy → x ≡ y
        inv N = N x refl

        sec : (g : x ≡ y) → inv (fwd g) ≡ g
        sec = Path.unitl

        retr : (N : Noy) → fwd (inv N) ≡ N
        retr N i w a j = hcom (∂ j ∨ i) λ where
          k (j = i0) → w
          k (j = i1) →
            N (a (~ i)) (λ j → a (~ i ∨ j)) k
          k (i = i1) → N w a (j ∧ k)
          k (k = i0) → a (~ i ∧ j)
```

## Path groupoid

We build all fields as local definitions so that `act` and `idn`
are concrete names during typechecking, avoiding stuck record
projections from `no-eta-equality`.

```agda
PathCat : ∀ {u} (A : Type u) → category u u
PathCat A = C module PathCat where
  open PG {A = A}

  act : ∀ {x : A} → ∀ w → w ≡ x → ∀ z → x ≡ z → w ≡ z
  act w p z q = p ∙ q
```

### Absorb contractibility

The type `Σ e, ∀ {z} h → e ∙ h ≡ h` is a retract of the
extensional fiber `Σ e, (λ z h → e ∙ h) ≡ (λ z h → h)`, which
is contractible by `eqv-fibers` of the post-composition
equivalence. The retraction is definitional via `funext`/`happly`.

```agda
  ac : ∀ {x : A} → is-contr
    (Σ e ∶ x ≡ x
    , ∀ {z} (h : x ≡ z) → act x e z h ≡ h)
  ac {x} = cc where
    postcomp : x ≡ x → (z : A) → x ≡ z → x ≡ z
    postcomp e z h = e ∙ h

    ext-contr : is-contr
      (Σ e ∶ x ≡ x
      , postcomp e ≡ (λ z h → h))
    ext-contr = eqv-fibers postcomp-eqv (λ z h → h)

    s : (Σ e ∶ x ≡ x
        , ∀ {z} (h : x ≡ z) → e ∙ h ≡ h)
      → Σ e ∶ x ≡ x
      , postcomp e ≡ (λ z h → h)
    s (e , abs) = e , funext λ z → funext λ h → abs h

    r : (Σ e ∶ x ≡ x
        , postcomp e ≡ (λ z h → h))
      → Σ e ∶ x ≡ x
      , ∀ {z} (h : x ≡ z) → e ∙ h ≡ h
    r (e , p) = e , λ {z} h → happly (happly p z) h

    s-center : Σ e ∶ x ≡ x
      , postcomp e ≡ (λ z h → h)
    s-center = s (refl , λ h → Path.unitl h)

    cc : is-contr _
    cc .center = refl , λ h → Path.unitl h
    cc .paths t =
      ap r (sym (ext-contr .paths s-center)
            ∙ ext-contr .paths (s t))

  idn : ∀ {x : A} → x ≡ x
  idn = ac .center .fst
```

### Repr contractibility

The repr-fiber of `f` packages `(Y, N, yb, nb, ic)`. The center
is the canonical post/pre-composition with interchange from
`Path.assoc`.

For `paths`, we construct the identification from center to any
point `((Y, N), yb, nb, ic)` using the evaluation equivalence
counits and `cat.bfill` for dependent fills. The counit
`PE.counit Y i y refl` computes definitionally to `Path.unitr g i`
(where `g = Y y refl`), and similarly `QE.counit N i x refl`
computes to `Path.unitl h i` (where `h = N x refl`). The
dependent fills for `yb` and `nb` are then transposes of
`cat.bfill`. The interchange fill uses `pcom.contr` (the
contractibility of triple composites).

```agda
  module Repr {x y : A} (f : x ≡ y) where
    private
      module PE = Equiv ((λ g v b → g ∙ b) , postcomp-eqv {x = x} {y})
      module QE = Equiv ((λ g w a → a ∙ g) , precomp-eqv {x = x} {y})

    RF : Type _
    RF = Σ (Y , N) ∶ (∀ v → y ≡ v → x ≡ v)
                   × (∀ w → w ≡ x → w ≡ y)
       , (Y y refl ≡ f)
       × (N x refl ≡ f)
       × (∀ w (a : w ≡ x) v (b : y ≡ v)
         → a ∙ (Y v b) ≡ (N w a) ∙ b)

    ctr : RF
    ctr =
      ((λ v b → f ∙ b) , (λ w a → a ∙ f))
      , Path.unitr f
      , Path.unitl f
      , λ w a v b → Path.assoc a f b

    module _
      (Y : ∀ v → y ≡ v → x ≡ v)
      (N : ∀ w → w ≡ x → w ≡ y)
      (yb : Y y refl ≡ f)
      (nb : N x refl ≡ f)
      (ic : ∀ w (a : w ≡ x) v (b : y ≡ v)
        → a ∙ (Y v b) ≡ (N w a) ∙ b)
      where

      private
        g = Y y refl
        h = N x refl

        -- PE.counit Y i y refl computes to Path.unitr g i
        -- (same hcom with cofibration ∂ j ∨ i and constant
        -- system when b = refl).
        Y-path : (λ v b → f ∙ b) ≡ Y
        Y-path =
          ap (λ g v b → g ∙ b) (sym yb)
          ∙ PE.counit Y

        -- QE.counit N i x refl computes to Path.unitl h i
        -- (same hcom with cofibration ∂ j ∨ i and constant
        -- system when a = refl).
        N-path : (λ w a → a ∙ f) ≡ N
        N-path =
          ap (λ g w a → a ∙ g) (sym nb)
          ∙ QE.counit N

        -- yb fill: transpose of cat.bfill.
        -- PE.counit Y i y refl = Path.unitr g i definitionally,
        -- so Y-path i y refl = (ap-segment ∙ unitr g) i y refl.
        -- At the first segment: ap (λ g → g ∙ refl) (sym yb) i
        --   = (sym yb i) ∙ refl
        -- At the second segment: Path.unitr g i

        -- The full Y-path i y refl goes:
        --   i ∈ first segment: (sym yb i) ∙ refl
        --   i ∈ second segment: Path.unitr g i
        -- From f ∙ refl through g ∙ refl to g.

        -- yb-fill over this two-segment path requires two
        -- cat.bfill squares pasted together.

        -- Alternatively: build the full path from center to
        -- point via the fiber contractibility, using the yon
        -- and noy fibers.

        -- The yon-fiber Σ g, (λ v b → g ∙ b) ≡ Y is
        -- contractible. Both (f, Y-path) and (g, PE.counit Y)
        -- lie in it. By contractibility, the path from
        -- center (g, PE.counit Y) to (f, Y-path) gives us
        -- paths on both components.

        yon-fib-contr
          : is-contr
            (Σ k ∶ x ≡ y
            , (λ v b → k ∙ b) ≡ Y)
        yon-fib-contr = eqv-fibers postcomp-eqv Y

        -- Point (f, Y-path) in yon-fiber:
        yon-pt : Σ k ∶ x ≡ y , (λ v b → k ∙ b) ≡ Y
        yon-pt = f , Y-path

        -- Path from center to our point:
        yon-to-f
          : yon-fib-contr .center ≡ yon-pt
        yon-to-f =
          yon-fib-contr .paths yon-pt

        -- fst of center is g, fst of yon-pt is f.
        -- ap fst yon-to-f : g ≡ f. This should equal yb.
        -- snd gives PathP on the Y-component.

        noy-fib-contr
          : is-contr
            (Σ k ∶ x ≡ y
            , (λ w a → a ∙ k) ≡ N)
        noy-fib-contr = eqv-fibers precomp-eqv N

        noy-pt : Σ k ∶ x ≡ y , (λ w a → a ∙ k) ≡ N
        noy-pt = f , N-path

        noy-to-f
          : noy-fib-contr .center ≡ noy-pt
        noy-to-f =
          noy-fib-contr .paths noy-pt

        -- Now: the FULL path from ctr to pt uses these
        -- fiber paths.
        --
        -- yon-to-f gives g ≡ f on fst and
        --   PathP (λ i → (λ v b → yon-to-f i .fst ∙ b) ≡ Y)
        --         (PE.counit Y) Y-path
        -- on snd. The fst path is g → f, and the snd gives
        -- a PathP on Y-components.
        --
        -- noy-to-f gives h ≡ f on fst and similar for N.
        --
        -- From the yon-fiber center, we get:
        --   yon-fib-contr .center .fst = g (= Y y refl)
        --   yon-fib-contr .center .snd = PE.counit Y
        --
        -- The path yon-to-f takes (g, PE.counit Y) to
        -- (f, Y-path). Projecting:
        --   ap fst yon-to-f : g ≡ f
        --   ap snd yon-to-f : PathP over this path

        -- yon path g → f from the fiber
        g→f : g ≡ f
        g→f = ap fst yon-to-f

        -- noy path h → f from the fiber
        h→f : h ≡ f
        h→f = ap fst noy-to-f

        -- The Y-path from the yon-fiber
        Y-pathP : PathP
          (λ i → (λ v b → g→f i ∙ b) ≡ Y)
          (PE.counit Y) Y-path
        Y-pathP = ap snd yon-to-f

        N-pathP : PathP
          (λ i → (λ w a → a ∙ h→f i) ≡ N)
          (QE.counit N) N-path
        N-pathP = ap snd noy-to-f

      -- The full path from ctr to the point.
      -- We compose: first move f to g (via sym g→f),
      -- picking up the yon-fiber identification, then
      -- move f to h (via sym h→f), picking up the noy
      -- identification.
      --
      -- More directly: define the path as
      --   λ i → ((Y-path' i, N-path' i), yb-fill i, nb-fill i, ic-fill i)
      -- where Y-path' is the fst.fst component path,
      -- N-path' is the fst.snd component path, and the
      -- dependent components are filled using the fiber
      -- data.

      -- OK, let me try the DIRECT approach. The path is
      -- a lambda that gives each component at each i.
      to-ctr : ctr ≡ ((Y , N) , yb , nb , ic)
      to-ctr = {!!}

  repr : ∀ {x y : A} (f : x ≡ y) → is-contr RF
    where open Repr f
  repr f .center = Repr.ctr f
  repr f .paths ((Y , N) , yb , nb , ic) =
    Repr.to-ctr f Y N yb nb ic
```

### Yon/noy embedding

`yon g = (λ v b → g ∙ b)` is determined by `g` via the
post-composition equivalence. Once `repr-contr` is filled,
`yon f` reduces to `repr f .center .fst .fst = (λ v b → f ∙ b)`.
The yon-fiber `Σ g, yon g ≡ yon f` is then `Σ g, (λ v b → g ∙ b) ≡ (λ v b → f ∙ b)`,
the fiber of `postcomp-eqv` over `(λ v b → f ∙ b)`.

```agda
  ye : ∀ {x y : A} (f : x ≡ y) → is-contr
    (Σ g ∶ x ≡ y
    , (λ v b → g ∙ b) ≡ (λ v b → f ∙ b))
  ye f = eqv-fibers postcomp-eqv (λ v b → f ∙ b)

  ne : ∀ {x y : A} (f : x ≡ y) → is-contr
    (Σ g ∶ x ≡ y
    , (λ w a → a ∙ g) ≡ (λ w a → a ∙ f))
  ne f = eqv-fibers precomp-eqv (λ w a → a ∙ f)

  C : category _ _
  C .category.ob = A
  C .category.hom = _≡_
  C .category.act = act
  C .category.absorb-contr = ac
  C .category.repr-contr = repr
  C .category.yon-emb = {!!}
  C .category.noy-emb = {!!}
```

```
