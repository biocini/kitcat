Lane Biocini, March 2026

Heterogeneous tight-first representability.

The tight-first `emb a y q z r = pcom (sym a) q r` generalizes
to heterogeneous `q : PathP A x y` giving `PathP A w z`. The
representable fiber `Σ w, ∀ y q z r → PathP A w z` is
contractible, derived from `SinglP-contr` via interval
inversion and `op-emb-equiv` from `Core.Groupoid.Virtual`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.HGroupoid where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv.Base
  using (is-equiv; iso→equiv; is-contr-equiv; _≃_; Equiv)
open import Core.Equiv.Properties using (Σ-equiv-snd; esym)
open import Core.Transport.Base
open import Core.Groupoid.Virtual

private variable
  u : Level
```

## SinglP-contr-cofan

`SinglP-contr x : is-contr (Σ y, PathP A x y)` sums over the
target endpoint `y : A i1`. The cofan version sums over the
source `w : A i0`. Obtained by applying `SinglP-contr` to the
reversed family `λ i → A (~ i)` and converting via `sym`.

```agda

SinglP-contr-cofan
  : ∀ {u} {A : I → Type u} (y : A i1)
  → is-contr (Σ w ∶ A i0 , PathP A w y)
SinglP-contr-cofan {A = A} y .center = coe10 A y , inv-coe-filler A y
SinglP-contr-cofan {A = A} y .paths (x , q) i = lid i , filler where
  sys : (φ : I) → HSys (∂ φ) (∂.sym A)
  sys φ k (φ = i0) = coe0i (∂.sym A) k y
  sys φ k (k = i0) = y
  sys φ k (φ = i1) = q (~ k)

  lid : coe01 (∂.sym A) y ≡ x
  lid j = com (∂.sym A) (∂ j) (sys j)

  filler : PathP A (lid i) y
  filler j = fil (∂.sym A) (∂ i) (~ j) (sys i)

```

## Heterogeneous emb

```agda

module _ {A : I → Type u} where

  emb : {w x : A i0}
      → w ≡ x
      → ∀ (y : A i1) → PathP A x y
      → ∀ (z : A i1) → y ≡ z → PathP A w z
  emb a y q z r = pcom (sym a) q r

```

## Representable fiber

The representable type bundles `w : A i0` with a heterogeneous
composition action. The center is the basepoint `x` with
heterogeneous binary composition.

```agda

  is-representable : A i0 → Type u
  is-representable x =
    Σ w ∶ A i0
    , ∀ (y : A i1) → PathP A x y
      → ∀ (z : A i1) → y ≡ z → PathP A w z

```

## Equivalence

The section recovers the tight cell: `inv (emb a) ≡ a` via
`pcom.unique`. The retraction shows any representable action
is determined by its value at identity arguments.

```agda

  -- private
  --   x' : A i0 → A i1
  --   x' x = coe01 A x

  --   x-fil : (x : A i0) → PathP A x (x' x)
  --   x-fil x = coe-filler A x

  module _ {w x : A i0} where
    private
      -- Evaluate f at identity-like arguments to get PathP A w (coe01 A x),
      -- then transport back to A i0 via com (∂.sym A).
      inv : (∀ (y : A i1) → PathP A x y → ∀ (z : A i1) → y ≡ z → PathP A w z) → w ≡ x
      inv f j = com (∂.sym A) (∂ j) λ where
        k (j = i0) → f (coe01 A x) (coe-filler A x) (coe01 A x) refl (~ k)
        k (k = i0) → coe01 A x
        k (j = i1) → coe0i A (~ k) x

    emb-parametric : (f
       : (y : A i1) → PathP A x y → (z : A i1) → y ≡ z → PathP A w z) → emb (inv f) ≡ f
    emb-parametric f = {!!}

    emb-equiv : is-equiv (emb {w} {x})
    emb-equiv = iso→equiv emb inv sec emb-parametric .snd where
      -- inv (emb a) transports pcom (sym a) (coe-filler A x) refl
      -- back via com (∂.sym A). The round-trip equals a because
      -- the com system is filled by the pcom witness.
      sec : (a : w ≡ x) → inv (emb a) ≡ a
      sec a = {!!}

```

## Contractibility

The representable fiber contractibility requires `emb-equiv`.
Commented out until the retraction is resolved.

```agda

  representable-contr : {x : A i0} → is-contr (is-representable x)
  representable-contr {x} = {!!}


-- `
