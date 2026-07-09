Lane Biocini
July 2026

The free scaffolding of a braided monoidal structure. The
associator `⊗-assoc` is free because reassociation keeps
`tensor-emb`'s target fixed: `(x ⊗ y) ⊗ z` and `x ⊗ (y ⊗ z)`
both represent the same ternary operation, so the associator is
`ap fst` of an identification inside one contractible fiber. A
braiding is different: it *moves* the target. The object `x ⊗ y`
represents `λ l r → tensor-emb x l (noy y r)`, whereas `y ⊗ x`
represents `λ l r → tensor-emb y l (noy x r)`, and these are
genuinely distinct operations. So the braiding needs one new
datum — a path between those two operations — but that path is
supplied by interchange together with a single flank swap, and
the object braiding then derives by the *same* contractible-fiber
projection as `⊗-assoc`: an explicit rhs fiber point read off with
`ap fst`.

The genuinely-new field is `tensor-flank-swap`: interchange
already carries `tensor-emb x l (noy y r) ≡ tensor-emb y (yon x l) r`,
so the only half it does not give us is moving the swapped factor
from a `yon` on the left flank to a `noy` on the right flank. Once
that half is a field, the full braid `tensor-braid` composes it
after interchange, `tensor-emb-ext` promotes it to a path of
operations `tensor-braid-ext`, and `β` is read off a contractible
composition fiber exactly as the associator is.

Invertibility is free: `β` is a path in `ob`, so its symmetry is
its inverse — there is no separate axiom, unlike the classical
definition where the braiding's invertibility is an imposed
condition on a natural transformation.

The hexagon coherences are *not* free. They are cross-target
2-paths relating the braid to the associator, and they are
deferred to a later module.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Braid where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan

open import Cat.Type
open import Cat.Monoidal
```

## The braided record

`tensor-flank-swap` is the one honest datum. Everything below it
is derived: the record has a single field, so the derived
definitions (which use `where`) follow the last field.

```agda
record braided {o h} {C : category o h} (M : monoidal C) : Type (o ⊔ h) where
  open monoidal M
  open category C using (ob)

  field
    tensor-flank-swap
      : (y x l r : ob)
      → tensor-emb y (yon x l) r ≡ tensor-emb y l (noy x r)

  tensor-braid
    : (x y l r : ob)
    → tensor-emb x l (noy y r) ≡ tensor-emb y l (noy x r)
  tensor-braid x y l r =
    tensor-interchange x y l r ∙ tensor-flank-swap y x l r
```

## The object braiding

`tensor-braid-ext` promotes the pointwise braid to a path between
the two representing operations. `β` supplies an explicit rhs
fiber point — the object `x ⊗ y` together with the witness
`tensor-emb-composite x y ∙ tensor-braid-ext x y`, which composes
the composite equation with the promoted braid to land at
`λ l r → tensor-emb y l (noy x r)` — and then projects the
contractible-fiber identification against `tensor-compose-contr y x`
with `ap fst`, exactly the `⊗-assoc` idiom. The point's first
component is `x ⊗ y` definitionally, so no transport is needed.

```agda
  tensor-braid-ext
    : (x y : ob)
    → (λ l r → tensor-emb x l (noy y r))
    ≡ (λ l r → tensor-emb y l (noy x r))
  tensor-braid-ext x y = tensor-emb-ext (tensor-braid x y)

  β : (x y : ob) → x ⊗ y ≡ y ⊗ x
  β x y =
    ap fst
      (is-contr→is-prop (tensor-compose-contr y x)
        P₁ (tensor-compose-contr y x .center))
    where
      P₁ : fiber tensor-emb (λ l r → tensor-emb y l (noy x r))
      P₁ = x ⊗ y , tensor-emb-composite x y ∙ tensor-braid-ext x y

  β-inv : (x y : ob) → y ⊗ x ≡ x ⊗ y
  β-inv x y = sym (β x y)
```
