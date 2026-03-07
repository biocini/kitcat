Lane Biocini
February 2026

# Categories via symmetric Segal conditions

The covariant Segal conditions ask that `fiber yon (λ _ → id)` and
`fiber yon (λ w → yon g w ∘ yon f w)` are contractible. The contravariant
conditions ask the same for `yon-op`. Contractibility subsumes existence
(the center gives `idn` and `_⨾_`) and uniqueness (which gives the
embedding properties). The covariant/contravariant pairing gives perfect
op-symmetry.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv
open import Core.Transport
open import Core.Path using (ap-comp)
open import Core.Trait.Trunc
  using ( Π-is-prop; Πi-is-prop )
open import Core.Function.Base
open import Core.Function.Embedding

record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y

    idn-contr
      : ∀ {x}
      → is-contr
          (fiber yon (λ (_ : ob) → id {A = hom _ x}))
    composable-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (fiber yon (λ w → yon g w ∘ yon f w))

  idn : ∀ {x} → hom x x
  idn = idn-contr .center .fst

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = composable-contr f g .center .fst
  infixr 40 _⨾_

  yon-op : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  yon-op {x} f z g = yon g x f

  field
    idn-op-contr
      : ∀ {x}
      → is-contr
          (fiber (yon-op {x} {x}) (λ (_ : ob) → id))
    composable-op-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr
          (fiber (yon-op {x} {z})
            (λ w → yon-op f w ∘ yon-op g w))

  {-# INLINE yon #-}
```

## Cat module

```agda
module Cat {o} {h} (C : category o h) where
  open category C public
```

### Basic witnesses

```agda
  yon-idn : ∀ {x} → yon (idn {x}) ≡ (λ _ → id)
  yon-idn = idn-contr .center .snd

  yon-st
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → yon (f ⨾ g) ≡ (λ w → yon g w ∘ yon f w)
  yon-st f g = composable-contr f g .center .snd

  yon-idn-pt
    : ∀ {x} (w : ob) (k : hom w x)
    → yon idn w k ≡ k
  yon-idn-pt w k i = yon-idn i w k
```

### Contravariant identity

The contravariant Segal condition gives its own identity `op-idn`
with `yon g x op-idn ≡ g` for all g. Both conditions applied to each
other force `op-idn ≡ idn`.

```agda
  private
    op-idn : ∀ {x} → hom x x
    op-idn = idn-op-contr .center .fst

    op-idn-wit
      : ∀ {x} → yon-op (op-idn {x}) ≡ (λ _ → id)
    op-idn-wit = idn-op-contr .center .snd

    op-idn-pt
      : ∀ {x} (z : ob) (g : hom x z)
      → yon g x op-idn ≡ g
    op-idn-pt z g i = op-idn-wit i z g

    op-idn≡idn : ∀ {x} → op-idn {x} ≡ idn
    op-idn≡idn =
      sym (yon-idn-pt _ op-idn) ∙ op-idn-pt _ idn

  yon-op-idn-pt
    : ∀ {x} (z : ob) (g : hom x z)
    → yon g x idn ≡ g
  yon-op-idn-pt z g =
    ap (yon g _) (sym op-idn≡idn) ∙ op-idn-pt z g
```

### yon-emb

Any inhabited fiber of `yon` is contractible:
`composable-contr idn m` gives contractibility of
`fiber yon (yon m)` after transport along the identity witness.

```agda
  yon-image-contr
    : ∀ {x y} (m : hom x y)
    → is-contr (fiber yon (yon m))
  yon-image-contr m =
    subst (is-contr ∘ fiber yon) path
      (composable-contr idn m)
    where
      path : (λ w → yon m w ∘ yon idn w) ≡ yon m
      path i w k = yon m w (yon-idn-pt w k i)

  yon-emb : ∀ {x y} → is-embedding (yon {x} {y})
  yon-emb t (n , p) =
    is-contr→is-prop
      (subst (is-contr ∘ fiber yon) p
        (yon-image-contr n))
      (n , p)
```

### yon-op-emb

Dual construction using the contravariant Segal conditions.

```agda
  private
    yon-op-image-contr
      : ∀ {x y} (m : hom x y)
      → is-contr (fiber yon-op (yon-op m))
    yon-op-image-contr m =
      subst (is-contr ∘ fiber yon-op) path
        (composable-op-contr idn m)
      where
        path
          : (λ w → yon-op idn w ∘ yon-op m w)
          ≡ yon-op m
        path i w k = yon-op-idn-pt w (yon-op m w k) i

  yon-op-emb
    : ∀ {x y} → is-embedding (yon-op {x} {y})
  yon-op-emb t (n , p) =
    is-contr→is-prop
      (subst (is-contr ∘ fiber yon-op) p
        (yon-op-image-contr n))
      (n , p)
```

### Composite vocabulary

```agda
  composite
    : ∀ {x y z} → hom x y → hom y z → hom x z
    → Type (o ⊔ h)
  composite f g s = yon s ≡ λ w → yon g w ∘ yon f w
  syntax composite f g s = f ⨾ g => s

  is-composable
    : ∀ {x y z} → hom x y → hom y z → Type (o ⊔ h)
  is-composable f g = fiber yon (λ w → yon g w ∘ yon f w)

  composite-contr
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr (is-composable f g)
  composite-contr = composable-contr

  cast-path
    : ∀ {x y z} {f : hom x y} {g : hom y z}
      {s : hom x z}
    → f ⨾ g => s → f ⨾ g ≡ s
  cast-path {f = f} {g} α =
    ap fst (composite-contr f g .paths (_ , α))

  cast-pathp
    : ∀ {x y z} {f : hom x y} {g : hom y z}
      {s : hom x z}
    → (α : f ⨾ g => s)
    → PathP (λ i → f ⨾ g => (cast-path α i))
        (yon-st f g) α
  cast-pathp {f = f} {g} α =
    ap snd (composite-contr f g .paths (_ , α))

  is-composable-is-prop
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-prop (is-composable f g)
  is-composable-is-prop f g =
    is-contr→is-prop (composite-contr f g)

  yon-inj
    : ∀ {x y} {f g : hom x y}
    → yon f ≡ yon g → f ≡ g
  yon-inj = is-embedding→injective yon-emb

  yon-op-inj
    : ∀ {x y} {f g : hom x y}
    → yon-op f ≡ yon-op g → f ≡ g
  yon-op-inj = is-embedding→injective yon-op-emb
```

### comp-eq and yon-nat

The composition `f ⨾ g` equals `yon g x f`, the Yoneda pairing.
This follows by evaluating the composition witness at `idn`.

```agda
  comp-eq
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → f ⨾ g ≡ yon g x f
  comp-eq f g =
    sym (yon-op-idn-pt _ (f ⨾ g))
    ∙ (λ i → yon-st f g i _ idn)
    ∙ ap (yon g _) (yon-op-idn-pt _ f)
```

The naturality condition says precomposing with `f ⨾ g` decomposes
as two precompositions. We extract this from the contractible
contravariant composition fiber: the center gives `(r, α)`, and
we show `r ≡ f ⨾ g` by evaluating `α` at the identity.

```agda
  yon-nat
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      (w : ob) (k : hom z w)
    → yon k x (f ⨾ g) ≡ yon (yon k y g) x f
  yon-nat f g w k =
    ap (yon k _) fg≡r ∙ (λ i → α i w k)
    where
      r : hom _ _
      r = composable-op-contr f g .center .fst

      α : yon-op r ≡ (λ w → yon-op f w ∘ yon-op g w)
      α = composable-op-contr f g .center .snd

      r≡yon-g-f : r ≡ yon g _ f
      r≡yon-g-f =
        sym (yon-idn-pt _ r)
        ∙ (λ i → α i _ idn)
        ∙ ap (λ h → yon h _ f) (yon-idn-pt _ g)

      fg≡r : f ⨾ g ≡ r
      fg≡r = comp-eq f g ∙ sym r≡yon-g-f
```

### Unit laws and associativity

```agda
  opaque
    unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
    unitr f = cast-path wit where
      wit : f ⨾ idn => f
      wit i w k = yon-idn-pt w (yon f w k) (~ i)

    unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
    unitl f = cast-path wit where
      wit : composite idn f f
      wit i w k = yon f w (yon-idn-pt w k (~ i))

    assoc
      : ∀ {x y z w} (f : hom x y) (g : hom y z)
        (h : hom z w)
      → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
    assoc f g h = cast-path wit where
      wit : composite (f ⨾ g) h (f ⨾ (g ⨾ h))
      wit =
        yon-st f (g ⨾ h)
        ∙ (λ i w k → yon-st g h i w (yon f w k))
        ∙ sym (λ i w k → yon h w (yon-st f g i w k))
```

### Induction and crossing lemmas

```agda
  yon-ind
    : ∀ {ℓ'} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z) → f ⨾ g => s → Type ℓ')
    → P (f ⨾ g) (yon-st f g)
    → ∀ s q → P s q
  yon-ind f g P base m p =
    coe01 (λ i → P (path i .fst) (path i .snd)) base
    where
      path : (f ⨾ g , yon-st f g) ≡ (m , p)
      path = composite-contr f g .paths (m , p)

  lcross
    : ∀ {w x y z} (f : hom w x) (g : hom x y)
      (h : hom y z)
      {s : hom w y}
    → f ⨾ g => s → s ⨾ h ≡ f ⨾ (g ⨾ h)
  lcross f g h α =
    sym (ap (_⨾ h) (cast-path α)) ∙ assoc f g h

  rcross
    : ∀ {w x y z} (f : hom w x) (g : hom x y)
      (h : hom y z)
      {r : hom x z}
    → g ⨾ h => r → (f ⨾ g) ⨾ h ≡ f ⨾ r
  rcross f g h β =
    assoc f g h ∙ ap (f ⨾_) (cast-path β)

  conj
    : ∀ {w x y z} (f : hom w x) (g : hom x y)
      (h : hom y z)
      {s : hom w y} {r : hom x z}
    → f ⨾ g => s → g ⨾ h => r
    → s ⨾ h ≡ f ⨾ r
  conj f g h α β =
    sym (ap (_⨾ h) (cast-path α))
    ∙ assoc f g h
    ∙ ap (f ⨾_) (cast-path β)
```

### Embeddings

```agda
  emb : ∀ {x y} → hom x y ↪ (∀ w → hom w x → hom w y)
  emb .fst = yon
  emb .snd = yon-emb

  emb-op
    : ∀ {x y}
    → hom x y ↪ (∀ z → hom y z → hom x z)
  emb-op .fst = yon-op
  emb-op .snd = yon-op-emb

  emb-inj
    : ∀ {x y} {f g : hom x y}
    → (∀ w (h : hom w x) → h ⨾ f ≡ h ⨾ g)
    → f ≡ g
  emb-inj {f = f} {g} p =
    pcom (unitl f) (p _ idn) (unitl g)

  emb-op-inj
    : ∀ {x y} {f g : hom x y}
    → (∀ z (h : hom y z) → f ⨾ h ≡ g ⨾ h)
    → f ≡ g
  emb-op-inj {f = f} {g} p =
    pcom (unitr f) (p _ idn) (unitr g)
```

## Opposite category

The opposite category swaps morphism direction. In op, `yon` becomes
`yon-op` from the original category. The covariant and contravariant
Segal conditions swap.

```agda
module _ {o h} (C : category o h) where
  private module C = Cat C

  op : category o h
  op .category.ob = C.ob
  op .category.hom = flip C.hom
  op .category.yon = C.yon-op
  op .category.idn-contr =
    C.idn-op-contr
  op .category.composable-contr f g =
    C.composable-op-contr g f
  op .category.idn-op-contr =
    C.idn-contr
  op .category.composable-op-contr f g =
    C.composable-contr g f
```

## Opposite involution

The structural fields (ob, hom, yon) are definitionally equal after
double reversal. The Segal conditions are propositions (is-contr is
a proposition), so `is-prop→PathP` fills them.

```agda
module _ {o h} (C : category o h) where
  private module C = Cat C

  op-invol : op (op C) ≡ C
  op-invol i .category.ob = C.ob
  op-invol i .category.hom = C.hom
  op-invol i .category.yon {x} {y} = C.yon {x} {y}
  op-invol i .category.idn-contr {x} =
    is-prop→PathP
      {A = λ _ → is-contr
        (fiber (C.yon {x}) (λ _ → id))}
      (λ _ → is-contr-is-prop _)
      (category.idn-contr (op (op C)))
      C.idn-contr i
  op-invol i .category.composable-contr
    {x} {y} {z} f g =
    is-prop→PathP
      {A = λ _ → is-contr
        (fiber (C.yon {x} {z})
          (λ w → C.yon {y} {z} g w
               ∘ C.yon {x} {y} f w))}
      (λ _ → is-contr-is-prop _)
      (category.composable-contr (op (op C)) f g)
      (C.composable-contr f g) i
  op-invol i .category.idn-op-contr {x} =
    is-prop→PathP
      {A = λ _ → is-contr
        (fiber (C.yon-op {x} {x}) (λ _ → id))}
      (λ _ → is-contr-is-prop _)
      (category.idn-op-contr (op (op C)))
      C.idn-op-contr i
  op-invol i .category.composable-op-contr
    {x} {y} {z} f g =
    is-prop→PathP
      {A = λ _ → is-contr
        (fiber (C.yon-op {x} {z})
          (λ w → C.yon-op {x} {y} f w
               ∘ C.yon-op {y} {z} g w))}
      (λ _ → is-contr-is-prop _)
      (category.composable-op-contr (op (op C)) f g)
      (C.composable-op-contr f g) i
```
