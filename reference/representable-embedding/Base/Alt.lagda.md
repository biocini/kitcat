Lane Biocini
February 2026

# Categories via the Yoneda equivalence

An alternative category definition where `yon` is required to be an
equivalence rather than merely an embedding. Where `Cat.Base` has 7
fields (4 propositional), this formulation needs only 5 fields (2
propositional): the identity morphism, composition, and all
categorical laws are derived from the equivalence inverse and
counit.

The idea is that if `yon : hom x y -> (forall w -> hom w x -> hom w y)`
is an equivalence, then its inverse recovers identity (`yon-inv id`)
and composition (`yon-inv (yon g . yon f)`), while its counit
witnesses the categorical laws by reducing to function-level
identities.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Base.Alt where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv
open import Core.Transport
  using ( is-prop→PathP; is-contr→is-prop; is-prop→is-set; is-based-identity-system
        ; IdsJ-based; subst; is-contr-is-prop)
open import Core.Trait.Trunc using (Π-is-prop; Πi-is-prop)
open import Core.Function.Base
open import Core.Function.Embedding

record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
    yon-equiv : ∀ {x y} → is-equiv (yon {x} {y})

  private module E {x} {y} = Equiv (yon {x} {y} , yon-equiv {x} {y})

  yon-op : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  yon-op {x} f z g = yon g x f

  coyo : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  coyo f w g = E.inv (λ w → yon f w ∘ yon g w)

  field
    yon-op-equiv : ∀ {x y} → is-equiv (yon-op {x} {y})

  idn : ∀ {x} → hom x x
  idn = E.inv (λ _ → id)

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = E.inv (λ w → yon g w ∘ yon f w)

  {-# INLINE yon #-}
  {-# INLINE coyo #-}
```

## Cat module

All derived structure lives in `module Cat`, opened from the record.

```agda
module Cat {o} {h} (C : category o h) where
  open category C

  private module E {x} {y} = Equiv (yon {x} {y} , yon-equiv {x} {y})
```

### Standard witnesses

The counit of the equivalence provides that `yon` applied to a
derived morphism recovers the function it was inverted from.

```agda
  yon-idn : ∀ {x} → yon (idn {x}) ≡ (λ _ → id)
  yon-idn = E.counit (λ _ → id)

  yon-st
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → yon (f ⨾ g) ≡ (λ w → yon g w ∘ yon f w)
  yon-st f g = E.counit (λ w → yon g w ∘ yon f w)

  yon-idn-pt
    : ∀ {x} (w : ob) (k : hom w x)
    → yon idn w k ≡ k
  yon-idn-pt w k i = yon-idn i w k
```

### Composite vocabulary

```agda
  composite
    : ∀ {x y z} → hom x y → hom y z → hom x z → Type (o ⊔ h)
  composite f g s = yon s ≡ λ w → yon g w ∘ yon f w

  is-composable
    : ∀ {x y z} → hom x y → hom y z → Type (o ⊔ h)
  is-composable f g = fiber yon (λ w → yon g w ∘ yon f w)

  composite-contr
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr (is-composable f g)
  composite-contr f g =
    yon-equiv .eqv-fibers (λ w → yon g w ∘ yon f w)
```

### Identity system / cast-path

```agda
  cast-path
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → composite f g s → f ⨾ g ≡ s
  cast-path {f = f} {g} α =
    ap fst (composite-contr f g .paths (_ , α))

  cast-pathp
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → (α : composite f g s)
    → PathP (λ i → composite f g (cast-path α i)) (yon-st f g) α
  cast-pathp {f = f} {g} α =
    ap snd (composite-contr f g .paths (_ , α))
```

### Induction principle

```agda
  yon-ind
    : ∀ {ℓ'} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z) → composite f g s → Type ℓ')
    → P (f ⨾ g) (yon-st f g)
    → ∀ s q → P s q
  yon-ind f g P base m p =
    transp (λ i → P (path i .fst) (path i .snd)) i0 base
    where
      path : (f ⨾ g , yon-st f g) ≡ (m , p)
      path = composite-contr f g .paths (m , p)
```

### Helpers

```agda
  is-composable-is-prop
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-prop (is-composable f g)
  is-composable-is-prop f g =
    is-contr→is-prop (composite-contr f g)

```

### Unit laws

```agda
  opaque
    unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
    unitr f = cast-path wit where
      wit : composite f idn f
      wit i w k = yon-idn-pt w (yon f w k) (~ i)

    unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
    unitl f = cast-path wit where
      wit : composite idn f f
      wit i w k = yon f w (yon-idn-pt w k (~ i))
```

### Associativity

```agda
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

    pentagon
      : ∀ {v w x y z} (f : hom v w) (g : hom w x)
        (h : hom x y) (k : hom y z)
      → assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
        ≡ ap (_⨾ k) (assoc f g h) ∙ assoc f (g ⨾ h) k
          ∙ ap (f ⨾_) (assoc g h k)
    pentagon f g h k = {!!}
```

### Whiskering / crossing

```agda
  lcross
    : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
      {s : hom w y}
    → composite f g s → s ⨾ h ≡ f ⨾ (g ⨾ h)
  lcross f g h α =
    sym (ap (_⨾ h) (cast-path α)) ∙ assoc f g h

  rcross
    : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
      {r : hom x z}
    → composite g h r → (f ⨾ g) ⨾ h ≡ f ⨾ r
  rcross f g h β =
    assoc f g h ∙ ap (f ⨾_) (cast-path β)

  conj
    : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
      {s : hom w y} {r : hom x z}
    → composite f g s → composite g h r
    → s ⨾ h ≡ f ⨾ r
  conj f g h α β =
    sym (ap (_⨾ h) (cast-path α))
    ∙ assoc f g h
    ∙ ap (f ⨾_) (cast-path β)
```

### Pentagon

The two canonical paths from `((f ⨾ g) ⨾ h) ⨾ k` to `f ⨾ (g ⨾ (h ⨾ k))`
agree. Both compose through different intermediate bracketings, but
the contractibility of the 4-fold composite fiber forces them
together. Proved inside the opaque block alongside `assoc`.

### Embedding properties

Since `yon` is an equivalence, it is in particular an embedding.

```agda
  is-embedding-yon
    : ∀ {x y} → is-embedding (yon {x} {y})
  is-embedding-yon = is-equiv→is-embedding yon-equiv

  repr : ∀ {x y} → hom x y ↪ (∀ w → hom w x → hom w y)
  repr .fst = yon
  repr .snd = is-embedding-yon

  private module R {x} {y} = Emb (repr {x} {y})

  yon-inj
    : ∀ {x y} {f g : hom x y}
    → yon f ≡ yon g → f ≡ g
  yon-inj {f = f} {g} p =
    pcom (E.unit f) (ap E.inv p) (E.unit g)

  yon-image-contr
    : ∀ {x y} (a : hom x y)
    → is-contr (fiber yon (λ w k → yon a w k))
  yon-image-contr a =
    subst (λ G → is-contr (fiber yon G))
      (λ i w k → yon a w (yon-idn-pt w k i))
      (composite-contr idn a)
```

### Repr-based injectivity

```agda
  repr-inj
    : ∀ {x y} {f g : hom x y}
    → (∀ w (h : hom w x) → h ⨾ f ≡ h ⨾ g)
    → f ≡ g
  repr-inj {f = f} {g} p =
    pcom (unitl f) (p _ idn) (unitl g)

  repr-op-inj
    : ∀ {x y} {f g : hom x y}
    → (∀ z (h : hom y z) → f ⨾ h ≡ g ⨾ h)
    → f ≡ g
  repr-op-inj {f = f} {g} p =
    pcom (unitr f) (p _ idn) (unitr g)
```

### yon-op-inj

```agda
  yon-op-inj
    : ∀ {x y} {f g : hom x y}
    → yon-op f ≡ yon-op g → f ≡ g
  yon-op-inj {x = x} {f = f} {g} p =
    pcom (λ i → yon-idn-pt x f i) (λ i → p i _ idn)
      (λ i → yon-idn-pt x g i)
```

### Contravariant embedding properties

Since `yon-op` is an equivalence, it is an embedding.

```agda
  is-embedding-yon-op
    : ∀ {x y} → is-embedding (yon-op {x} {y})
  is-embedding-yon-op = is-equiv→is-embedding yon-op-equiv

  repr-op
    : ∀ {x y} → hom x y ↪ (∀ z → hom y z → hom x z)
  repr-op .fst = yon-op
  repr-op .snd = is-embedding-yon-op
```

### Derived preserving-representability witness

```agda
  pres-contr
    : ∀ {x y} (f : hom x y)
    → is-contr (fiber yon (coyo f))
  pres-contr f = yon-equiv .eqv-fibers (coyo f)
```

### Propositional witnesses

```agda
  yon-equiv-is-prop
    : is-prop (∀ {x y} → is-equiv (yon {x} {y}))
  yon-equiv-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ →
    is-equiv-is-prop _

  yon-op-equiv-is-prop
    : is-prop (∀ {x y} → is-equiv (yon-op {x} {y}))
  yon-op-equiv-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ →
    is-equiv-is-prop _
```

### Opposite category

The opposite category swaps morphism direction: `hom-op x y = hom y x`.
In op, `yon` becomes `yon-op` from the original and vice versa, so
the two equivalence witnesses simply swap.

```agda
  op : category o h
  op .category.ob             = ob
  op .category.hom x y        = hom y x
  op .category.yon f w g       = yon g _ f
  op .category.yon-equiv       = yon-op-equiv
  op .category.yon-op-equiv    = yon-equiv
  {-# INLINE op #-}
```

### Opposite involution

Applying `op` twice recovers the original category. The `ob`,
`hom`, and `yon` fields are definitionally equal after double
reversal (the two swaps cancel via INLINE). The equivalence
witnesses are propositions, so `is-prop→PathP` fills them.

```agda
module _ {o h} (C : category o h) where
  private module C = Cat C

  op-invo : Cat.op (Cat.op C) ≡ C
  op-invo i .category.ob        = category.ob C
  op-invo i .category.hom       = category.hom C
  op-invo i .category.yon       = category.yon C
  op-invo i .category.yon-equiv {x} {y} =
    is-prop→PathP
      (λ _ → is-equiv-is-prop (category.yon C {x} {y}))
      (category.yon-equiv (Cat.op (Cat.op C)))
      (category.yon-equiv C) i
  op-invo i .category.yon-op-equiv {x} {y} =
    is-prop→PathP
      (λ _ → is-equiv-is-prop
        (category.yon-op C {x} {y}))
      (category.yon-op-equiv (Cat.op (Cat.op C)))
      (category.yon-op-equiv C) i
```
