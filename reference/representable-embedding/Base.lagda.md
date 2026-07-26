Lane Biocini
February 2026

# Categories via Representable Embeddings

A category is defined by embedding its morphisms into their
post-composition actions on a function type. Each `f : hom x y`
is faithfully represented by the function `(_ ⨾ f) : hom w x → hom w y`.
Since function types carry algebraic structure for free—composition
is definitionally associative and unital—the category laws reduce
to the statement that two morphisms with the same post-composition
behavior must be equal, which is exactly what the embedding
guarantees via propositional fibers.

## The fields

The first three fields give the basic structure:

  - `repr : hom x y ↪ (∀ w → hom w x → hom w y)` embeds
    each morphism into its post-composition action
  - `unital : fiber (repr .fst) (λ _ → id)` places the identity
    function in the image, giving the identity morphism
  - `associator f g : fiber yon (λ w → yon g w ∘ yon f w)`
    closes the image under composition, giving `f ⨾ g`

From these, both unit laws and associativity are derived by
injectivity of the embedding. For instance, `f ⨾ idn` and `f`
both represent the same function (since `repr idn = id`), so
they're equal. Both `(f ⨾ g) ⨾ h` and `f ⨾ (g ⨾ h)` represent
`repr h ∘ repr g ∘ repr f`, so they inhabit the same fiber;
since fibers of an embedding are propositions, they must be
equal.

Two further fields make the definition self-dual:

  - `repr-op-emb` asserts that pre-composition
    `f ↦ (f ⨾ _)` is an embedding
  - `yon-emb` asserts that post-composition
    `f ↦ (_ ⨾ f)` is an embedding

Both are propositions (`is-embedding` is always a proposition).
The opposite category swaps `repr` with the derived `repr-op`
and exchanges the two embedding fields: pre-composition in the
opposite is post-composition in the original, and vice versa.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv
open import Core.Transport using (is-prop→PathP; is-contr→is-prop)
open import Core.Trait.Trunc using (Π-is-prop; Πi-is-prop)
open import Core.Function.Base
open import Core.Function.Embedding

record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    repr : ∀ {x y} → hom x y ↪ (∀ w → hom w x → hom w y)

  yon
    : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  yon = repr .fst

  yon-op
    : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  yon-op {x} f z g = yon g x f

  field
    unital : ∀ {x} → fiber (yon {x} {x}) (λ _ → id)
    associator
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → fiber yon (λ w → yon g w ∘ yon f w)
    yon-op-emb : ∀ {x y} → is-embedding (yon-op {x} {y})

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  _⨾_ f g = associator f g .fst

  field
    repr-acts
      : ∀ {x y} (h : hom x y) → yon h ≡ (λ w k → k ⨾ h)

  {-# INLINE yon #-}
  {-# INLINE yon-op #-}
  {-# INLINE _⨾_ #-}

module Cat {o} {h} (C : category o h) where
  open category C

```

## Derived definitions

The representation map `repr .fst` is an embedding, so its fibers
are propositions. This gives injectivity: equal representations
imply equal morphisms. All the category laws reduce to showing
that two representations coincide, then applying injectivity.

```agda
  private module R {x} {y} = Emb (repr {x} {y})

  composite : ∀ {x y z} → hom x y → hom y z → hom x z → Type (o ⊔ h)
  composite f g s = yon s ≡ λ w → yon g w ∘ yon f w

  is-composable : ∀ {x y z} → hom x y → hom y z → Type (o ⊔ h)
  is-composable {x} {z} f g = fiber yon (λ w → yon g w ∘ yon f w)

  composite-contr
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr (is-composable f g)
  composite-contr f g .center = associator f g
  composite-contr f g .paths =
    repr .snd (λ w → repr .fst g w ∘ repr .fst f w)
      (associator f g)

  idn : ∀ {x} → hom x x
  idn = unital .fst

  yon≡seq
    : ∀ {x y} (h : hom x y) (w : ob) (k : hom w x)
    → yon h w k ≡ k ⨾ h
  yon≡seq h w k i = repr-acts h i w k

  repr-fiber : ∀ {x y} (h : hom x y) → fiber yon (λ w k → k ⨾ h)
  repr-fiber h .fst = h
  repr-fiber h .snd = repr-acts h

  {-# DISPLAY category.associator _ f g .fst = f ⨾ g #-}
  {-# DISPLAY category.unital _ {x} .fst = idn {x} #-}

  repr-op
    : ∀ {x y} → hom x y ↪ (∀ z → hom y z → hom x z)
  repr-op .fst = yon-op
  repr-op .snd = yon-op-emb

  is-composable-is-prop
    : ∀ {x y z} (f : hom x y) (g : hom y z) → is-prop (is-composable f g)
  is-composable-is-prop f g = is-contr→is-prop (composite-contr f g)

  yon-ind
    : ∀ {ℓ'} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z) → composite f g s → Type ℓ')
    → P (f ⨾ g) (associator f g .snd)
    → ∀ s q → P s q
  yon-ind f g P base m p =
    transp (λ i → P (path i .fst) (path i .snd)) i0 base
    where
      path : associator f g ≡ (m , p)
      path = composite-contr f g .paths (m , p)

  yon-op-inj
    : ∀ {x y} {f g : hom x y} → yon-op f ≡ yon-op g → f ≡ g
  yon-op-inj {f = f} {g} p =
    pcom (λ i → unital .snd i _ f) (λ i → p i _ idn)
      (λ i → unital .snd i _ g)

  yon-st
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → yon (f ⨾ g) ≡ (λ w → yon g w ∘ yon f w)
  yon-st f g = associator f g .snd

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

## Right unit law

`coh f idn .snd` gives a path from `repr .fst (f ⨾ idn)` to
`repr .fst idn ∘ repr .fst f`. Then `unital .snd` collapses
`repr .fst idn` to `id`, recovering `repr .fst f`.

```agda
  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  unitr f =
    R.inj (associator f idn .snd
      ∙ λ i w h → unital .snd i w (yon f w h))
```

## Left unit law

```agda


  unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  unitl f =
    R.inj (associator idn f .snd
      ∙ λ i w h → repr .fst f w (unital .snd i w h))

  op-coh
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → fiber (yon {x} {z}) (λ w → _⨾ g ∘ _⨾ f)
  op-coh {x} {y} {z} f g .fst = f ⨾ g
  op-coh {x} {y} {z} f g .snd =
    associator f g .snd
    ∙ (λ i w k → repr-acts g i w (repr-acts f i w k))

```

## Associativity

Both `(f ⨾ g) ⨾ h` and `f ⨾ (g ⨾ h)` live in a fiber over the
fully-decomposed representation
`λ w a → repr .fst h w (repr .fst g w (repr .fst f w a))`.
We build each fiber element and then use propositional fibers to
identify them.

```agda
  assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (repr .snd _ lhs rhs)
    where
      decomposed : ∀ v → hom v _ → hom v _
      decomposed v a =
        repr .fst h v (repr .fst g v (repr .fst f v a))

      lhs : fiber (repr .fst) decomposed
      lhs .fst = (f ⨾ g) ⨾ h
      lhs .snd =
        associator (f ⨾ g) h .snd
        ∙ λ i v a →
          repr .fst h v (associator f g .snd i v a)

      rhs : fiber (repr .fst) decomposed
      rhs .fst = f ⨾ (g ⨾ h)
      rhs .snd =
        associator f (g ⨾ h) .snd
        ∙ λ i v a →
          associator g h .snd i v (repr .fst f v a)

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
    → composite f g s → composite g h r → s ⨾ h ≡ f ⨾ r
  conj f g h α β =
    sym (ap (_⨾ h) (cast-path α)) ∙ assoc f g h ∙ ap (f ⨾_) (cast-path β)

  op-composite : ∀ {x y z} → hom z y → hom y x → hom z x → Type (o ⊔ h)
  op-composite f g s = yon-op s ≡ λ w → yon-op f w ∘ yon-op g w

  is-op-composable : ∀ {x y z} → hom z y → hom y x → Type (o ⊔ h)
  is-op-composable f g = fiber yon-op (λ w → yon-op f w ∘ yon-op g w)

  op-composite-contr
    : ∀ {x y z} (f : hom z y) (g : hom y x)
    → is-contr (is-op-composable f g)
  op-composite-contr {x} {y} {z} f g .center =
    f ⨾ g , λ i w k → chain w k i
    where
      chain : ∀ w (k : hom x w) → yon k z (f ⨾ g) ≡ yon (yon k y g) z f
      chain w k =
        (λ j → repr-acts k j z (f ⨾ g))
        ∙ assoc f g k
        ∙ ap (f ⨾_) (sym (λ j → repr-acts k j y g))
        ∙ sym (λ j → repr-acts (yon k y g) j z f)
  op-composite-contr {x} {y} {z} f g .paths =
    yon-op-emb (λ w → yon-op f w ∘ yon-op g w)
      (op-composite-contr f g .center)

  yon-op-ind
    : ∀ {ℓ'} {x y z} (f : hom z y) (g : hom y x)
    → (P : (s : hom z x) → op-composite f g s → Type ℓ')
    → P (f ⨾ g) (op-composite-contr f g .center .snd)
    → ∀ m p → P m p
  yon-op-ind f g P base m p =
    transp (λ i → P (path i .fst) (path i .snd)) i0 base
    where
      path : op-composite-contr f g .center ≡ (m , p)
      path = op-composite-contr f g .paths (m , p)

  op-cast-path
    : ∀ {x y z} {f : hom z y} {g : hom y x} {s : hom z x}
    → op-composite f g s → f ⨾ g ≡ s
  op-cast-path {f = f} {g} α =
    ap fst (op-composite-contr f g .paths (_ , α))

  op-cast-pathp
    : ∀ {x y z} {f : hom z y} {g : hom y x} {s : hom z x}
    → (α : op-composite f g s)
    → PathP (λ i → op-composite f g (op-cast-path α i))
        (op-composite-contr f g .center .snd) α
  op-cast-pathp {f = f} {g} α =
    ap snd (op-composite-contr f g .paths (_ , α))

```

## Repr-op injectivity

If `f` and `g` compose identically with every morphism on the
right, they must be equal. We instantiate at `idn` and cancel
the units.

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

## Contravariant representation

The contravariant embedding sends a morphism to its
pre-composition action. The embedding property is the
axiom `yon-emb`.

```agda
  private
    module Rop {x} {y} = Emb (repr-op {x} {y})

  repr-fiber-op : ∀ {x y} (h : hom x y) → fiber yon-op (λ z g → h ⨾ g)
  repr-fiber-op {x} h .fst = h
  repr-fiber-op {x} h .snd i z g = repr-acts g i x h
```


## Derived op-structure

The unit and coherence witnesses for `repr-op` follow from
`unitl` and `assoc`.

```agda
  unital-op : ∀ {x} → fiber (repr-op {x} {x} .fst) (λ _ → id)
  unital-op {x} .fst = idn
  unital-op {x} .snd i z g =
    ((λ j → repr-acts g j x idn) ∙ unitl g) i

  coh-op
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → fiber (repr-op .fst)
        (λ w → repr-op .fst f w ∘ repr-op .fst g w)
  coh-op {x} {y} {z} f g .fst = f ⨾ g
  coh-op {x} {y} {z} f g .snd = λ i w h → chain w h i where
    chain : ∀ w (h : hom z w) → yon h x (f ⨾ g) ≡ yon (yon h y g) x f
    chain w h =
      (λ j → repr-acts h j x (f ⨾ g))
      ∙ assoc f g h
      ∙ ap (f ⨾_) (sym (λ j → repr-acts h j y g))
      ∙ sym (λ j → repr-acts (yon h y g) j x f)

```

## The opposite category

The opposite swaps `repr` with the derived `repr-op` and
exchanges the two embedding fields. Pre-composition in `op`
is post-composition in `C` (so `op.repr-op-emb = C.yon-emb`),
and post-composition in `op` is pre-composition in `C`
(so `op.yon-emb = C.repr-op-emb`).

```agda
  op : category o h
  op .category.ob          = ob
  op .category.hom         = λ x y → hom y x
  op .category.repr        = repr-op
  op .category.unital      = unital-op
  op .category.associator  = flip coh-op
  op .category.yon-op-emb  = repr .snd
  op .category.repr-acts h = λ i w k → repr-acts k i _ h
  {-# INLINE op #-}

module _ {o h} (C : category o h) where
  private module C = category C

  private
    module D = Cat (Cat.op C)
    module CC = Cat C

  assoc-is-prop
    : is-prop (∀ {x y z} (f : C.hom x y) (g : C.hom y z)
              → fiber C.yon (λ w → C.yon g w ∘ C.yon f w))
  assoc-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → C.repr .snd _

  op-invo : Cat.op (Cat.op C) ≡ C
  op-invo i .category.ob         = C.ob
  op-invo i .category.hom        = C.hom
  op-invo i .category.repr       = C.repr
  op-invo i .category.unital     =
    is-prop→PathP (λ _ → C.repr .snd (λ _ → id))
      D.unital-op C.unital i
  op-invo i .category.associator =
    is-prop→PathP (λ _ → assoc-is-prop)
      (flip D.coh-op) C.associator i
  op-invo i .category.yon-op-emb = C.yon-op-emb
  op-invo i .category.repr-acts  = {! !}

```
