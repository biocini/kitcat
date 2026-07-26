Lane Biocini, February 2026

# Categories via contractible composition fibers

An experimental reformulation of the category definition from `Cat.Base`.
The key change: `yon` becomes a standalone field rather than extracted
from an embedding bundle, and both `unital` and `associator` assert
contractibility of fibers directly. Two additional propositional fields
(`pres` and `pres-equiv`) witness that `yon` is equivalent to
post-composition, giving rise to a twisted representation
`yon h w k = k ⨾ ψ(h)` where `ψ` is the inverse of `pres-mor`.

The main payoff is that `is-embedding yon` is *derivable* from the other
axioms, and *every* non-data record field is propositional. This means
`op-invo` reduces to matching `ob`/`hom`/`yon` and filling everything
else by `is-prop→PathP`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Base.Exp where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv
open import Core.Transport
  using (is-prop→PathP; is-contr→is-prop; inhab-to-contr→is-prop
        ; is-based-identity-system; IdsJ-based; subst
        ; is-contr-is-prop)
open import Core.Trait.Trunc using (Π-is-prop; Πi-is-prop)
open import Core.Function.Base
open import Core.Function.Embedding

record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
    unital
      : ∀ {x} → is-contr (fiber (yon {x} {x}) (λ _ → id))
    associator
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (fiber yon (λ w → yon g w ∘ yon f w))

  idn : ∀ {x} → hom x x
  idn = unital .center .fst

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  _⨾_ f g = associator f g .center .fst

  yon-op
    : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  yon-op {x} f z g = yon g x f

  coyo
    : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  coyo {x} f w g = g ⨾ f

  field
    pres : ∀ {x y} (f : hom x y)
      → is-contr (fiber (yon {x} {y}) (coyo f))

  pres-mor : ∀ {x y} → hom x y → hom x y
  pres-mor h = pres h .center .fst

  pres-path : ∀ {x y} (h : hom x y) → yon (pres-mor h) ≡ coyo h
  pres-path h = pres h .center .snd

  field
    pres-equiv : ∀ {x y} → is-equiv (pres-mor {x} {y})

  {-# INLINE yon #-}
  {-# INLINE _⨾_ #-}


module Cat {o} {h} (C : category o h) where
  open category C

```

## Composite vocabulary

The composite relation, composability fibers, and their contractibility
are direct restatements of the record fields.

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
  composite-contr = associator

```

## Standard witnesses

```agda

  yon-st
    : ∀ {x y z} (f : hom x y) (g : hom y z) → composite f g (f ⨾ g)
  yon-st f g = associator f g .center .snd

  yon-idn
    : ∀ {x}
    → yon {x} {x} (idn {x}) ≡ (λ (_ : ob) → id)
  yon-idn {x} = unital {x} .center .snd

  yon-idn-pt
    : ∀ {x} (w : ob) (k : hom w x)
    → yon {x} {x} (idn {x}) w k ≡ k
  yon-idn-pt {x} w k i = yon-idn {x} i w k

```

## Identity system eliminators

`cast-path` extracts the morphism equality from a composite witness.
`cast-pathp` gives the dependent path over it.

```agda

  cast-path
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → composite f g s → f ⨾ g ≡ s
  cast-path {f = f} {g} α =
    ap fst (composite-contr f g .paths (_ , α))

  cast-pathp
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → (α : composite f g s)
    → PathP (λ i → composite f g (cast-path α i))
        (yon-st f g) α
  cast-pathp {f = f} {g} α =
    ap snd (composite-contr f g .paths (_ , α))

```

## Induction principle

J-eliminator for composites: given a property that holds for the
canonical composite `f ⨾ g`, it holds for any composite witness.

```agda

  yon-ind
    : ∀ {ℓ'} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z) → composite f g s → Type ℓ')
    → P (f ⨾ g) (yon-st f g)
    → ∀ s q → P s q
  yon-ind f g P base m p =
    transp (λ i → P (path i .fst) (path i .snd)) i0 base
    where
      path : associator f g .center ≡ (m , p)
      path = composite-contr f g .paths (m , p)

```

## Based identity system witness

```agda
  composite-ids
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-based-identity-system (f ⨾ g)
        (composite f g) (yon-st f g)
  composite-ids f g .is-based-identity-system.to-path =
    cast-path
  composite-ids f g .is-based-identity-system.to-path-over =
    cast-pathp

```

## Helpers

```agda

  is-composable-is-prop
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-prop (is-composable f g)
  is-composable-is-prop f g =
    is-contr→is-prop (composite-contr f g)

  {-# DISPLAY category.associator _ f g .center .fst = f ⨾ g #-}
  {-# DISPLAY category.unital _ {x} .center .fst = idn {x} #-}

```

## Unit laws

Both unit laws follow the same pattern: build a composite witness
for `(f, wit)` in the appropriate fiber, then apply `cast-path`.

```agda

  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  unitr {y = y} f = cast-path wit where
    wit : composite f idn f
    wit i w k = yon-idn-pt {y} w (yon f w k) (~ i)

  unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  unitl {x = x} f = cast-path wit where
    wit : composite idn f f
    wit i w k = yon f w (yon-idn-pt {x} w k (~ i))

```

## Associativity via cast-path

Both `(f ⨾ g) ⨾ h` and `f ⨾ (g ⨾ h)` represent the same
triply-decomposed function
`λ w k → yon h w (yon g w (yon f w k))`.
We build a composite witness showing `f ⨾ (g ⨾ h)` is a
composite of `(f ⨾ g)` and `h`, then apply `cast-path`.

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

```

## Whiskering / crossing lemmas

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

## Derived embedding properties

The fiber `fiber yon (yon a)` is contractible for every `a`,
because it transports to the contractible composition fiber
`associator idn a`. This gives injectivity of `yon` and the
full `is-embedding` property.

```agda

  yon-image-contr
    : ∀ {x y} (a : hom x y) → is-contr (fiber yon (yon a))
  yon-image-contr {x} a = subst (λ G → is-contr (fiber yon G))
    (λ i w k → yon a w (yon-idn-pt {x} w k i))
    (associator idn a)

  yon-inj
    : ∀ {x y} {f g : hom x y} → yon f ≡ yon g → f ≡ g
  yon-inj {f = f} {g} p =
    ap fst (is-contr→is-prop (yon-image-contr f)
      (f , refl) (g , sym p))

  is-embedding-yon
    : ∀ {x y} → is-embedding (yon {x} {y})
  is-embedding-yon F = inhab-to-contr→is-prop λ (a , p) →
    subst (λ G → is-contr (fiber yon G)) p
      (yon-image-contr a)

  repr : ∀ {x y} → hom x y ↪ (∀ w → hom w x → hom w y)
  repr .fst = yon
  repr .snd = is-embedding-yon

```

## Repr-based injectivity

If `f` and `g` compose identically with every morphism on the
left, they are equal. Instantiate at `idn` and cancel the units.

```agda

  private module R {x} {y} = Emb (repr {x} {y})

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
pre-composition action.

```agda

  yon-op-inj
    : ∀ {x y} {f g : hom x y} → yon-op f ≡ yon-op g → f ≡ g
  yon-op-inj {x} {y} {f} {g} p =
    pcom (λ i → yon-idn-pt {y} x f i)
      (λ i → p i _ idn)
      (λ i → yon-idn-pt {y} x g i)

```

## Equivalence structure

The `pres` and `pres-equiv` fields together give an equivalence
`pres-mor : hom x y → hom x y` with inverse `ψ`.

```agda

  private
    pres-eqv : ∀ {x y} → hom x y ≃ hom x y
    pres-eqv = pres-mor , pres-equiv

  ψ : ∀ {x y} → hom x y → hom x y
  ψ = Equiv.inv pres-eqv

  φψ : ∀ {x y} (h : hom x y) → pres-mor (ψ h) ≡ h
  φψ = Equiv.counit pres-eqv

  ψφ : ∀ {x y} (h : hom x y) → ψ (pres-mor h) ≡ h
  ψφ = Equiv.unit pres-eqv

```

## Twisted repr-acts

The key derived result: `yon h` agrees with `coyo (ψ h)`, i.e.
`yon h w k = k ⨾ ψ(h)` for all `w`, `k`.

```agda

  yon≡coyo-ψ
    : ∀ {x y} (h : hom x y) → yon h ≡ coyo (ψ h)
  yon≡coyo-ψ h =
    sym (ap yon (φψ h)) ∙ pres-path (ψ h)

  yon-tw
    : ∀ {x y} (h : hom x y) (w : ob) (k : hom w x)
    → yon h w k ≡ k ⨾ ψ h
  yon-tw h w k i = yon≡coyo-ψ h i w k

```

## pres-mor preserves identity

We construct a fiber element `(idn, _) : fiber yon (coyo idn)`
and use contractibility of `pres idn` to equate it with the center.

```agda

  pres-mor-idn : ∀ {x} → pres-mor (idn {x}) ≡ idn {x}
  pres-mor-idn {x} =
    ap fst (is-contr→is-prop (pres idn) (pres idn .center) fib)
    where
      fib : fiber (yon {x} {x}) (coyo (idn {x}))
      fib .fst = idn
      fib .snd = funext λ w → funext λ k →
        yon-idn-pt {x} w k ∙ sym (unitr k)

```

## pres-mor preserves composition

We construct a fiber element showing `pres-mor f ⨾ pres-mor g`
represents `coyo (f ⨾ g)`, then apply contractibility.

```agda

  pres-mor-seq
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → pres-mor (f ⨾ g) ≡ pres-mor f ⨾ pres-mor g
  pres-mor-seq f g =
    ap fst (is-contr→is-prop (pres (f ⨾ g))
      (pres (f ⨾ g) .center) fib)
    where
      fib : fiber yon (coyo (f ⨾ g))
      fib .fst = pres-mor f ⨾ pres-mor g
      fib .snd =
        yon-st (pres-mor f) (pres-mor g)
        ∙ (λ i w k → pres-path g i w (pres-path f i w k))
        ∙ (λ i w k → assoc k f g i)

```

## ψ preserves identity

```agda

  ψ-idn : ∀ {x} → ψ (idn {x}) ≡ idn {x}
  ψ-idn = ap ψ (sym pres-mor-idn) ∙ ψφ idn

```

## ψ preserves composition

```agda

  ψ-seq
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → ψ (f ⨾ g) ≡ ψ f ⨾ ψ g
  ψ-seq f g =
    ap ψ (sym (pres-mor-seq (ψ f) (ψ g)
      ∙ (λ i → φψ f i ⨾ φψ g i)))
    ∙ ψφ (ψ f ⨾ ψ g)

```

## Propositional field witnesses

All non-data fields of `category` are propositional. This is the
key fact that makes `op-invo` achievable via `is-prop→PathP`.

```agda

module _ {o h} (C : category o h) where
  open category C

  unital-is-prop
    : is-prop
        (∀ {x} → is-contr (fiber (yon {x} {x}) (λ _ → id)))
  unital-is-prop =
    Πi-is-prop λ _ → is-contr-is-prop _

  assoc-is-prop
    : is-prop
        (∀ {x y z} (f : hom x y) (g : hom y z)
        → is-contr (fiber yon (λ w → yon g w ∘ yon f w)))
  assoc-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _

  pres-is-prop
    : is-prop
        (∀ {x y} (f : hom x y)
        → is-contr (fiber (yon {x} {y}) (coyo f)))
  pres-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → is-contr-is-prop _

  pres-equiv-is-prop
    : is-prop (∀ {x y} → is-equiv (pres-mor {x} {y}))
  pres-equiv-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ →
    is-equiv-is-prop _

```
