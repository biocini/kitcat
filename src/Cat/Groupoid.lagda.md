Lane Biocini
March 2026

The path groupoid of a type, as a Cat.Virtual category.

For any type `A`, the yon-unbiased embedding `emb q w p z r = pcom (sym p) q r`
gives the ternary composition structure. The identity `refl` absorbs via
`Path.unitl` and `Path.unitr`. Composition is path concatenation. Interchange
follows from `pcom-split-l` and `pcom-split-r`.

The `category` record is from `Cat.Virtual`. Since Cat.Virtual imports
`Core.Groupoid` (for `yon-unbiased.emb` and `emb-equiv`), the instance
lives here to avoid a circular dependency.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Groupoid where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv.Base using (is-equiv; eqv-fibers; iso→equiv)
open import Core.Groupoid
open import Cat.Virtual
```

## Coherence helpers

These are the pcom coherences needed for the interchange proof. They
live in `Core.Coherence` but that module has unfinished pentagon holes,
so we reproduce the needed lemmas here.

```agda
private
  module _ {u} {A : Type u} where
    inv-sides-filler
      : {x y z : A} (p : x ≡ y) (q : x ≡ z)
      → Square p q (sym q) (sym p)
    inv-sides-filler {x = x} p q i j =
      hcom (∂ i ∨ ∂ j) λ where
        k (i = i0) → p (k ∧ j)
        k (i = i1) → q (~ j ∧ k)
        k (j = i0) → q (i ∧ k)
        k (j = i1) → p (~ i ∧ k)
        k (k = i0) → x

    pcom-leftright
      : {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → pcom refl p q ≡ pcom (sym p) q refl
    pcom-leftright p q i j =
      hcom (∂ j) λ where
        k (j = i0) → p (i ∧ (~ k))
        k (j = i1) → q (k ∨ i)
        k (k = i0) → inv-sides-filler q (sym p) (~ i) j

    pcom-split-l
      : {w x y z : A} (p : w ≡ x) (q : x ≡ y)
        (r : y ≡ z)
      → pcom (sym p) q r
      ≡ pcom refl (pcom (sym p) q refl) r
    pcom-split-l p q r j i =
      hcom (∂ i) λ where
        k (i = i0) → p (~ j ∧ ~ k)
        k (i = i1) → r k
        k (k = i0) → pfil (sym p) q refl i j

    pcom-split-r
      : {w x y z : A} (p : w ≡ x) (q : x ≡ y)
        (r : y ≡ z)
      → pcom (sym p) q r
      ≡ pcom (sym p) (pcom refl q r) refl
    pcom-split-r p q r j i =
      hcom (∂ i) λ where
        k (i = i0) → p (~ k)
        k (i = i1) → r (j ∨ k)
        k (k = i0) → pfil refl q r i j
```

## The path groupoid

`emb` is `yon-unbiased.emb` specialized to the constant type family.
Since `PathP (λ _ → A) x y` is definitionally `x ≡ y`, the types align
without coercion.

```agda
module _ {u} (A : Type u) where
  private
    E : {x y : A} → x ≡ y
      → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
    E = yon-unbiased.emb {A = λ _ → A}

    E-equiv : {x y : A} → is-equiv (E {x} {y})
    E-equiv = yon-unbiased.emb-equiv {A = λ _ → A}
```

### Unit

The identity is `refl`. The left action `λ h → E refl x refl z h` equals
`λ h → pcom refl refl h`, which is `λ h → refl ∙ h`. This is an
equivalence via `Path.unitl`. The right action `λ g → E refl w g x refl`
equals `λ g → pcom (sym g) refl refl`. By `pcom-leftright` this equals
`pcom refl g refl = g ∙ refl`, so the equivalence follows from `Path.unitr`.

Yon-idempotency `E refl x refl x refl ≡ refl` follows from `pcom.unit`.

```agda
    left-act : {x z : A} (h : x ≡ z)
      → E refl x refl z h ≡ h
    left-act = Path.unitl

    right-act : {x w : A} (g : w ≡ x)
      → E refl w g x refl ≡ g
    right-act g =
      sym (pcom-leftright g refl) ∙ Path.unitr g

    left-eqv : {x : A} {z : A}
      → is-equiv
          (λ (h : x ≡ z) → E refl x refl z h)
    left-eqv = iso→equiv
      (λ h → pcom refl refl h)
      id left-act left-act .snd

    right-eqv : {x : A} {w : A}
      → is-equiv
          (λ (g : w ≡ x) → E refl w g x refl)
    right-eqv {x} {w} =
      iso→equiv fwd id right-act right-act .snd
      where
        fwd : w ≡ x → w ≡ x
        fwd g = E refl w g x refl

    gpd-unit : {x : A}
      → Σ e ∶ x ≡ x
      , ( (∀ {z} → is-equiv
              (λ (h : x ≡ z) → E e x e z h))
        × (∀ {w} → is-equiv
              (λ (g : w ≡ x) → E e w g x e)))
      × (E e x e x e ≡ e)
    gpd-unit = refl
      , (left-eqv , right-eqv)
      , pcom.unit refl
```

### Compose contractibility

Since `E` is an equivalence, every fiber `Σ s, E s ≡ T` is contractible.
The target `T = λ w a v b → E f w a v (noy g v b)` is an element of
the codomain of `E`, so `eqv-fibers E-equiv T` gives contractibility.

```agda
    gpd-compose-contr
      : {x y z : A} (f : x ≡ y) (g : y ≡ z)
      → is-contr
          (Σ s ∶ x ≡ z
          , E s
            ≡ (λ w a v b →
                E f w a v (E g _ refl v b)))
    gpd-compose-contr f g =
      eqv-fibers E-equiv
        (λ w a v b → E f w a v (E g _ refl v b))
```

### Interchange

The interchange equation
`E f w a v (E g _ refl v b) ≡ E g w (E f w a _ refl) v b`
expands to
`pcom (sym a) f (pcom refl g b) ≡ pcom (sym (pcom (sym a) f refl)) g b`.

The proof chains `pcom-split-l`, `pcom-leftright`, and `sym pcom-split-r`.

```agda
    gpd-interchange
      : {x y z : A} (f : x ≡ y) (g : y ≡ z)
        (w : A) (a : w ≡ x) (v : A) (b : z ≡ v)
      → E f w a v (E g _ refl v b)
      ≡ E g w (E f w a _ refl) v b
    gpd-interchange f g w a v b =
      pcom-split-l a f (pcom refl g b)
      ∙ pcom-leftright
          (pcom (sym a) f refl) (pcom refl g b)
      ∙ sym (pcom-split-r
              (pcom (sym a) f refl) g b)
```

### Yon-eval

`yon f x refl = E f x refl y refl = pcom refl f refl ≡ f` by `pcom.unit`.

```agda
    gpd-yon-eval
      : {x y : A} (f : x ≡ y)
      → E f x refl y refl ≡ f
    gpd-yon-eval f = pcom.unit f
```

### Assembly

```agda
  ∞-groupoid : category u u
  ∞-groupoid .category.ob = A
  ∞-groupoid .category.hom = _≡_
  ∞-groupoid .category.emb = E
  ∞-groupoid .category.unit = gpd-unit
  ∞-groupoid .category.compose-contr =
    gpd-compose-contr
  ∞-groupoid .category.interchange =
    gpd-interchange
  ∞-groupoid .category.yon-eval =
    gpd-yon-eval
```
