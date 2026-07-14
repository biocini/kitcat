Lane Biocini
March 2026

The path groupoid of a type, as a Cat.Type category.

For any type `A`, the yon-unbiased embedding
`emb q w p z r = pcom (sym p) q r` gives the ternary
composition structure. The identity `refl` absorbs via
`Path.unitl` and `Path.unitr`. Composition is path
concatenation. Interchange follows from `pcom.lsplit`
and `pcom.rsplit`.

The `category` record is from `Cat.Type`; the ternary embedding
and its equivalence are from `Core.Groupoid.Virtual`. The
instance bridges the two, so it lives in its own module and keeps
`Cat.Type` free of the groupoid dependency.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Groupoid where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv.Base using (is-equiv; eqv-fibers; iso→equiv)
open import Core.Equiv.Properties using (comp-equiv)
open import Core.Groupoid.Virtual
open import Cat.Type
```

## The path groupoid

`E` is `yon-unbiased.emb` specialized to the constant
type family. Since `PathP (λ _ → A) x y` is
definitionally `x ≡ y`, the types align without coercion.

```agda
module _ {u} (A : Type u) where
  private
    E : {x y : A} → x ≡ y
      → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
    E = yon-unbiased.emb {A = λ _ → A}

    E-equiv : {x y : A} → is-equiv (E {x} {y})
    E-equiv = yon-unbiased.emb-equiv {A = λ _ → A}
```

### The composite view

`category-structure`'s `emb` lands in the uncurried composite
`(γ : ctx x y) → res γ`, a Π over `ctx x y = cofam x × fam y`.
`uncurryE` glues the curried `E` into that view and `curryE`
inverts it; both round-trips hold definitionally (function eta one
way, `Σ` eta the other), so `uncurryE` is an equivalence. The
structure's `emb f = uncurryE (E f)` then inherits `E`'s.

```agda
    uncurryE : {x y : A}
      → (∀ w → w ≡ x → ∀ v → y ≡ v → w ≡ v)
      → (γ : (Σ w ∶ A , w ≡ x) × (Σ v ∶ A , y ≡ v))
      → γ .fst .fst ≡ γ .snd .fst
    uncurryE G γ =
      G (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

    curryE : {x y : A}
      → ((γ : (Σ w ∶ A , w ≡ x) × (Σ v ∶ A , y ≡ v))
          → γ .fst .fst ≡ γ .snd .fst)
      → ∀ w → w ≡ x → ∀ v → y ≡ v → w ≡ v
    curryE F w a v b = F ((w , a) , (v , b))

    uncurryE-equiv : {x y : A} → is-equiv (uncurryE {x} {y})
    uncurryE-equiv =
      iso→equiv uncurryE curryE (λ _ → refl) (λ _ → refl) .snd
```

### Unit

The identity is `refl`. The left action
`λ h → E refl x refl z h` equals
`λ h → pcom refl refl h`, which is `λ h → refl ∙ h`.
This is an equivalence via `Path.unitl`. The right action
`λ g → E refl w g x refl` equals
`λ g → pcom (sym g) refl refl`. By `pcom.lr` this equals
`pcom refl g refl = g ∙ refl`, so the equivalence follows
from `Path.unitr`. As `category-structure` operations,
`pre (idn x)` and `post (idn x)` reduce to these two actions, so
`left-eqv` and `right-eqv` are exactly `unit-eqvl` and
`unit-eqvr`.

```agda
    left-act : {x z : A} (h : x ≡ z)
      → E refl x refl z h ≡ h
    left-act = Path.unitl

    right-act : {x w : A} (g : w ≡ x)
      → E refl w g x refl ≡ g
    right-act g =
      sym (pcom.lr g refl) ∙ Path.unitr g

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
```

### Compose contractibility

`emb f = uncurryE (E f)` is `E` followed by the currying
equivalence, hence itself an equivalence, so every fibre
`fiber emb T` is contractible (`eqv-fibers`). The `compose-contr`
axiom is that at `T = emb f · g`.

```agda
    emb-equiv : {x y : A}
      → is-equiv (λ (f : x ≡ y) → uncurryE (E f))
    emb-equiv = comp-equiv E-equiv uncurryE-equiv
```

### Interchange

The interchange equation
`E f w a v (E g _ refl v b)
  ≡ E g w (E f w a _ refl) v b`
expands to
`pcom (sym a) f (pcom refl g b)
  ≡ pcom (sym (pcom (sym a) f refl)) g b`.

The proof chains `pcom.lsplit`, `pcom.lr`, and
`sym pcom.rsplit`. Through the composite view,
`emb f ((w , a) , (v , pre g b))` is the left-hand side and
`emb g ((w , post f a) , (v , b))` the right, so this is the
`interchange` axiom verbatim.

```agda
    gpd-interchange
      : {x y z : A} (f : x ≡ y) (g : y ≡ z)
        (w : A) (a : w ≡ x) (v : A) (b : z ≡ v)
      → E f w a v (E g _ refl v b)
      ≡ E g w (E f w a _ refl) v b
    gpd-interchange f g w a v b =
      pcom.lsplit a f (pcom refl g b)
      ∙ pcom.lr
          (pcom (sym a) f refl) (pcom refl g b)
      ∙ sym (pcom.rsplit
              (pcom (sym a) f refl) g b)
```

### Post-eval

`post f (idn x) = E f x refl y refl
  = pcom refl f refl ≡ f` by `pcom.unit`.

```agda
    gpd-post-eval
      : {x y : A} (f : x ≡ y)
      → E f x refl y refl ≡ f
    gpd-post-eval f = pcom.unit f
```

### Assembly

The structure fixes `hom = _≡_`, `idn = refl`, and the composite
embedding `emb f = uncurryE (E f)`. The five axioms read off the
pieces above: `compose-contr` from `emb-equiv`, `interchange` and
`post-eval` from the `E`-level lemmas, and the two unit
equivalences from `left-eqv`/`right-eqv`.

```agda
    gpd-structure : category-structure u A
    gpd-structure .category-structure.hom = _≡_
    gpd-structure .category-structure.idn x = refl
    gpd-structure .category-structure.emb f = uncurryE (E f)

    gpd-axioms : category-axioms gpd-structure
    gpd-axioms .category-axioms.compose-contr f g =
      eqv-fibers emb-equiv _
    gpd-axioms .category-axioms.interchange f g {w} a {v} b =
      gpd-interchange f g w a v b
    gpd-axioms .category-axioms.post-eval f = gpd-post-eval f
    gpd-axioms .category-axioms.unit-eqvl = left-eqv
    gpd-axioms .category-axioms.unit-eqvr = right-eqv

  ∞-groupoid : category u u
  ∞-groupoid .category.ob = A
  ∞-groupoid .category.structure = gpd-structure
  ∞-groupoid .category.axioms = gpd-axioms
```
