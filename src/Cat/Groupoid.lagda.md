Lane Biocini
March 2026

The path groupoid of a type, as a Cat.Virtual category.

For any type `A`, the yon-unbiased embedding `emb q w p z r = pcom (sym p) q r`
gives the ternary composition structure. The identity `refl` absorbs via
`Path.unitl` and `Path.unitr`. Composition is path concatenation. Interchange
follows from `pcom.lsplit` and `pcom.rsplit`.

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
open import Core.Groupoid.Virtual
open import Cat.Virtual
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
equals `λ g → pcom (sym g) refl refl`. By `pcom.lr` this equals
`pcom refl g refl = g ∙ refl`, so the equivalence follows from `Path.unitr`.

Yon-idempotency `E refl x refl x refl ≡ refl` follows from `pcom.unit`.

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

    gpd-unit : {x : A}
      → Σ e ∶ x ≡ x
      , (∀ {z} → is-equiv
              (λ (h : x ≡ z) → E e x e z h))
      × (∀ {w} → is-equiv
              (λ (g : w ≡ x) → E e w g x e))
    gpd-unit = refl
      , left-eqv , right-eqv
```

### Compose contractibility

Since `E` is an equivalence, every fiber `Σ s, E s ≡ T` is contractible
(`eqv-fibers`). The pointwise version follows: the center is the same
path, and the contraction converts through `funext`/`happly`.

```agda
    gpd-compose-contr
      : {x y z : A} (f : x ≡ y) (g : y ≡ z)
      → is-contr
          (Σ s ∶ x ≡ z
          , ∀ w (a : w ≡ x) v (b : z ≡ v)
            → E s w a v b
            ≡ E f w a v (E g _ refl v b))
    gpd-compose-contr {x} {y} {z} f g = c'
      where
        T : ∀ w → w ≡ x → ∀ v → z ≡ v → w ≡ v
        T w a v b = E f w a v (E g _ refl v b)

        ext-contr : is-contr (Σ s ∶ x ≡ z , E s ≡ T)
        ext-contr = eqv-fibers E-equiv T

        s₀ : x ≡ z
        s₀ = ext-contr .center .fst

        ext-eq : E s₀ ≡ T
        ext-eq = ext-contr .center .snd

        pw₀ : ∀ w (a : w ≡ x) v (b : z ≡ v)
          → E s₀ w a v b ≡ T w a v b
        pw₀ w a v b i = ext-eq i w a v b

        c' : is-contr
          (Σ s ∶ x ≡ z
          , ∀ w (a : w ≡ x) v (b : z ≡ v)
            → E s w a v b ≡ T w a v b)
        c' .center = s₀ , pw₀
        c' .paths (s , pw) = path
          where
            ext-path : E s ≡ T
            ext-path = funext λ w → funext λ a →
              funext λ v → funext λ b → pw w a v b

            total-path
              : (s₀ , ext-eq) ≡ (s , ext-path)
            total-path = ext-contr .paths (s , ext-path)

            s-path : s₀ ≡ s
            s-path = ap fst total-path

            path
              : (s₀ , pw₀) ≡ (s , pw)
            path i = s-path i , λ w a v b j →
              let
                ext-over
                  : PathP
                      (λ i → E (s-path i) ≡ T)
                      ext-eq ext-path
                ext-over = ap snd total-path
              in ext-over i j w a v b
```

### Interchange

The interchange equation
`E f w a v (E g _ refl v b) ≡ E g w (E f w a _ refl) v b`
expands to
`pcom (sym a) f (pcom refl g b) ≡ pcom (sym (pcom (sym a) f refl)) g b`.

The proof chains `pcom.lsplit`, `pcom.lr`, and `sym pcom.rsplit`.

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
