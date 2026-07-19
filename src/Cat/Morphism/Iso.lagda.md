Lane Biocini
July 2026

Isomorphisms over a `Cat.Type` category: the inverse pair, identity
and composition of isomorphisms, uniqueness of inverses, and the
biinvertibility comparison.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Morphism.Iso where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base

open import Cat.Type
open import Cat.Base
open import Cat.Morphism

module iso {o h} (C : category o h) where
  open category C
  open theory C
  open morphism C
```

An isomorphism consists of a morphism `f` together with an inverse
`g` satisfying both `f ⨾ g ≡ idn` (left inverse) and `g ⨾ f ≡ idn`
(right inverse).

```agda
  module _ {x y} (f : hom x y) where
    left-inverse : hom y x → Type h
    left-inverse g = f ⨾ g ≡ idn _

    right-inverse : hom y x → Type h
    right-inverse g = g ⨾ f ≡ idn _

    is-iso : Type h
    is-iso = Σ g ∶ hom y x , left-inverse g × right-inverse g

  _≅_ : ob → ob → Type h
  x ≅ y = Σ f ∶ hom x y , is-iso f
  infix 4 _≅_
```

The identity is an isomorphism by `unitl` and `unitr`; symmetry swaps
the inverse and its witnesses.

```agda
  idn-iso : ∀ {x} → is-iso (idn x)
  idn-iso {x} = idn x , unitl (idn x) , unitr (idn x)

  iso-refl : ∀ {x} → x ≅ x
  iso-refl {x} = idn x , idn-iso

  iso-sym : ∀ {x y} → x ≅ y → y ≅ x
  iso-sym (f , g , p , q) = g , f , q , p
```

Composing isomorphisms requires associativity and whiskering to
shuttle the inverse pair through the composite. The left inverse
proof chains
`(f ⨾ f') ⨾ (g' ⨾ g) ≡ f ⨾ (f' ⨾ (g' ⨾ g)) ≡ f ⨾ ((f' ⨾ g') ⨾ g)`
`≡ f ⨾ (idn ⨾ g) ≡ f ⨾ g ≡ idn`, and symmetrically for the right
inverse.

```agda
  iso-cat : ∀ {x y z} → x ≅ y → y ≅ z → x ≅ z
  iso-cat (f , g , p , q) (f' , g' , p' , q') = f ⨾ f'
    , g' ⨾ g
    , pcom (assoc f f' (g' ⨾ g))
           (f ◃ assoc f' g' g)
           (pcom (f ◃ (sym p' ▹ g)) (f ◃ unitl g) p)
    , pcom (assoc g' g (f ⨾ f'))
           (g' ◃ assoc g f f')
           (pcom (g' ◃ (sym q ▹ f')) (g' ◃ unitl f') q')
```

## Inverse uniqueness

Any two one-sided inverses of `f` agree: a left inverse `s` equals a
right inverse `r` by sandwiching `f ⨾ s ≡ idn` between `r` and the
unit laws.

```agda
  module _ {x y} {f : hom x y} (iso : is-iso f) where
    private
      g = iso .fst

    inv-unique
      : {s r : hom y x}
      → left-inverse f s → right-inverse f r → s ≡ r
    inv-unique {s} {r} p' q' =
      pcom (unitl s) (sym q' ▹ s)
        (pcom (assoc r f s) (r ◃ p') (unitr r))
```

Isomorphisms have both a section and a retraction, so they are both
mono and epi.

```agda
  iso→section
    : ∀ {x y} {f : hom x y}
    → is-iso f → has-section f
  iso→section (g , p , _) = g , p

  iso→retraction
    : ∀ {x y} {f : hom x y}
    → is-iso f → has-retraction f
  iso→retraction (g , _ , q) = g , q

  iso→mono
    : ∀ {x y} {f : hom x y}
    → is-iso f → is-mono f
  iso→mono i = section→mono (iso→section i)

  iso→epi
    : ∀ {x y} {f : hom x y}
    → is-iso f → is-epi f
  iso→epi i = retraction→epi (iso→retraction i)
```

## Biinvertibility

A morphism is biinvertible if it has both a section and a retraction.
Every isomorphism is biinvertible, and conversely: the section and
retraction agree by `inv-unique`.

```agda
  is-biinv : ∀ {x y} → hom x y → Type h
  is-biinv f = has-section f × has-retraction f

  iso→biinv
    : ∀ {x y} {f : hom x y}
    → is-iso f → is-biinv f
  iso→biinv i = iso→section i , iso→retraction i

  biinv→iso
    : ∀ {x y} {f : hom x y}
    → is-biinv f → is-iso f
  biinv→iso {f = f} ((s , fs) , (r , rf)) =
    s , fs , ap (_⨾ f) s≡r ∙ rf
    where
      s≡r : s ≡ r
      s≡r =
        s             ≡˘⟨ unitl s ⟩
        idn _ ⨾ s     ≡˘⟨ rf ▹ s ⟩
        (r ⨾ f) ⨾ s   ≡⟨ sym (assoc r f s) ⟩
        r ⨾ (f ⨾ s)   ≡⟨ r ◃ fs ⟩
        r ⨾ idn _     ≡⟨ unitr r ⟩
        r ∎
```
