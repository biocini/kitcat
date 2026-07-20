Lane Biocini
July 2026

Isomorphisms over a `Cat.Type` category: the inverse pair, identity
and composition of isomorphisms, uniqueness of inverses, the
biinvertibility comparison, and the path bridge — object paths as
isomorphisms and hom-`PathP`s as classical squares, native cubical
throughout. There is no J anywhere in the bridge: the transported
identity is a transp-filler package whose laws are lines, so
nothing ever eliminates at `refl` and no `idtoiso-refl` patch
lemma exists to need.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Iso where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.Base using (coe01; coe-filler)

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

## The path bridge

An object path carries an isomorphism: the transported identity
in each direction, with the transp-fillers kept first-class —
`to-fill` has the fil cap at `i0` and the com at `i1`, both
definitional, so every law about `to` is stated and proved as a
line and the `refl` case is never special. The left inverse law
runs in the constant family `hom x x` — the pointwise composite
of the two fillers, closed by the unit — and the right inverse
law compares the pointwise composite against the identity
diagonal over `λ i → hom (p i) (p i)` by `pathp-ends`.

```agda
  module path-iso {x y : ob} (p : x ≡ y) where
    to : hom x y
    to = coe01 (λ i → hom x (p i)) (idn x)

    to-fill : PathP (λ i → hom x (p i)) (idn x) to
    to-fill = coe-filler (λ i → hom x (p i)) (idn x)

    from : hom y x
    from = coe01 (λ i → hom (p i) x) (idn x)

    from-fill : PathP (λ i → hom (p i) x) (idn x) from
    from-fill = coe-filler (λ i → hom (p i) x) (idn x)

    to-from : to ⨾ from ≡ idn x
    to-from = sym (λ i → to-fill i ⨾ from-fill i) ∙ unitl (idn x)

    from-to : from ⨾ to ≡ idn y
    from-to =
      pathp-ends {A = λ i → hom (p i) (p i)}
        (λ i → from-fill i ⨾ to-fill i)
        (λ i → idn (p i))
        (unitl (idn x))

    path→iso : x ≅ y
    path→iso = to , from , to-from , from-to
```

## Dependent paths as squares

A `PathP` of homs over object paths reads as the classical
commuting square through the transported identities: the two
whiskers `f ⨾ to-fill(q)` and `to-fill(p) ⨾ P` run in the one
family `hom x (q i)`, the unit laws join their `i0`-ends, and
`pathp-ends` closes the square. This is the map consumers use;
the equivalence between the two presentations is comparison
material for a Properties module, if ever wanted.

```agda
  hom-pathp→square
    : ∀ {x x' y y'} (p : x ≡ x') (q : y ≡ y')
      {f : hom x y} {g : hom x' y'}
    → PathP (λ i → hom (p i) (q i)) f g
    → f ⨾ path-iso.to q ≡ path-iso.to p ⨾ g
  hom-pathp→square p q {f} P =
    pathp-ends {A = λ i → hom _ (q i)}
      (λ i → f ⨾ path-iso.to-fill q i)
      (λ i → path-iso.to-fill p i ⨾ P i)
      (unitr f ∙ sym (unitl f))
```
