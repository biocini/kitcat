Lane Biocini
March 2026

Universal properties in category theory say "there exists a unique
morphism such that..." — contractibility of a fiber. Contractibility
gives an induction principle: to prove something about all solutions,
it suffices to prove it for the canonical one. This module makes that
pattern explicit over the `category` record at `Cat.Type`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base
open import Core.Transport.J
open import Core.Equiv.Base using (is-equiv; aut; _≃_; Equiv)
open import Core.Function.Embedding using (equiv→lc)
open import Cat.Type
open import Cat.Codep.Coherence
```

## Composite witnesses

A composite witness `f ⨾ g => s` asserts that `s` represents the same
two-sided composite as `f` then `g` — the equality `emb s ≡ emb f · g`
of composites, `emb-comp`'s right-hand side. `cast-path` extracts the
hom-level equality from this `emb`-level witness through the
contractible composition fiber `compose-contr`.

```agda
module Cat {o h} (C : category o h) where
  open category C
  open assoc-tower C

  _⨾_=>_ : ∀ {x y z} → hom x y → hom y z → hom x z → Type (o ⊔ h)
  _⨾_=>_ {x} {y} {z} f g s = emb s ≡ emb f · g

  cast-path
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → f ⨾ g => s → f ⨾ g ≡ s
  cast-path {f = f} {g} {s} α =
    ap fst (compose-contr f g .paths (s , α))
```

## Terminal and initial objects

The simplest universal properties: `hom X T` is contractible for all
`X` (terminal), or `hom I X` is contractible for all `X` (initial).
The induction principle `!-ind` says: to prove `P` for all morphisms
into `T`, prove it for the canonical one. The uniqueness rule
`!-unique` follows from induction at `P = (! ≡_)`.

```agda
  is-terminal : ob → Type (o ⊔ h)
  is-terminal T = ∀ X → is-contr (hom X T)

  module Terminal {T : ob} (term : is-terminal T) where
    ! : ∀ {X} → hom X T
    ! = term _ .center

    !-ind
      : ∀ {u} {X : ob} (P : hom X T → Type u)
      → P !
      → ∀ f → P f
    !-ind = contr-ind (term _)

    !-unique : ∀ {X} (f : hom X T) → ! ≡ f
    !-unique = !-ind (! ≡_) refl

  is-initial : ob → Type (o ⊔ h)
  is-initial I = ∀ X → is-contr (hom I X)

  module Initial {I : ob} (init : is-initial I) where
    ¡ : ∀ {X} → hom I X
    ¡ = init _ .center

    ¡-ind
      : ∀ {u} {X : ob} (P : hom I X → Type u)
      → P ¡
      → ∀ f → P f
    ¡-ind P = contr-ind (init _) P

    ¡-unique : ∀ {X} (f : hom I X) → ¡ ≡ f
    ¡-unique = ¡-ind (¡ ≡_) refl
```

## Products

A product cone over projections `π₁ : P → A` and `π₂ : P → B` from an
object `X` consists of a mediating morphism `m : X → P` together with
composite witnesses `m ⨾ π₁ => f` and `m ⨾ π₂ => g`. The product
condition asks this cone type to be contractible for all `f` and `g`.

- β-rules are the commuting conditions, extracted from the composite
  witnesses;
- the η-rule is uniqueness of the mediating morphism, obtained by
  induction at `Q = ⟨ f , g ⟩ ≡_`;
- induction is the full dependent eliminator, subsuming both.

```agda
  product-cone
    : ∀ {A B P : ob} → hom P A → hom P B
    → (X : ob) → hom X A → hom X B → Type (o ⊔ h)
  product-cone {P = P} π₁ π₂ X f g =
    Sigma (hom X P) λ m → (m ⨾ π₁ => f) × (m ⨾ π₂ => g)

  is-product
    : ∀ {A B P : ob}
      (π₁ : hom P A) (π₂ : hom P B)
    → Type (o ⊔ h)
  is-product π₁ π₂ =
    ∀ {X} (f : hom X _) (g : hom X _)
    → is-contr (product-cone π₁ π₂ X f g)

  module Product
    {A B P : ob} {π₁ : hom P A} {π₂ : hom P B}
    (prod : is-product π₁ π₂)
    where

    ⟨_,_⟩ : ∀ {X} → hom X A → hom X B → hom X P
    ⟨ f , g ⟩ = prod f g .center .fst

    ⟨,⟩-factors₁
      : ∀ {X} (f : hom X A) (g : hom X B)
      → ⟨ f , g ⟩ ⨾ π₁ => f
    ⟨,⟩-factors₁ f g = prod f g .center .snd .fst

    ⟨,⟩-factors₂
      : ∀ {X} (f : hom X A) (g : hom X B)
      → ⟨ f , g ⟩ ⨾ π₂ => g
    ⟨,⟩-factors₂ f g = prod f g .center .snd .snd

    ⟨,⟩-ind
      : ∀ {u X} (f : hom X A) (g : hom X B)
      → (Q : (m : hom X P)
           → m ⨾ π₁ => f → m ⨾ π₂ => g
           → Type u)
      → Q ⟨ f , g ⟩
          (⟨,⟩-factors₁ f g) (⟨,⟩-factors₂ f g)
      → ∀ m α β → Q m α β
    ⟨,⟩-ind f g Q base m α β =
      contr-ind (prod f g)
        (λ where (m , α , β) → Q m α β)
        base (m , α , β)

    ⟨,⟩-β₁
      : ∀ {X} (f : hom X A) (g : hom X B)
      → ⟨ f , g ⟩ ⨾ π₁ ≡ f
    ⟨,⟩-β₁ f g = cast-path (⟨,⟩-factors₁ f g)

    ⟨,⟩-β₂
      : ∀ {X} (f : hom X A) (g : hom X B)
      → ⟨ f , g ⟩ ⨾ π₂ ≡ g
    ⟨,⟩-β₂ f g = cast-path (⟨,⟩-factors₂ f g)

    ⟨,⟩-η
      : ∀ {X} (f : hom X A) (g : hom X B)
      → (m : hom X P)
      → m ⨾ π₁ => f → m ⨾ π₂ => g
      → ⟨ f , g ⟩ ≡ m
    ⟨,⟩-η f g =
      ⟨,⟩-ind f g (λ m _ _ → ⟨ f , g ⟩ ≡ m) refl
```

## Coproducts

Dual of products. A coproduct cocone over injections `ι₁ : A → S` and
`ι₂ : B → S` from an object `X` consists of a mediating morphism
`m : S → X` together with composite witnesses `ι₁ ⨾ m => f` and
`ι₂ ⨾ m => g`. The mediating morphism goes *out* of the coproduct,
reversing the product's direction; the same β/η reading applies.

```agda
  coproduct-cocone
    : ∀ {A B S : ob} → hom A S → hom B S
    → (X : ob) → hom A X → hom B X → Type (o ⊔ h)
  coproduct-cocone {S = S} ι₁ ι₂ X f g =
    Sigma (hom S X) λ m → (ι₁ ⨾ m => f) × (ι₂ ⨾ m => g)

  is-coproduct
    : ∀ {A B S : ob}
      (ι₁ : hom A S) (ι₂ : hom B S)
    → Type (o ⊔ h)
  is-coproduct ι₁ ι₂ =
    ∀ {X} (f : hom _ X) (g : hom _ X)
    → is-contr (coproduct-cocone ι₁ ι₂ X f g)

  module Coproduct
    {A B S : ob} {ι₁ : hom A S} {ι₂ : hom B S}
    (coprod : is-coproduct ι₁ ι₂)
    where
    copair : ∀ {X} → hom A X → hom B X → hom S X
    copair f g = coprod f g .center .fst

    copair-factors₁
      : ∀ {X} (f : hom A X) (g : hom B X)
      → ι₁ ⨾ copair f g => f
    copair-factors₁ f g = coprod f g .center .snd .fst

    copair-factors₂
      : ∀ {X} (f : hom A X) (g : hom B X)
      → ι₂ ⨾ copair f g => g
    copair-factors₂ f g = coprod f g .center .snd .snd

    copair-ind
      : ∀ {u X} (f : hom A X) (g : hom B X)
      → (Q : (m : hom S X)
           → ι₁ ⨾ m => f → ι₂ ⨾ m => g
           → Type u)
      → Q (copair f g)
          (copair-factors₁ f g) (copair-factors₂ f g)
      → ∀ m α β → Q m α β
    copair-ind f g Q base m α β =
      contr-ind (coprod f g)
        (λ where (m , α , β) → Q m α β)
        base (m , α , β)

    copair-β₁
      : ∀ {X} (f : hom A X) (g : hom B X)
      → ι₁ ⨾ copair f g ≡ f
    copair-β₁ f g = cast-path (copair-factors₁ f g)

    copair-β₂
      : ∀ {X} (f : hom A X) (g : hom B X)
      → ι₂ ⨾ copair f g ≡ g
    copair-β₂ f g = cast-path (copair-factors₂ f g)

    copair-η
      : ∀ {X} (f : hom A X) (g : hom B X)
      → (m : hom S X)
      → ι₁ ⨾ m => f → ι₂ ⨾ m => g
      → copair f g ≡ m
    copair-η f g =
      copair-ind f g
        (λ m _ _ → copair f g ≡ m) refl
```

## Equalizers

Given `f, g : hom A B`, an equalizer `e : hom E A` satisfies
`e ⨾ f ≡ e ⨾ g` and has a conditional universal property: for any
`h' : hom X A` with `h' ⨾ f ≡ h' ⨾ g`, the cone
`Σ m ∶ hom X E , (m ⨾ e => h')` is contractible. The precondition
`h' ⨾ f ≡ h' ⨾ g` gates access to the mediating morphism.

```agda
  equalizer-cone
    : ∀ {A E : ob} → hom E A
    → (X : ob) → hom X A → Type (o ⊔ h)
  equalizer-cone {E = E} e X h' =
    Sigma (hom X E) λ m → m ⨾ e => h'

  is-equalizer
    : ∀ {A B E : ob}
      (f g : hom A B) (e : hom E A)
    → Type (o ⊔ h)
  is-equalizer f g e =
    (e ⨾ f ≡ e ⨾ g)
    × (∀ {X} (h' : hom X _) → h' ⨾ f ≡ h' ⨾ g
       → is-contr (equalizer-cone e X h'))

  module Equalizer
    {A B E : ob} {f g : hom A B} {e : hom E A}
    (eq : is-equalizer f g e)
    where

    equalizes : e ⨾ f ≡ e ⨾ g
    equalizes = eq .fst

    eq-med
      : ∀ {X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → hom X E
    eq-med h' p = eq .snd h' p .center .fst

    eq-factors
      : ∀ {X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → eq-med h' p ⨾ e => h'
    eq-factors h' p = eq .snd h' p .center .snd

    eq-ind
      : ∀ {u X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → (Q : (m : hom X E) → m ⨾ e => h' → Type u)
      → Q (eq-med h' p) (eq-factors h' p)
      → ∀ m α → Q m α
    eq-ind h' p Q base m α =
      contr-ind (eq .snd h' p)
        (λ where (m , α) → Q m α)
        base (m , α)

    eq-β
      : ∀ {X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → eq-med h' p ⨾ e ≡ h'
    eq-β h' p = cast-path (eq-factors h' p)

    eq-η
      : ∀ {X} (h' : hom X A) (p : h' ⨾ f ≡ h' ⨾ g)
      → (m : hom X E)
      → m ⨾ e => h'
      → eq-med h' p ≡ m
    eq-η h' p =
      eq-ind h' p (λ m _ → eq-med h' p ≡ m) refl
```

## Pullbacks

A pullback of `f : hom A C` and `g : hom B C` consists of projections
`p₁ : hom P A` and `p₂ : hom P B` satisfying the commuting square
`p₁ ⨾ f ≡ p₂ ⨾ g`, together with a conditional universal property: for
any `h₁ : hom X A` and `h₂ : hom X B` with `h₁ ⨾ f ≡ h₂ ⨾ g`, the
product-shaped cone is contractible. The cone type is identical to
`product-cone`; the precondition `h₁ ⨾ f ≡ h₂ ⨾ g` is the only
difference from products.

```agda
  pullback-cone = product-cone

  is-pullback
    : ∀ {A B C P : ob}
      (p₁ : hom P A) (p₂ : hom P B)
      (f : hom A C) (g : hom B C)
    → Type (o ⊔ h)
  is-pullback p₁ p₂ f g =
    (p₁ ⨾ f ≡ p₂ ⨾ g)
    × (∀ {X} (h₁ : hom X _) (h₂ : hom X _)
       → h₁ ⨾ f ≡ h₂ ⨾ g
       → is-contr (pullback-cone p₁ p₂ X h₁ h₂))

  module Pullback
    {A B C P : ob}
    {p₁ : hom P A} {p₂ : hom P B}
    {f : hom A C} {g : hom B C}
    (pb : is-pullback p₁ p₂ f g)
    where

    square : p₁ ⨾ f ≡ p₂ ⨾ g
    square = pb .fst

    pb-med
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → hom X P
    pb-med h₁ h₂ q = pb .snd h₁ h₂ q .center .fst

    pb-factors₁
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → pb-med h₁ h₂ q ⨾ p₁ => h₁
    pb-factors₁ h₁ h₂ q =
      pb .snd h₁ h₂ q .center .snd .fst

    pb-factors₂
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → pb-med h₁ h₂ q ⨾ p₂ => h₂
    pb-factors₂ h₁ h₂ q =
      pb .snd h₁ h₂ q .center .snd .snd

    pb-ind
      : ∀ {u X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → (Q : (m : hom X P)
           → m ⨾ p₁ => h₁ → m ⨾ p₂ => h₂
           → Type u)
      → Q (pb-med h₁ h₂ q)
          (pb-factors₁ h₁ h₂ q)
          (pb-factors₂ h₁ h₂ q)
      → ∀ m α β → Q m α β
    pb-ind h₁ h₂ q Q base m α β =
      contr-ind (pb .snd h₁ h₂ q)
        (λ where (m , α , β) → Q m α β)
        base (m , α , β)

    pb-β₁
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → pb-med h₁ h₂ q ⨾ p₁ ≡ h₁
    pb-β₁ h₁ h₂ q = cast-path (pb-factors₁ h₁ h₂ q)

    pb-β₂
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → pb-med h₁ h₂ q ⨾ p₂ ≡ h₂
    pb-β₂ h₁ h₂ q = cast-path (pb-factors₂ h₁ h₂ q)

    pb-η
      : ∀ {X} (h₁ : hom X A) (h₂ : hom X B)
        (q : h₁ ⨾ f ≡ h₂ ⨾ g)
      → (m : hom X P)
      → m ⨾ p₁ => h₁ → m ⨾ p₂ => h₂
      → pb-med h₁ h₂ q ≡ m
    pb-η h₁ h₂ q =
      pb-ind h₁ h₂ q
        (λ m _ _ → pb-med h₁ h₂ q ≡ m) refl
```

## Morphism properties

Whiskering operators apply a morphism to one side of a path. Right
whiskering `p ▹ h'` precomposes the path's endpoints with `h'`; left
whiskering `f ◃ p` postcomposes `f`.

```agda
  _▹_
    : ∀ {x y z} {f g : hom x y}
    → f ≡ g → (h' : hom y z)
    → f ⨾ h' ≡ g ⨾ h'
  p ▹ h' = ap (_⨾ h') p
  infixr 25 _▹_

  _◃_
    : ∀ {x y z} (f : hom x y)
    → {g h' : hom y z} → g ≡ h'
    → f ⨾ g ≡ f ⨾ h'
  f ◃ p = ap (f ⨾_) p
  infixl 26 _◃_
```

### Sections and retractions

A morphism `f` has a section when there exists a right inverse `g`
with `f ⨾ g ≡ idn`. It has a retraction when there exists a left
inverse `g` with `g ⨾ f ≡ idn`.

```agda
  has-section : ∀ {x y} → hom x y → Type h
  has-section {y} f = Σ g ∶ hom y _ , f ⨾ g ≡ idn _

  has-retraction : ∀ {x y} → hom x y → Type h
  has-retraction {x} f = Σ g ∶ hom _ x , g ⨾ f ≡ idn _
```

### Mono and epi

A monomorphism is left-cancellable; an epimorphism is
right-cancellable.

```agda
  is-mono : ∀ {x y} → hom x y → Type (o ⊔ h)
  is-mono {x} f = ∀ {w} {g h' : hom w x} → g ⨾ f ≡ h' ⨾ f → g ≡ h'

  is-epi : ∀ {x y} → hom x y → Type (o ⊔ h)
  is-epi {y} f = ∀ {z} {g h' : hom y z} → f ⨾ g ≡ f ⨾ h' → g ≡ h'
```

### Isomorphisms

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
    , pcom (sym (assoc f f' (g' ⨾ g)))
           (f ◃ sym (assoc f' g' g))
           (pcom (f ◃ (sym p' ▹ g)) (f ◃ unitl g) p)
    , pcom (sym (assoc g' g (f ⨾ f')))
           (g' ◃ sym (assoc g f f'))
           (pcom (g' ◃ (sym q ▹ f')) (g' ◃ unitl f') q')
```

### Inverse uniqueness

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
        (pcom (sym (assoc r f s)) (r ◃ p') (unitr r))
```

### Sections and retractions vs mono and epi

A section (right inverse) gives a monomorphism; a retraction (left
inverse) gives an epimorphism. The proofs sandwich the hypothesis
between unit laws and associativity.

```agda
  section→mono
    : ∀ {x y} {f : hom x y}
    → has-section f → is-mono f
  section→mono {f = f} (g , s) {g = a} {h' = b} p =
    a             ≡˘⟨ unitr a ⟩
    a ⨾ idn _     ≡˘⟨ a ◃ s ⟩
    a ⨾ (f ⨾ g)   ≡˘⟨ assoc a f g ⟩
    (a ⨾ f) ⨾ g   ≡⟨ p ▹ g ⟩
    (b ⨾ f) ⨾ g   ≡⟨ assoc b f g ⟩
    b ⨾ (f ⨾ g)   ≡⟨ b ◃ s ⟩
    b ⨾ idn _     ≡⟨ unitr b ⟩
    b ∎

  retraction→epi
    : ∀ {x y} {f : hom x y}
    → has-retraction f → is-epi f
  retraction→epi {f = f} (g , r) {g = a} {h' = b} p =
    a             ≡˘⟨ unitl a ⟩
    idn _ ⨾ a     ≡˘⟨ r ▹ a ⟩
    (g ⨾ f) ⨾ a   ≡⟨ assoc g f a ⟩
    g ⨾ (f ⨾ a)   ≡⟨ g ◃ p ⟩
    g ⨾ (f ⨾ b)   ≡˘⟨ assoc g f b ⟩
    (g ⨾ f) ⨾ b   ≡⟨ r ▹ b ⟩
    idn _ ⨾ b     ≡⟨ unitl b ⟩
    b ∎
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

### Mono/epi composition and cancellation

Monomorphisms compose: if both `f` and `g` are mono, then `f ⨾ g` is
mono. The proof reassociates to apply `g`'s cancellation, then `f`'s.

```agda
  mono-comp
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-mono f → is-mono g → is-mono (f ⨾ g)
  mono-comp {f = f} {g} mf mg p =
    mf (mg (assoc _ f g ∙ p ∙ sym (assoc _ f g)))

  epi-comp
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-epi f → is-epi g → is-epi (f ⨾ g)
  epi-comp {f = f} {g} ef eg p =
    eg (ef (sym (assoc f g _) ∙ p ∙ assoc f g _))
```

If `f ⨾ g` is mono then `f` is mono; if `f ⨾ g` is epi then `g` is
epi. The proofs apply the composite cancellation after wrapping with
the opposite morphism.

```agda
  mono-cancel
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-mono (f ⨾ g) → is-mono f
  mono-cancel {f = f} {g} mfg p =
    mfg (sym (assoc _ f g) ∙ p ▹ g ∙ assoc _ f g)

  epi-cancel
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-epi (f ⨾ g) → is-epi g
  epi-cancel {f = f} {g} efg p =
    efg (assoc f g _ ∙ f ◃ p ∙ sym (assoc f g _))
```

### Composite witnesses from paths

`cast-path` extracts a hom-level path from an emb-level composite
witness. The reverse direction reconstructs the witness from a path
and the canonical composite equation `emb-comp`.

```agda
  cast-path⁻¹
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → f ⨾ g ≡ s → f ⨾ g => s
  cast-path⁻¹ {f = f} {g} {s} p =
    ap emb (sym p) ∙ emb-comp f g
```

### Product η-expansion

The pairing of the projections is the identity: `idn` factors through
each projection as itself, since `idn ⨾ π => π` is exactly
`emb π ≡ emb (idn) · π`, and `emb-idn-absorb` proves the composite
`emb (idn) · π` collapses to `emb π`. Uniqueness of the product cone
does the rest.

```agda
  module _
    {A B P : ob} {π₁ : hom P A} {π₂ : hom P B}
    (prod : is-product π₁ π₂)
    where
    open Product prod

    private
      idn-factors₁ : idn P ⨾ π₁ => π₁
      idn-factors₁ = sym (emb-idn-absorb π₁)

      idn-factors₂ : idn P ⨾ π₂ => π₂
      idn-factors₂ = sym (emb-idn-absorb π₂)

    ⟨,⟩-η-idn : ⟨ π₁ , π₂ ⟩ ≡ idn P
    ⟨,⟩-η-idn = ⟨,⟩-η π₁ π₂ (idn P) idn-factors₁ idn-factors₂
```

### Coproduct η-expansion

Dual: the copairing of the injections is the identity. Here
`ι ⨾ idn => ι` is `emb ι ≡ emb ι · idn`, collapsed by `·-idn`.

```agda
  module _
    {A B S : ob} {ι₁ : hom A S} {ι₂ : hom B S}
    (coprod : is-coproduct ι₁ ι₂)
    where
    open Coproduct coprod

    private
      idn-cofactors₁ : ι₁ ⨾ idn S => ι₁
      idn-cofactors₁ = sym (·-idn (emb ι₁))

      idn-cofactors₂ : ι₂ ⨾ idn S => ι₂
      idn-cofactors₂ = sym (·-idn (emb ι₂))

    copair-η-idn : copair ι₁ ι₂ ≡ idn S
    copair-η-idn =
      copair-η ι₁ ι₂ (idn S) idn-cofactors₁ idn-cofactors₂
```

### Product uniqueness up to isomorphism

Two products for the same diagram are isomorphic. The mediating
morphisms from each product's universal property compose to the
identity by η-expansion.

```agda
  product-unique
    : ∀ {A B P P' : ob}
      {π₁ : hom P A} {π₂ : hom P B}
      {π₁' : hom P' A} {π₂' : hom P' B}
    → (prod : is-product π₁ π₂)
    → (prod' : is-product π₁' π₂')
    → P ≅ P'
  product-unique {π₁ = π₁} {π₂} {π₁'} {π₂'} prod prod' =
    ψ , φ , ψφ≡idn , φψ≡idn
    where
      module Π  = Product prod
      module Π' = Product prod'
      φ : hom _ _
      φ = Π.⟨ π₁' , π₂' ⟩
      ψ : hom _ _
      ψ = Π'.⟨ π₁ , π₂ ⟩

      ψφ≡idn : ψ ⨾ φ ≡ idn _
      ψφ≡idn =
        sym (Π.⟨,⟩-η π₁ π₂ (ψ ⨾ φ)
          (cast-path⁻¹ (assoc ψ φ π₁
            ∙ ψ ◃ Π.⟨,⟩-β₁ π₁' π₂'
            ∙ Π'.⟨,⟩-β₁ π₁ π₂))
          (cast-path⁻¹ (assoc ψ φ π₂
            ∙ ψ ◃ Π.⟨,⟩-β₂ π₁' π₂'
            ∙ Π'.⟨,⟩-β₂ π₁ π₂)))
        ∙ ⟨,⟩-η-idn prod

      φψ≡idn : φ ⨾ ψ ≡ idn _
      φψ≡idn =
        sym (Π'.⟨,⟩-η π₁' π₂' (φ ⨾ ψ)
          (cast-path⁻¹ (assoc φ ψ π₁'
            ∙ φ ◃ Π'.⟨,⟩-β₁ π₁ π₂
            ∙ Π.⟨,⟩-β₁ π₁' π₂'))
          (cast-path⁻¹ (assoc φ ψ π₂'
            ∙ φ ◃ Π'.⟨,⟩-β₂ π₁ π₂
            ∙ Π.⟨,⟩-β₂ π₁' π₂')))
        ∙ ⟨,⟩-η-idn prod'

  coproduct-unique
    : ∀ {A B S S' : ob}
      {ι₁ : hom A S} {ι₂ : hom B S}
      {ι₁' : hom A S'} {ι₂' : hom B S'}
    → (coprod : is-coproduct ι₁ ι₂)
    → (coprod' : is-coproduct ι₁' ι₂')
    → S ≅ S'
  coproduct-unique
    {ι₁ = ι₁} {ι₂} {ι₁'} {ι₂'} coprod coprod' =
    φ , ψ , φψ≡idn , ψφ≡idn
    where
      module Co  = Coproduct coprod
      module Co' = Coproduct coprod'
      φ : hom _ _
      φ = Co.copair ι₁' ι₂'
      ψ : hom _ _
      ψ = Co'.copair ι₁ ι₂

      ψφ≡idn : ψ ⨾ φ ≡ idn _
      ψφ≡idn =
        sym (Co'.copair-η ι₁' ι₂' (ψ ⨾ φ)
          (cast-path⁻¹ (sym (assoc ι₁' ψ φ)
            ∙ Co'.copair-β₁ ι₁ ι₂ ▹ φ
            ∙ Co.copair-β₁ ι₁' ι₂'))
          (cast-path⁻¹ (sym (assoc ι₂' ψ φ)
            ∙ Co'.copair-β₂ ι₁ ι₂ ▹ φ
            ∙ Co.copair-β₂ ι₁' ι₂')))
        ∙ copair-η-idn coprod'

      φψ≡idn : φ ⨾ ψ ≡ idn _
      φψ≡idn =
        sym (Co.copair-η ι₁ ι₂ (φ ⨾ ψ)
          (cast-path⁻¹ (sym (assoc ι₁ φ ψ)
            ∙ Co.copair-β₁ ι₁' ι₂' ▹ ψ
            ∙ Co'.copair-β₁ ι₁ ι₂))
          (cast-path⁻¹ (sym (assoc ι₂ φ ψ)
            ∙ Co.copair-β₂ ι₁' ι₂' ▹ ψ
            ∙ Co'.copair-β₂ ι₁ ι₂)))
        ∙ copair-η-idn coprod
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
        (r ⨾ f) ⨾ s   ≡⟨ assoc r f s ⟩
        r ⨾ (f ⨾ s)   ≡⟨ r ◃ fs ⟩
        r ⨾ idn _     ≡⟨ unitr r ⟩
        r ∎
```

### Neutrality

A morphism is neutral when both composition maps are equivalences.
Left-neutrality: `(f ⨾_)` is an equivalence. Right-neutrality:
`(_⨾ f)` is an equivalence. An idempotent neutral morphism equals the
identity (cancel `_⨾ e` against `idn ⨾ e`).

```agda
  is-neutral : ∀ {x y} → hom x y → Type (o ⊔ h)
  is-neutral {x} {y} f =
    (∀ {z} → is-equiv (λ (h' : hom y z) → f ⨾ h'))
    × (∀ {w} → is-equiv (λ (g : hom w x) → g ⨾ f))

  idn-is-neutral : ∀ {x} → is-neutral (idn x)
  idn-is-neutral .fst =
    subst is-equiv (sym (funext unitl)) (aut .snd)
  idn-is-neutral .snd =
    subst is-equiv (sym (funext unitr)) (aut .snd)

  idempotent-neutral→idn
    : ∀ {x} {e : hom x x}
    → is-neutral e → e ⨾ e ≡ e → e ≡ idn _
  idempotent-neutral→idn {e = e} (_ , re) ee≡e =
    equiv→lc re
      (ee≡e ∙ sym (unitl e))
```

## Functors

A functor maps objects and morphisms, preserving composition and
neutrality. Identity preservation is derived: `hmap idn` is neutral
(preserved) and idempotent (from comp preservation + `idem`), so it
equals `idn` by `idempotent-neutral→idn`.

```agda
record functor
  {o h o' h'}
  (C : category o h) (D : category o' h')
  : Type (o ⊔ h ⊔ o' ⊔ h')
  where
  no-eta-equality
  private
    module Cs = category C
    module Ds = category D
    module Cb = Cat C
    module Db = Cat D

  field
    map  : Cs.ob → Ds.ob
    hmap : ∀ {x y}
      → Cs.hom x y → Ds.hom (map x) (map y)
    preserves-comp
      : ∀ {x y z} (f : Cs.hom x y) (g : Cs.hom y z)
      → hmap (f Cs.⨾ g) ≡ hmap f Ds.⨾ hmap g
    preserves-neutral
      : ∀ {x y} {f : Cs.hom x y}
      → Cb.is-neutral f → Db.is-neutral (hmap f)

  hmap-idn : ∀ {x} → hmap (Cs.idn x) ≡ Ds.idn (map x)
  hmap-idn {x} = Db.idempotent-neutral→idn
    (preserves-neutral Cb.idn-is-neutral)
    (sym (preserves-comp (Cs.idn x) (Cs.idn x)) ∙ ap hmap Cs.idem)

{-# INLINE functor.constructor #-}
```

The identity functor maps everything to itself.

```agda
id-functor
  : ∀ {o h} (C : category o h) → functor C C
id-functor C .functor.map x = x
id-functor C .functor.hmap f = f
id-functor C .functor.preserves-comp _ _ = refl
id-functor C .functor.preserves-neutral n = n
```

Functor composition maps objects and morphisms sequentially. Identity
preservation chains through both functors; composition preservation
uses `preserves-comp` of each functor plus `ap` to push the inner
functor's equation through the outer.

```agda
_∘F_
  : ∀ {o₁ h₁ o₂ h₂ o₃ h₃}
    {C : category o₁ h₁}
    {D : category o₂ h₂}
    {E : category o₃ h₃}
  → functor D E → functor C D → functor C E
_∘F_ {C = C} {D} {E} G F = FGF where
  module F = functor F
  module G = functor G

  FGF : functor C E
  FGF .functor.map x = G.map (F.map x)
  FGF .functor.hmap f = G.hmap (F.hmap f)
  FGF .functor.preserves-comp f g =
    ap G.hmap (F.preserves-comp f g)
    ∙ G.preserves-comp (F.hmap f) (F.hmap g)
  FGF .functor.preserves-neutral n =
    G.preserves-neutral (F.preserves-neutral n)

infixr 30 _∘F_
```

## Natural transformations

A natural transformation between functors `F` and `G` assigns to each
object `x` a component morphism `F x → G x`, such that for any
morphism `f : x → y`, the naturality square commutes:
`F(f) ⨾ η y ≡ η x ⨾ G(f)`.

```agda
record nat-trans
  {o h o' h'}
  {C : category o h} {D : category o' h'}
  (F G : functor C D)
  : Type (o ⊔ h ⊔ h')
  where
  no-eta-equality
  private
    module C = category C
    module D = category D
    module F = functor F
    module G = functor G

  field
    component
      : ∀ x → D.hom (F.map x) (G.map x)
    natural
      : ∀ {x y} (f : C.hom x y)
      → F.hmap f D.⨾ component y
      ≡ component x D.⨾ G.hmap f

{-# INLINE nat-trans.constructor #-}
```

The identity natural transformation has `idn` as every component.
Naturality follows from `unitl` and `unitr`.

```agda
nat-id
  : ∀ {o h o' h'}
    {C : category o h} {D : category o' h'}
    (F : functor C D)
  → nat-trans F F
nat-id {D = D} F = nt where
  module D = category D
  module F = functor F

  nt : nat-trans F F
  nt .nat-trans.component x = D.idn (F.map x)
  nt .nat-trans.natural f =
    D.unitr (F.hmap f) ∙ sym (D.unitl (F.hmap f))
```

Vertical composition of natural transformations composes the
components. Naturality of the composite follows from associativity
and the naturality of each factor.

```agda
nat-comp
  : ∀ {o h o' h'}
    {C : category o h} {D : category o' h'}
    {F G H : functor C D}
  → nat-trans F G → nat-trans G H → nat-trans F H
nat-comp {D = D} {F} {G} {H} α β = αβ where
  module D  = category D
  module Dt = assoc-tower D
  module Ca = Cat D
  module F  = functor F
  module G  = functor G
  module H  = functor H
  module α  = nat-trans α
  module β  = nat-trans β

  αβ : nat-trans F H
  αβ .nat-trans.component x =
    α.component x D.⨾ β.component x
  αβ .nat-trans.natural {x} {y} f =
    F.hmap f D.⨾ (α.component y D.⨾ β.component y)
      ≡˘⟨ Dt.assoc (F.hmap f)
            (α.component y) (β.component y) ⟩
    (F.hmap f D.⨾ α.component y) D.⨾ β.component y
      ≡⟨ α.natural f Ca.▹ β.component y ⟩
    (α.component x D.⨾ G.hmap f) D.⨾ β.component y
      ≡⟨ Dt.assoc (α.component x)
            (G.hmap f) (β.component y) ⟩
    α.component x D.⨾ (G.hmap f D.⨾ β.component y)
      ≡⟨ α.component x Ca.◃ β.natural f ⟩
    α.component x D.⨾ (β.component x D.⨾ H.hmap f)
      ≡˘⟨ Dt.assoc (α.component x)
            (β.component x) (H.hmap f) ⟩
    (α.component x D.⨾ β.component x) D.⨾ H.hmap f ∎
```

## Adjunctions

An adjunction `F ⊣ G` between categories `C` and `D` consists of an
equivalence `D.hom (F x) y ≃ C.hom x (G y)` natural in both variables.
The adjunct and coadjunct are the forward and inverse directions.

```agda
record _⊣_
  {o h o' h'}
  {C : category o h} {D : category o' h'}
  (F : functor C D) (G : functor D C)
  : Type (o ⊔ h ⊔ o' ⊔ h')
  where
  no-eta-equality
  private
    module Cs = category C
    module Ds = category D
    module F = functor F
    module G = functor G

  field
    hom-equiv
      : ∀ x y
      → Ds.hom (F.map x) y ≃ Cs.hom x (G.map y)

  adjunct : ∀ {x y}
    → Ds.hom (F.map x) y → Cs.hom x (G.map y)
  adjunct {x} {y} = Equiv.fwd (hom-equiv x y)

  coadjunct : ∀ {x y}
    → Cs.hom x (G.map y) → Ds.hom (F.map x) y
  coadjunct {x} {y} = Equiv.inv (hom-equiv x y)

  field
    natural-dom
      : ∀ {x x' y} (f : Cs.hom x' x) (g : Ds.hom (F.map x) y)
      → adjunct (F.hmap f Ds.⨾ g) ≡ f Cs.⨾ adjunct g
    natural-cod
      : ∀ {x y y'} (g : Ds.hom (F.map x) y) (k : Ds.hom y y')
      → adjunct (g Ds.⨾ k) ≡ adjunct g Cs.⨾ G.hmap k

{-# INLINE _⊣_.constructor #-}

is-left-adjoint
  : ∀ {o h o' h'}
    {C : category o h} {D : category o' h'}
  → functor C D → Type _
is-left-adjoint F =
  Σ G ∶ functor _ _ , F ⊣ G

is-right-adjoint
  : ∀ {o h o' h'}
    {C : category o h} {D : category o' h'}
  → functor D C → Type _
is-right-adjoint G =
  Σ F ∶ functor _ _ , F ⊣ G
```
