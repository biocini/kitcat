---
author: Lane Biocini
date: 2026-07
contents: Presentation comparisons for Cat — hom-PathPs against squares over path-iso.
---

Presentation-comparison material one level down from
`Cat.Depreciated.Monoidal.Properties`. The spine's path bridge (`Cat.Depreciated.Iso`) is
native cubical: `path-iso` packages the transported identities
with first-class fillers, and `hom-pathp→square` reads a
dependent path of homs as the classical commuting square. The
comparison between the two presentations — the `≡`-of-types
characterization and its equivalence form — is J-shaped, so it
lives here: a double J over the object paths whose base case
conjugates by the `refl`-value of the transported identity,
exactly the eliminator the spine retired.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Properties where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base using (transport; transport⁻; transport-refl)
open import Core.Transport.Properties using (transport-equiv)
open import Core.Transport.J using (J)
open import Core.Equiv.Base using (_≃_)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Base
open import Cat.Depreciated.Morphism
open import Cat.Depreciated.Iso

module _ {o h} (C : category o h) where
  open category C
  open theory C
  open morphism C
  open iso C
```

## The transported identity at `refl`

`path-iso.to refl` is a transport along the constant family, so
it collapses to the identity by `transport-refl` — native, no
eliminator. This is the cell the double J's base case conjugates
by, standing where the old formulation needed a `J-refl` patch
lemma.

```agda
  to-refl : ∀ {x} → path-iso.to (refl {x = x}) ≡ idn x
  to-refl {x} = transport-refl (idn x)
```

## The `≡`-of-types characterization

A dependent path of homs over object paths `p` and `q` is the
same type as the classical square through the transported
identities. The proof is a double J on `p` then `q`; the base
case is a line of path types whose endpoints ride the
`to-refl` conjugations back to the unit laws.

```agda
  hom-pathp≡square
    : ∀ {x x' y y'} (p : x ≡ x') (q : y ≡ y')
      (f : hom x y) (g : hom x' y')
    → (PathP (λ i → hom (p i) (q i)) f g)
    ≡ (f ⨾ path-iso.to q ≡ path-iso.to p ⨾ g)
  hom-pathp≡square {x} {x'} {y} {y'} p q f g =
    J (λ x₁ p₁ → (y₁ : ob) (q₁ : y ≡ y₁) (g₁ : hom x₁ y₁)
               → (PathP (λ i → hom (p₁ i) (q₁ i)) f g₁)
               ≡ (f ⨾ path-iso.to q₁ ≡ path-iso.to p₁ ⨾ g₁))
      outer-base p y' q g
    where
      inner-base
        : (g₁ : hom x y)
        → (f ≡ g₁)
        ≡ (f ⨾ path-iso.to (refl {x = y})
           ≡ path-iso.to (refl {x = x}) ⨾ g₁)
      inner-base g₁ i = Lend (~ i) ≡ Rend (~ i)
        where
          Lend : f ⨾ path-iso.to (refl {x = y}) ≡ f
          Lend = (f ◃ to-refl) ∙ unitr f

          Rend : path-iso.to (refl {x = x}) ⨾ g₁ ≡ g₁
          Rend = (to-refl ▹ g₁) ∙ unitl g₁

      outer-base
        : (y₁ : ob) (q₁ : y ≡ y₁) (g₁ : hom x y₁)
        → (PathP (λ i → hom x (q₁ i)) f g₁)
        ≡ (f ⨾ path-iso.to q₁ ≡ path-iso.to (refl {x = x}) ⨾ g₁)
      outer-base y₁ q₁ g₁ =
        J (λ y₂ q₂ → (g₂ : hom x y₂)
                   → (PathP (λ i → hom x (q₂ i)) f g₂)
                   ≡ (f ⨾ path-iso.to q₂
                      ≡ path-iso.to (refl {x = x}) ⨾ g₂))
          inner-base q₁ g₁
```

## The equivalence of presentations

Transport along the characterization closes the presentation
comparison both ways: the spine's `hom-pathp→square` is the
consumer-facing map, and the `≡`-of-types upgrades the
presentations to an equivalence, with `square→hom-pathp` the
inverse direction the spine never carries.

```agda
  square→hom-pathp
    : ∀ {x x' y y'} (p : x ≡ x') (q : y ≡ y')
      {f : hom x y} {g : hom x' y'}
    → f ⨾ path-iso.to q ≡ path-iso.to p ⨾ g
    → PathP (λ i → hom (p i) (q i)) f g
  square→hom-pathp p q {f} {g} = transport⁻ (hom-pathp≡square p q f g)

  hom-pathp≃square
    : ∀ {x x' y y'} (p : x ≡ x') (q : y ≡ y')
      {f : hom x y} {g : hom x' y'}
    → (PathP (λ i → hom (p i) (q i)) f g)
    ≃ (f ⨾ path-iso.to q ≡ path-iso.to p ⨾ g)
  hom-pathp≃square p q {f} {g} =
    transport (hom-pathp≡square p q f g)
    , transport-equiv (hom-pathp≡square p q f g)
```
