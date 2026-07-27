Spike: position (B) — post `twist⁻` only, extract `twist⁺`.

The `⁻` unit tier mentions `coact-π`, hence `var`, hence `twist⁻`
alone. So it is stateable before `twist⁺` exists, and its centre defines
`twist⁺`. Mutual inverseness on that side is then not an axiom but the
centre's own witness, and the carrier loses a field.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.ExtractedTwist where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
```

## The carrier, with one twist

```agda
record graph⁻ o h : Type₊ (o ⊔ h) where
  field
    ob  : Type o
    hom : ob → ob → Type h

  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v

  argument : ob → ob → Type (o ⊔ h)
  argument x y = term x × coterm y

  conclusion : ∀ {x y} → argument x y → Type h
  conclusion γ = hom (γ .fst .fst) (γ .snd .fst)

  judgment : ob → ob → Type (o ⊔ h)
  judgment x y = (γ : argument x y) → conclusion γ

  field
    reflect : ∀ {x y} → hom x y → judgment x y
    twist⁻  : (x : ob) → hom x x

  var : (x : ob) → term x
  var x = x , twist⁻ x

  coact-π : ∀ {x y} → hom x y → (k : coterm y) → hom x (k .fst)
  coact-π {x} f k = reflect f (var x , k)
```

The `⁻` tier needs nothing else, and its centre is the other twist.

```agda
  field
    unital⁻ : (x : ob) → is-contr (fiber (coact-π {x} {x}) snd)

  twist⁺ : (x : ob) → hom x x
  twist⁺ x = unital⁻ x .center .fst

  cancel⁻ : (x : ob) → coact-π (twist⁺ x) ≡ snd
  cancel⁻ x = unital⁻ x .center .snd

  covar : (y : ob) → coterm y
  covar y = y , twist⁺ y

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact f k = k .fst , coact-π f k

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (t , covar y)

  act : ∀ {x y} → hom x y → term x → term y
  act f t = t .fst , act-π f t

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect f (γ .fst , coact g (γ .snd))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect g (act f (γ .fst) , γ .snd)

  representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  representable = fiber reflect

  field
    stable : ∀ {x y} (α : judgment x y) → is-prop (representable α)
    cut⁺   : ∀ {x y z} (f : hom x y) (g : hom y z)
           → representable (composite⁺ f g)
    cut⁻   : ∀ {x y z} (f : hom x y) (g : hom y z)
           → representable (composite⁻ f g)
```

## What comes free

Extraction hands back the coterm-side absorption at once, with no
readback and no second twist posited.

```agda
module extracted {o h} (G : graph⁻ o h) where
  open graph⁻ G public

  reflect-lc : ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-lc {n = n} p = ap fst (stable (reflect n) (_ , p) (n , refl))

  _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁺ g = cut⁺ f g .fst

  reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁺ g) ≡ composite⁺ f g
  reflect-⨾⁺ f g = cut⁺ f g .snd

  absorb⁻ : ∀ {x} (k : coterm x) → coact (twist⁺ x) k ≡ k
  absorb⁻ {x} k i = k .fst , cancel⁻ x i k

  composite-twist⁺ : ∀ {x y} (f : hom x y) → composite⁺ f (twist⁺ y) ≡ reflect f
  composite-twist⁺ f i γ = reflect f (γ .fst , absorb⁻ (γ .snd) i)

  unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ twist⁺ y ≡ f
  unitr⁺ f = reflect-lc (reflect-⨾⁺ f (twist⁺ y) ∙ composite-twist⁺ f)
    where y = _
```
