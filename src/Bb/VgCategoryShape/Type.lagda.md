An h-category: a graph, a ternary reflection of its edges into
judgments, a filler for the two argument slots, and both cuts
represented.

Structure is the graph, the reflection, and the filler with its
alignment. Property is the two cuts and unitality — where unitality is
not a condition on a posited unit but the contractibility of the type of
neutral idempotents, so the unit is extracted rather than chosen.
Stability and interchange are neither: both are theorems.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VgCategoryShape.Type where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Equiv.Base using (is-equiv)
open import Core.Equiv.Properties using (is-equiv-is-prop)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; ×-is-hlevel)
open import Core.Transport.Properties
  using (is-prop-is-prop; is-contr-is-prop)
```

## The graph and its reflection

```agda
record hcategory o h : Type₊ (o ⊔ h) where
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
```

## Representation

```agda
  representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  representable = fiber reflect

  is-stable : Type (o ⊔ h)
  is-stable = ∀ {x y} (α : judgment x y) → is-prop (representable α)

  is-stable-is-prop : is-prop is-stable
  is-stable-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → is-prop-is-prop _
```

## Neutrality, self-filled

An endomorphism holds its own slot while the other varies. It is tested
against its own object and nothing else, needing no filler to state, and
each half is a proposition.

```agda
  is-neutral : ∀ {x} → hom x x → Type (o ⊔ h)
  is-neutral {x} e =
      (∀ {z} → is-equiv (λ (h : hom x z) → reflect e ((x , e) , (z , h))))
    × (∀ {w} → is-equiv (λ (g : hom w x) → reflect e ((w , g) , (x , e))))

  is-neutral-is-prop : ∀ {x} (e : hom x x) → is-prop (is-neutral e)
  is-neutral-is-prop e =
    ×-is-hlevel 1 (Πi-is-prop λ _ → is-equiv-is-prop _)
                  (Πi-is-prop λ _ → is-equiv-is-prop _)
```

## The reflexivity edge

Both argument slots are closed by one section, and reading an edge back
off its own reflection returns it. Nothing here asks `rx` to be a unit.
That it is one is a theorem, `rx≡idn` in `Bb.VgCategoryShape.Base`.

```agda
  field
    rx : (x : ob) → hom x x

  var : (x : ob) → term x
  var x = x , rx x

  covar : (y : ob) → coterm y
  covar y = y , rx y

  axiom : (x : ob) → argument x x
  axiom x = var x , covar x

  eval : ∀ {x y} → judgment x y → hom x y
  eval {x} {y} α = α (var x , covar y)

  field
    readback : ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f
```

## The two actions

```agda
  coact-π : ∀ {x y} → hom x y → (k : coterm y) → hom x (k .fst)
  coact-π {x} f k = reflect f (var x , k)

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact f k = k .fst , coact-π f k

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (t , covar y)

  act : ∀ {x y} → hom x y → term x → term y
  act f t = t .fst , act-π f t
```

## The two cuts

A positive cut absorbs its second factor into the coterm and keeps the
first reflected; a negative cut absorbs its first into the term and
keeps the second. Contractibility is a proposition whatever it is
applied to, so both axioms are property outright.

```agda
  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect f (γ .fst , coact g (γ .snd))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect g (act f (γ .fst) , γ .snd)

  field
    cut⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (representable (composite⁺ f g))
    cut⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (representable (composite⁻ f g))

  _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁺ g = cut⁺ f g .center .fst

  _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁻ g = cut⁻ f g .center .fst

  reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁺ g) ≡ composite⁺ f g
  reflect-⨾⁺ f g = cut⁺ f g .center .snd

  reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁻ g) ≡ composite⁻ f g
  reflect-⨾⁻ f g = cut⁻ f g .center .snd
```

## Unitality

A neutral idempotent, after Capriotti-Kraus. The predicate is not itself
a proposition: its second component is a path between untruncated edges,
and over the path groupoid on `S²` the fibre at `refl` is `Ω²S² = ℤ`.
The type of edges satisfying it is a proposition, which
`Bb.VgCategoryShape.Base` proves as `is-unital-is-prop`. So the
field asks only for inhabitation,
and asking for it is property.

```agda
  unital : ∀ {x} → hom x x → Type (o ⊔ h)
  unital e = is-neutral e × (e ⨾⁻ e ≡ e)

  is-unital : ob → Type (o ⊔ h)
  is-unital x = Σ e ∶ hom x x , unital e

  field
    unit : (x : ob) → is-unital x

  idn : ∀ {x} → hom x x
  idn {x} = unit x .fst

  idn-neutral : ∀ {x} → is-neutral (idn {x})
  idn-neutral {x} = unit x .snd .fst

  idn-idem⁻ : ∀ {x} → idn {x} ⨾⁻ idn ≡ idn
  idn-idem⁻ {x} = unit x .snd .snd
```
