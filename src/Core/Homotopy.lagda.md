Homotopy algebra: equivalence relation operations and whiskering.

Following the equivalence relation naming convention (like Core.Kan):
- `eqv` — identity/reflexivity
- `inv` — inversion/symmetry
- `cat` — concatenation/transitivity

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Homotopy where

open import Core.Type using (Level; Type; _⊔_; _∘_)
open import Core.Base using (_≡_; refl; sym; _~_; ap)
open import Core.Kan using (_∙_; module Path)
open import Core.Transport.J using (J)

private variable
  u v w : Level
  A : Type u
  B : A → Type v
  C : Type w

```

## Homotopy Equivalence Relation

```agda

module htpy where
  eqv : {f : (x : A) → B x} → f ~ f
  eqv _ = refl

  inv : {f g : (x : A) → B x} → f ~ g → g ~ f
  inv H x = sym (H x)

  cat : {f g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
  cat H K x = H x ∙ K x

```

## Whiskering

```agda

module _ {u v w} {A : Type u} {B : Type v} {C : Type w} where
  _·l_ : (h : B → C) {f g : A → B} → f ~ g → (h ∘ f) ~ (h ∘ g)
  (h ·l H) x = ap h (H x)

  _·r_ : {f g : B → C} → f ~ g → (k : A → B) → (f ∘ k) ~ (g ∘ k)
  (H ·r k) a = H (k a)

  infixl 10 _·l_ _·r_

-- `inv` is not re-exported to avoid name clash with Equiv.inv and is-half-adj.inv.
-- Use htpy.inv explicitly for homotopy inversion.
open htpy public using (eqv; cat)

```

## Naturality

For a homotopy `η : k ~ l`, transporting a path `q` through `k`
first and crossing `η` at the endpoint agrees with crossing `η`
at the start and transporting through `l`.

```agda
homotopy-natural
  : {k l : A → C} (η : ∀ x → k x ≡ l x)
    {a b : A} (q : a ≡ b)
  → ap k q ∙ η b ≡ η a ∙ ap l q
homotopy-natural {k = k} {l = l} η {a = a} q =
  J (λ b' q' → ap k q' ∙ η b' ≡ η a ∙ ap l q')
    (Path.unitl (η a) ∙ sym (Path.unitr (η a)))
    q
```
