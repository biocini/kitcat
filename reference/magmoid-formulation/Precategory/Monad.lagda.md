Lane Biocini, February 2025

Wild monads and Kleisli categories.

References:
- Halley, Mimram (2024), "Polynomials in Homotopy Type Theory as a Kleisli Category"

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Monad where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel
open import Core.Kan hiding (assoc; unitl; unitr)
open import Core.Transport
open import Core.Equiv

open import Cat.Base

private variable
  u v w : Level

module monad-def {u v} (C : precategory u v) where
  private module C = Cat C

  record Wild-monad : Type (u ⊔ v) where
    no-eta-equality
    field
      M : C.ob → C.ob
      unit : ∀ {a} → C.hom a (M a)
      bind : ∀ {a b} → C.hom a (M b) → C.hom (M a) (M b)

    extend = bind

    join : ∀ {a} → C.hom (M (M a)) (M a)
    join = bind C.idn

    map : ∀ {a b} → C.hom a b → C.hom (M a) (M b)
    map f = bind (C._⨾_ f unit)

    field
      unit-bind : ∀ {a b} {f : C.hom a (M b)} → C._⨾_ unit (bind f) ≡ f
      bind-unit : ∀ {a} → bind unit ≡ C.idn {x = M a}
      bind-bind : ∀ {a b c} {f : C.hom a (M b)} {g : C.hom b (M c)}
                → C._⨾_ (bind f) (bind g) ≡ bind (C._⨾_ f (bind g))

  {-# INLINE Wild-monad.constructor #-}

  record Wild-comonad : Type (u ⊔ v) where
    no-eta-equality
    field
      W : C.ob → C.ob
      counit : ∀ {a} → C.hom (W a) a
      cobind : ∀ {a b} → C.hom (W a) b → C.hom (W a) (W b)

    coextend = cobind

    duplicate : ∀ {a} → C.hom (W a) (W (W a))
    duplicate = cobind C.idn

    comap : ∀ {a b} → C.hom a b → C.hom (W a) (W b)
    comap f = cobind (C._⨾_ counit f)

    field
      cobind-counit : ∀ {a b} {f : C.hom (W a) b} → C._⨾_ (cobind f) counit ≡ f
      counit-cobind : ∀ {a} → cobind counit ≡ C.idn {x = W a}
      cobind-cobind : ∀ {a b c} {f : C.hom (W a) b} {g : C.hom (W b) c}
                    → C._⨾_ (cobind f) (cobind g) ≡ cobind (C._⨾_ (cobind f) g)

  {-# INLINE Wild-comonad.constructor #-}

module kleisli {u v} (C : precategory u v) where
  private module C = Cat C
  open monad-def C

  module _ (monad : Wild-monad) where
    open Wild-monad monad

    private
      K-ob : Type u
      K-ob = C.ob

      K-hom : K-ob → K-ob → Type v
      K-hom a b = C.hom a (M b)

      infixr 40 _⨾ᴷ_
      _⨾ᴷ_ : ∀ {a b c} → K-hom a b → K-hom b c → K-hom a c
      f ⨾ᴷ g = C._⨾_ f (bind g)

      K-assoc : ∀ {a b c d} (f : K-hom a b) (g : K-hom b c) (h : K-hom c d)
              → f ⨾ᴷ (g ⨾ᴷ h) ≡ (f ⨾ᴷ g) ⨾ᴷ h
      K-assoc f g h = ap (C._⨾_ f) (sym (bind-bind {f = g} {g = h})) ∙ C.assoc f (bind g) (bind h)

      K-is-eqv : ∀ {x y} → K-hom x y → Type (u ⊔ v)
      K-is-eqv {x} {y} f = (∀ {z} → is-equiv (λ (g : K-hom y z) → f ⨾ᴷ g))
                         × (∀ {w} → is-equiv (λ (g : K-hom w x) → g ⨾ᴷ f))

      unit-is-eqv : ∀ {a} → K-is-eqv (unit {a})
      unit-is-eqv .fst = subst is-equiv (sym (funext λ g → unit-bind)) id-equiv
      unit-is-eqv .snd = subst is-equiv (sym (funext λ g → ap (C._⨾_ g) bind-unit ∙ C.runit g)) id-equiv

      unit-idem : ∀ {a} → unit {a} ≡ unit ⨾ᴷ unit
      unit-idem = sym (ap (C._⨾_ unit) bind-unit ∙ C.runit unit)

      K-unital : ∀ x → Σ i ∶ K-hom x x , K-is-eqv i × (i ≡ i ⨾ᴷ i)
      K-unital x = unit , unit-is-eqv , unit-idem

    Kleisli : precategory u v
    Kleisli .precategory.ob = K-ob
    Kleisli .precategory.hom = K-hom
    Kleisli .precategory._⨾_ = _⨾ᴷ_
    Kleisli .precategory.unital = K-unital
    Kleisli .precategory.assoc = K-assoc

module cokleisli {u v} (C : precategory u v) where
  private module C = Cat C
  open monad-def C

  module _ (comonad : Wild-comonad) where
    open Wild-comonad comonad

    private
      coK-ob : Type u
      coK-ob = C.ob

      coK-hom : coK-ob → coK-ob → Type v
      coK-hom a b = C.hom (W a) b

      infixr 40 _⨾ᶜᵒᴷ_
      _⨾ᶜᵒᴷ_ : ∀ {a b c} → coK-hom a b → coK-hom b c → coK-hom a c
      f ⨾ᶜᵒᴷ g = C._⨾_ (cobind f) g

      coK-assoc : ∀ {a b c d} (f : coK-hom a b) (g : coK-hom b c) (h : coK-hom c d)
                → f ⨾ᶜᵒᴷ (g ⨾ᶜᵒᴷ h) ≡ (f ⨾ᶜᵒᴷ g) ⨾ᶜᵒᴷ h
      coK-assoc f g h = C.assoc (cobind f) (cobind g) h ∙ ap (λ z → C._⨾_ z h) (cobind-cobind {f = f} {g = g})

      coK-is-eqv : ∀ {x y} → coK-hom x y → Type (u ⊔ v)
      coK-is-eqv {x} {y} f = (∀ {z} → is-equiv (λ (g : coK-hom y z) → f ⨾ᶜᵒᴷ g))
                           × (∀ {w} → is-equiv (λ (g : coK-hom w x) → g ⨾ᶜᵒᴷ f))

      counit-is-eqv : ∀ {a} → coK-is-eqv (counit {a})
      counit-is-eqv .fst = subst is-equiv (sym (funext λ g → ap (λ z → C._⨾_ z g) counit-cobind ∙ C.lunit g)) id-equiv
      counit-is-eqv .snd = subst is-equiv (sym (funext λ g → cobind-counit)) id-equiv

      counit-idem : ∀ {a} → counit {a} ≡ counit ⨾ᶜᵒᴷ counit
      counit-idem = sym (ap (λ z → C._⨾_ z counit) counit-cobind ∙ C.lunit counit)

      coK-unital : ∀ x → Σ i ∶ coK-hom x x , coK-is-eqv i × (i ≡ i ⨾ᶜᵒᴷ i)
      coK-unital x = counit , counit-is-eqv , counit-idem

    CoKleisli : precategory u v
    CoKleisli .precategory.ob = coK-ob
    CoKleisli .precategory.hom = coK-hom
    CoKleisli .precategory._⨾_ = _⨾ᶜᵒᴷ_
    CoKleisli .precategory.unital = coK-unital
    CoKleisli .precategory.assoc = coK-assoc
```

