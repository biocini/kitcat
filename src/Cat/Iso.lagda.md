The `idtoiso` bridge sends a path between objects to an
isomorphism by specialising `J` at the reflexive isomorphism.
Building on it, `hom-PathP≃square` characterises dependent
paths between morphisms as commuting squares whose sides are
the transported identities.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Iso where

open import Core.Transport.Properties using (transport-equiv)
open import Core.Transport.Base using (transport; transport⁻)
open import Core.Transport.J using (J; J-refl)
open import Core.Data.Sigma.Type using (fst; _,_)
open import Core.Equiv.Base using (_≃_)
open import Core.Base
open import Core.Kan using (_∙_)

open import Cat.Base using (module Cat)
open import Cat.Type using (category; module Virtual)

module _ {o h} (C : category o h) where
  open Virtual C
  open Cat C

```

## From paths to isomorphisms

`idtoiso` transports the reflexive isomorphism along a path of
objects. Its value at `refl` is `iso-refl` by `J-refl`, but only
propositionally: `idtoiso refl` does not reduce definitionally,
so the underlying-morphism law `idtoiso-refl-hom` is recorded
explicitly for later rewriting.

```agda
  -- Following Rijke Ch 5 (J); cf. 1lab Cat.Univalent path→iso
  idtoiso : ∀ {x y} → x ≡ y → x ≅ y
  idtoiso {x} = J (λ y _ → x ≅ y) iso-refl

  idtoiso-refl : ∀ {x} → idtoiso {x} {x} refl ≡ iso-refl
  idtoiso-refl {x} = J-refl (λ y _ → x ≅ y) iso-refl

  idtoiso-refl-hom : ∀ {x} → idtoiso {x} {x} refl .fst ≡ idn
  idtoiso-refl-hom {x} = ap fst (idtoiso-refl {x})

```

## Dependent paths as squares

A dependent path between morphisms over object paths `p` and `q`
is the same data as a commuting square relating the two
morphisms through the induced identities. The proof is a double
`J` on `p` then `q`; the base case rewrites the two stuck
`idtoiso refl` sides back to identities via `idtoiso-refl-hom`.

```agda
  hom-PathP≡square
    : ∀ {x x' y y'} (p : x ≡ x') (q : y ≡ y')
    → (f : hom x y) (g : hom x' y')
    → (PathP (λ i → hom (p i) (q i)) f g)
      ≡ (f ⨾ idtoiso q .fst ≡ idtoiso p .fst ⨾ g)
  hom-PathP≡square {x} {x'} {y} {y'} p q f g =
    J (λ x₁ p₁ → (y₁ : ob) (q₁ : y ≡ y₁) (g₁ : hom x₁ y₁)
                 → (PathP (λ i → hom (p₁ i) (q₁ i)) f g₁)
                   ≡ (f ⨾ idtoiso q₁ .fst ≡ idtoiso p₁ .fst ⨾ g₁))
      outer-base p y' q g
    where
      inner-base
        : (g₁ : hom x y)
        → (f ≡ g₁)
          ≡ (f ⨾ idtoiso (refl {x = y}) .fst
             ≡ idtoiso (refl {x = x}) .fst ⨾ g₁)
      inner-base g₁ i = Lend (~ i) ≡ Rend (~ i) where
        Lend : (f ⨾ idtoiso (refl {x = y}) .fst) ≡ f
        Lend = (f ◃ idtoiso-refl-hom {y}) ∙ unitr f

        Rend : (idtoiso (refl {x = x}) .fst ⨾ g₁) ≡ g₁
        Rend = (idtoiso-refl-hom {x} ▹ g₁) ∙ unitl g₁

      outer-base
        : (y₁ : ob) (q₁ : y ≡ y₁) (g₁ : hom x y₁)
        → (PathP (λ i → hom x (q₁ i)) f g₁)
          ≡ (f ⨾ idtoiso q₁ .fst ≡ idtoiso (refl {x = x}) .fst ⨾ g₁)
      outer-base y₁ q₁ g₁ =
        J (λ y₂ q₂ → (g₂ : hom x y₂)
                     → (PathP (λ i → hom x (q₂ i)) f g₂)
                       ≡ (f ⨾ idtoiso q₂ .fst
                          ≡ idtoiso (refl {x = x}) .fst ⨾ g₂))
          inner-base q₁ g₁

```

Promoting the path of types to an equivalence uses only
`transport-equiv`, keeping the module within the
`--erased-cubical` flag profile. The forward and backward
projections are the concrete maps consumers call.

```agda
  hom-PathP≃square
    : ∀ {x x' y y'} (p : x ≡ x') (q : y ≡ y')
    → {f : hom x y} {g : hom x' y'}
    → PathP (λ i → hom (p i) (q i)) f g
      ≃ (f ⨾ idtoiso q .fst ≡ idtoiso p .fst ⨾ g)
  hom-PathP≃square p q {f} {g}
    = transport (hom-PathP≡square p q f g)
    , transport-equiv (hom-PathP≡square p q f g)

  hom-PathP→square
    : ∀ {x x' y y'} (p : x ≡ x') (q : y ≡ y')
    → {f : hom x y} {g : hom x' y'}
    → PathP (λ i → hom (p i) (q i)) f g
    → f ⨾ idtoiso q .fst ≡ idtoiso p .fst ⨾ g
  hom-PathP→square p q {f} {g} = transport (hom-PathP≡square p q f g)

  square→hom-PathP
    : ∀ {x x' y y'} (p : x ≡ x') (q : y ≡ y')
    → {f : hom x y} {g : hom x' y'}
    → f ⨾ idtoiso q .fst ≡ idtoiso p .fst ⨾ g
    → PathP (λ i → hom (p i) (q i)) f g
  square→hom-PathP p q {f} {g} = transport⁻ (hom-PathP≡square p q f g)

```
