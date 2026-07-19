Lane Biocini
July 2026

The terminal category, as a `Cat.Type` category.

One object, contractible homs. Every structural type — contexts,
composites, spines — is contractible, so the axioms are discharged
by the contractibility machinery alone. This is the unit for the
product line of constructions.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Terminal where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Agda.Builtin.Unit using (⊤; tt)
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.Properties using (weak-funext)
open import Core.HLevel.Base using (⊤-is-contr; PathP-is-contr)

open import Cat.Type

terminal-graph : reflexive-graph 0ℓ 0ℓ
terminal-graph .reflexive-graph.ob = ⊤
terminal-graph .reflexive-graph.edge _ _ = ⊤
terminal-graph .reflexive-graph.rx _ = tt

module V = virtual terminal-graph
open V
```

## Contractibility of the structural types

```agda
ob-contr : is-contr ob
ob-contr = ⊤-is-contr

hom-contr : ∀ {x y} → is-contr (hom x y)
hom-contr = ⊤-is-contr

over-contr : ∀ {x} → is-contr (over x)
over-contr = Σ-contr-contr ⊤-is-contr λ _ → ⊤-is-contr

under-contr : ∀ {x} → is-contr (under x)
under-contr = Σ-contr-contr ⊤-is-contr λ _ → ⊤-is-contr

ctx-contr : ∀ {x y} → is-contr (ctx x y)
ctx-contr = Σ-contr-contr over-contr λ _ → under-contr

res-contr : ∀ {x y} (γ : ctx x y) → is-contr (res γ)
res-contr _ = ⊤-is-contr

composite-contr : ∀ {x y} → is-contr (composite x y)
composite-contr = weak-funext λ γ → ⊤-is-contr
```

## The axioms

Every field is a contractibility statement over contractible types.

```agda
private
  temb : ∀ {x y} → hom x y → composite x y
  temb f γ = tt

  open representable terminal-graph temb

  Spine : ∀ {x y z} (f : hom x y) (g : hom y z) → Type 0ℓ
  Spine {x} {z} f g =
    Σ k ∶ hom x z ,
    Σ p ∶ (temb k ≡ temb f ▾ g) ,
    Σ q ∶ (temb k ≡ f ▴ temb g) ,
      PathP (λ i → temb k ≡
        is-contr→is-prop composite-contr (temb f ▿ temb g) (temb f ▵ temb g) i)
        p q

  spine-contr-impl : ∀ {x y z} (f : hom x y) (g : hom y z) → is-contr (Spine f g)
  spine-contr-impl f g =
    Σ-contr-contr hom-contr λ k →
    Σ-contr-contr
      (PathP-is-contr composite-contr (temb k) (temb f ▾ g)) λ p →
    Σ-contr-contr
      (PathP-is-contr composite-contr (temb k) (f ▴ temb g)) λ q →
      PathP-is-contr
        (PathP-is-contr composite-contr (temb k) _)
        p q

terminal-axioms : category-axioms terminal-graph
terminal-axioms .category-axioms.emb = temb
terminal-axioms .category-axioms.interchange♭ {x} {z} U V =
  is-contr→is-prop (composite-contr {x} {z}) _ _
terminal-axioms .category-axioms.spine-contr = spine-contr-impl
terminal-axioms .category-axioms.unit f =
  is-contr→is-prop hom-contr _ _

terminal-category : category 0ℓ 0ℓ
terminal-category .category.structure = terminal-graph
terminal-category .category.axioms = terminal-axioms
```

## The terminal object

Its unique object is terminal: every hom into it is contractible.

```agda
open import Cat.Limits.Terminal

terminal-obj-is-terminal
  : is-terminal terminal-category tt
terminal-obj-is-terminal X = hom-contr
```
