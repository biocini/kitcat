Lane Biocini
February 2026

Product of virtual graphs. Given two virtual graphs V and W, the product
has pairs of objects, pairs of morphisms, and componentwise Yoneda action.
The embedding property follows from the component embeddings via an
ap-equivalence argument.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Bb.UnitalMagmoids.Magmoid

module Bb.UnitalMagmoids.Prod (V W : virtual-graphs) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv
open import Core.Function.Embedding
  using ( is-embedding; is-embedding→contr-fibers
        ; is-embedding→ap-equiv; image-fibers-contr→is-embedding
        ; ap-equiv→image-fibers-contr )
import Bb.UnitalMagmoids.Base

private
  module V = virtual-graphs V
  module W = virtual-graphs W
```

## Product yon

```agda
private
  yon-prod
    : ∀ {x y : V.ob × W.ob}
    → V.hom (fst x) (fst y) × W.hom (snd x) (snd y)
    → ∀ (w : V.ob × W.ob)
    → V.hom (fst w) (fst x) × W.hom (snd w) (snd x)
    → V.hom (fst w) (fst y) × W.hom (snd w) (snd y)
  yon-prod (f₁ , f₂) (w₁ , w₂) (k₁ , k₂) =
    V.yon f₁ w₁ k₁ , W.yon f₂ w₂ k₂
```

## Product embedding

The embedding of `yon-prod` is disabled below, along with the product
magmoid it supports. Its route runs through an equivalence between paths
of product morphisms and paths of product Yoneda functions, whose
retraction asks that a path between two componentwise Yoneda actions
carry no dependence of one component on the other's coordinates in its
interior. Contracting the fiber of `V.yon` identifies the two candidate
paths only over a loop in `hom`, so the retraction closes exactly when
the hom types are sets — an assumption unavailable here, homs being
untruncated by design.

```agda
-- private
--   yon-prod-≡-equiv
--     : ∀ {x y : V.ob × W.ob}
--       (f g : V.hom (fst x) (fst y)
--            × W.hom (snd x) (snd y))
--     → (V.yon (fst f) ≡ V.yon (fst g))
--     × (W.yon (snd f) ≡ W.yon (snd g))
--     ≃ (yon-prod f ≡ yon-prod g)
--   yon-prod-≡-equiv {x = x} {y = y} f g = iso→equiv fwd bwd sec retr
--     where
--       fwd : (V.yon (fst f) ≡ V.yon (fst g))
--           × (W.yon (snd f) ≡ W.yon (snd g))
--           → yon-prod f ≡ yon-prod g
--       fwd (α , β) i w k =
--         ( α i (fst w) (fst k)
--         , β i (snd w) (snd k)
--         )
--
--       bwd : yon-prod f ≡ yon-prod g
--           → (V.yon (fst f) ≡ V.yon (fst g))
--           × (W.yon (snd f) ≡ W.yon (snd g))
--       bwd γ =
--         ( (λ i w₁ k₁ → fst (γ i (w₁ , snd x) (k₁ , W.idn)))
--         , (λ i w₂ k₂ → snd (γ i (fst x , w₂) (V.idn , k₂)))
--         )
--
--       sec : (q : (V.yon (fst f) ≡ V.yon (fst g))
--                × (W.yon (snd f) ≡ W.yon (snd g)))
--           → bwd (fwd q) ≡ q
--       sec (α , β) = refl
--
--       retr : (γ : yon-prod f ≡ yon-prod g)
--            → fwd (bwd γ) ≡ γ
--       retr γ = funext λ i → funext λ w → funext λ k → λ j →
--         (V-eq i w k j , W-eq i w k j)
--         where
--           x₁ = fst x
--           x₂ = snd x
--           f₁ = fst f
--           g₁ = fst g
--           f₂ = snd f
--           g₂ = snd g
--
--           δV : (w₂ : W.ob) (k₂ : W.hom w₂ x₂)
--              → V.yon f₁ ≡ V.yon g₁
--           δV w₂ k₂ i w₁ k₁ =
--             fst (γ i (w₁ , w₂) (k₁ , k₂))
--
--           δV-dummy : V.yon f₁ ≡ V.yon g₁
--           δV-dummy i w₁ k₁ =
--             fst (γ i (w₁ , x₂) (k₁ , W.idn))
--
--           v-fib : (w₂ : W.ob) (k₂ : W.hom w₂ x₂)
--                 → fiber V.yon (V.yon f₁)
--           v-fib w₂ k₂ =
--             g₁ , sym (λ i → δV w₂ k₂ i)
--
--           v-fib-dummy : fiber V.yon (V.yon f₁)
--           v-fib-dummy =
--             g₁ , sym δV-dummy
--
--           v-center : is-contr (fiber V.yon (V.yon f₁))
--           v-center = is-embedding→contr-fibers V.yon-emb (f₁ , refl)
--
--           δV≡ : (w₂ : W.ob) (k₂ : W.hom w₂ x₂)
--               → v-fib w₂ k₂ ≡ v-fib-dummy
--           δV≡ w₂ k₂ =
--             is-contr→is-prop v-center (v-fib w₂ k₂) v-fib-dummy
--
--           V-path≡ : (w₂ : W.ob) (k₂ : W.hom w₂ x₂)
--                   → (λ i w₁ k₁ → δV w₂ k₂ i w₁ k₁) ≡ δV-dummy
--           V-path≡ w₂ k₂ = ap sym (ap snd (δV≡ w₂ k₂))
--
--           V-eq : ∀ i w k
--                → fst (fwd (bwd γ) i w k)
--                ≡ fst (γ i w k)
--           V-eq i w k =
--             sym ( happly (happly (happly (V-path≡ (snd w) (snd k)) i)
--                           (fst w)) (fst k) )
--
--           δW : (w₁ : V.ob) (k₁ : V.hom w₁ x₁)
--              → W.yon f₂ ≡ W.yon g₂
--           δW w₁ k₁ i w₂ k₂ =
--             snd (γ i (w₁ , w₂) (k₁ , k₂))
--
--           δW-dummy : W.yon f₂ ≡ W.yon g₂
--           δW-dummy i w₂ k₂ =
--             snd (γ i (x₁ , w₂) (V.idn , k₂))
--
--           w-fib : (w₁ : V.ob) (k₁ : V.hom w₁ x₁)
--                 → fiber W.yon (W.yon f₂)
--           w-fib w₁ k₁ =
--             g₂ , sym (λ i → δW w₁ k₁ i)
--
--           w-fib-dummy : fiber W.yon (W.yon f₂)
--           w-fib-dummy =
--             g₂ , sym δW-dummy
--
--           w-center : is-contr (fiber W.yon (W.yon f₂))
--           w-center = is-embedding→contr-fibers W.yon-emb (f₂ , refl)
--
--           δW≡ : (w₁ : V.ob) (k₁ : V.hom w₁ x₁)
--               → w-fib w₁ k₁ ≡ w-fib-dummy
--           δW≡ w₁ k₁ =
--             is-contr→is-prop w-center (w-fib w₁ k₁) w-fib-dummy
--
--           W-path≡ : (w₁ : V.ob) (k₁ : V.hom w₁ x₁)
--                   → (λ i w₂ k₂ → δW w₁ k₁ i w₂ k₂) ≡ δW-dummy
--           W-path≡ w₁ k₁ = ap sym (ap snd (δW≡ w₁ k₁))
--
--           W-eq : ∀ i w k
--                → snd (fwd (bwd γ) i w k)
--                ≡ snd (γ i w k)
--           W-eq i w k =
--             sym ( happly (happly (happly (W-path≡ (fst w) (fst k)) i)
--                           (snd w)) (snd k) )
--
--   yon-prod-ap-equiv
--     : ∀ {x y : V.ob × W.ob} {f g}
--     → is-equiv (ap yon-prod {x} {y} {f} {g})
--   yon-prod-ap-equiv {f = f} {g} =
--     comp-equiv (comp-equiv e₁ e₂) e₃
--     where
--       e₁ = ×-path-equiv .snd
--       e₂ = ×-is-equiv (is-embedding→ap-equiv V.yon-emb)
--                       (is-embedding→ap-equiv W.yon-emb)
--       e₃ = yon-prod-≡-equiv f g .snd
--
--   yon-prod-image-contr
--     : ∀ {x y : V.ob × W.ob}
--       (m : V.hom (fst x) (fst y)
--          × W.hom (snd x) (snd y))
--     → is-contr (fiber yon-prod (yon-prod m))
--   yon-prod-image-contr {x} {y} m =
--     ap-equiv→image-fibers-contr
--       (λ n → yon-prod-ap-equiv {f = m} {g = n})
--
--   yon-prod-emb
--     : ∀ {x y : V.ob × W.ob}
--     → is-embedding (yon-prod {x} {y})
--   yon-prod-emb =
--     image-fibers-contr→is-embedding yon-prod-image-contr
```

## Product magmoid

```agda
-- prod : magmoids
-- prod = str
--   (V.ob × W.ob)
--   (λ x y →
--     V.hom (fst x) (fst y) × W.hom (snd x) (snd y))
--   yon-prod
--   yon-prod-emb
```

```agda
-- open Bb.UnitalMagmoids.Base prod public
```
