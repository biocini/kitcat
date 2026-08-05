Representability and the embedding condition over the bare carrier,
and the opposite. Nothing here reads a twist: every statement is a
condition on `reflect` alone.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Embedding where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Path.Base using (ap-comp)
open import Core.Transport.J using (J)
open import Core.Transport.Properties
  using (is-prop-is-prop; is-prop→is-set; prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; is-prop-equiv; Π-is-hlevel)
open import Core.Function.Embedding using (is-embedding; injective→is-embedding)
open import Core.Equiv.Base using (iso→equiv; _≃_)

open import Bb.VirtualGraphs.Type
```

## Representability

A judgment is representable when it is the reflection of an edge.
Every edge represents its own reflection, and the whole hom type is
equivalent to the total space of represented judgments.

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G

  is-representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  is-representable = fiber reflect

  normal : ∀ {x y} (f : hom x y) → is-representable (reflect f)
  normal f = f , refl

  hom≃total-representable
    : ∀ {x y} → hom x y ≃ (Σ α ∶ judgment x y , is-representable α)
  hom≃total-representable {x} {y} = iso→equiv fwd bwd hom-ret rep-sec
    where
      fwd : hom x y → Σ F ∶ judgment x y , is-representable F
      fwd f = reflect f , (f , refl)

      bwd : (Σ α ∶ judgment x y , is-representable α) → hom x y
      bwd (_ , a , _) = a

      hom-ret : ∀ f → bwd (fwd f) ≡ f
      hom-ret f = refl

      rep-sec : ∀ s → fwd (bwd s) ≡ s
      rep-sec (_ , a , p) = J (λ F' p' → fwd a ≡ (F' , a , p')) refl p
```

## The embedding condition

Representation is unique where it occurs. Propositional fibers is
what an embedding is, so the embedding condition is `reflect` being
one at every pair of objects.

```agda
  reflect-is-embedding : Type (o ⊔ h)
  reflect-is-embedding = ∀ {x y} (α : judgment x y) → is-prop (is-representable α)

  reflect-is-embedding-is-prop : is-prop reflect-is-embedding
  reflect-is-embedding-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → is-prop-is-prop _

  reflect-lc : reflect-is-embedding → ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-lc S {n = n} p = ap fst (S (reflect n) (_ , p) (normal n))

  contr-from-embedding
    : reflect-is-embedding → ∀ {x y} (α : judgment x y)
    → is-representable α → is-contr (is-representable α)
  contr-from-embedding S α = prop-inhabited→is-contr (S α)

  reflect-is-embedding-unfolds : reflect-is-embedding ≡ (∀ {x y} → is-embedding (reflect {x} {y}))
  reflect-is-embedding-unfolds = refl
```

Two representations of one judgment name a path of edges twice
over: cancel `reflect` across the loop that runs through the
judgment, or project the fiber's own path. The two agree, so any
construction stated through the cancellation transports to one
stated in the fiber.

```agda
  reflect-lc-fiber
    : (S : reflect-is-embedding) {x y : ob} (α : judgment x y)
      (u v : is-representable α)
    → reflect-lc S {m = u .fst} {n = v .fst} (u .snd ∙ sym (v .snd))
    ≡ ap fst (S α u v)
  reflect-lc-fiber S α u v =
      ap (ap fst)
        (is-prop→is-set P (φ u) (normal n) (P (φ u) (normal n))
          (P (φ u) (φ v) ∙ P (φ v) (normal n)))
    ∙ ap-comp fst (P (φ u) (φ v)) (P (φ v) (normal n))
    ∙ ap2s _∙_ head tail
    ∙ Path.unitr (ap fst (S α u v))
    where
      n = v .fst

      P : is-prop (is-representable (reflect n))
      P = S (reflect n)

      φ : is-representable α → is-representable (reflect n)
      φ w = w .fst , w .snd ∙ sym (v .snd)

      head : ap fst (P (φ u) (φ v)) ≡ ap fst (S α u v)
      head = ap (ap fst)
        (is-prop→is-set P (φ u) (φ v) (P (φ u) (φ v)) (ap φ (S α u v)))

      tail : ap fst (P (φ v) (normal n)) ≡ refl
      tail = ap (ap fst)
        (is-prop→is-set P (φ v) (normal n) (P (φ v) (normal n))
          (λ i → n , Path.invr (v .snd) i))
```

Where the edges form sets the judgments do too, and an embedding is
then an injection: the embedding condition reduces to injectivity of
`reflect`.

```agda
  embedding-from-injective
    : (∀ {x y} → is-set (hom x y))
    → (∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n)
    → reflect-is-embedding
  embedding-from-injective hset inj α =
    injective→is-embedding (Π-is-hlevel 2 λ _ → hset) reflect inj α
```

## The opposite

Reversing edges exchanges the two argument halves. The carrier has no
further fields, so doing it twice returns the record on the nose.

```agda
opⱽ : ∀ {o h} → virtual-graph o h → virtual-graph o h
opⱽ G .virtual-graph.ob        = virtual-graph.ob G
opⱽ G .virtual-graph.hom x y   = virtual-graph.hom G y x
opⱽ G .virtual-graph.reflect f γ = virtual-graph.reflect G f (γ .snd , γ .fst)

opⱽ-invol : ∀ {o h} (G : virtual-graph o h) → opⱽ (opⱽ G) ≡ G
opⱽ-invol G = refl
```

The embedding condition crosses the opposite by reindexing a judgment
along the argument exchange, which is an equivalence on fibers.

```agda
op-embedding : ∀ {o h} (G : virtual-graph o h)
             → reflect-is-embedding G → reflect-is-embedding (opⱽ G)
op-embedding G S α =
  is-prop-equiv
    (iso→equiv (λ w → w .fst , λ i δ → w .snd i (δ .snd , δ .fst))
               (λ w → w .fst , λ i γ → w .snd i (γ .snd , γ .fst))
               (λ _ → refl) (λ _ → refl))
    (S (λ δ → α (δ .snd , δ .fst)))
```
