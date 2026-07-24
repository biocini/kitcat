Augmented simplices and lists, after Sterling, *Reflexive Graph Lenses*,
§ "Example: definitional lenses for finite ordinals" and § "Lists". The reflexive
graph `AugSpx` has the naturals as vertices and monotone equivalences of finite
ordinals as edges. It is a path object because the category of augmented
simplices is gaunt: at most one monotone equivalence relates two finite ordinals,
and a monotone equivalence forces their sizes equal.

Lists valued in a path object arise as the partial products of `AugSpx` with the
family of finite ordinals `𝔉`, whose transport is the underlying map of a
monotone equivalence — a definitional lens, unital on the nose at the identity.

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Cat.Graph.Refl.Simplex where

open import Core.Type
open import Core.Base
open import Core.Kan using (_∙_)
open import Core.Data.Sigma
open import Core.Data.Nat using (Nat)
open import Core.Data.Fin.Type using (Fin)
open import Core.Data.Fin.Monotone.Type using (is-monotone)
open import Core.Data.Fin.Monotone.Gaunt
  using (mono-unique; mono-card; is-monotone-is-prop)
open import Core.Equiv using (_≃_; Equiv; aut; equiv-path)
open import Core.HLevel.Base using (Σ-prop-path)
open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base
open import Cat.Graph.Refl.Poly

```

## The reflexive graph of augmented simplices

Vertices are the naturals; an edge from `m` to `n` is a monotone equivalence of
the finite ordinals `Fin m` and `Fin n`; reflexivity is the identity, monotone by
inspection.

```agda

AugSpx : reflexive-graph 0ℓ 0ℓ
AugSpx .reflexive-graph.vtx        = Nat
AugSpx .reflexive-graph.edge m n   = Σ e ∶ (Fin m ≃ Fin n) , is-monotone (e .fst)
AugSpx .reflexive-graph.rx n       = aut , λ _ _ le → le

```

## Univalence

Each fan is a proposition. The edge type at fixed endpoints is a proposition
because a monotone equivalence is determined by its underlying map and that map
is unique; distinct fan targets coincide because each is the size of `m`.

```agda

private
  edge-prop : (m n : Nat) → is-prop (reflexive-graph.edge AugSpx m n)
  edge-prop m n (e , me) (e' , me') =
    Σ-prop-path (λ ee → is-monotone-is-prop (ee .fst))
      (equiv-path e e' (mono-unique e e' me me'))

AugSpx-path-object : rx.is-univalent AugSpx
AugSpx-path-object m (n₀ , e₀ , mono₀) (n₁ , e₁ , mono₁) =
  Σ-prop-path (edge-prop m) (sym (mono-card e₀ mono₀) ∙ mono-card e₁ mono₁)

```

## Lists

The finite ordinals form a family `𝔉` over `AugSpx` whose vertices are `Fin n`;
only the vertices figure in the partial product. Its transport pushes an index
forward along the underlying map of a monotone equivalence, unital on the nose
because the reflexive edge is the identity. Covariant and contravariant partial
products with a path object `𝒜` give the two list path objects; their common
vertex type is `Σ n , (Fin n → vtx 𝒜)`.

```agda

𝔉 : rx.vfam AugSpx 0ℓ 0ℓ
𝔉 n = discrete (Fin n)

List⁺ : ∀ {w z} → reflexive-graph w z → reflexive-graph w z
List⁺ 𝒜 = cov-poly AugSpx 𝔉 𝒜 (λ _ _ e u → e .fst .fst u) (λ _ → refl)

List⁻ : ∀ {w z} → reflexive-graph w z → reflexive-graph w z
List⁻ 𝒜 = ctrv-poly AugSpx 𝔉 𝒜 (λ _ _ e u → Equiv.inv (e .fst) u) (λ _ → refl)

List⁺-path-object : ∀ {w z} (𝒜 : reflexive-graph w z)
                  → rx.is-univalent 𝒜 → rx.is-univalent (List⁺ 𝒜)
List⁺-path-object 𝒜 =
  cov-poly-path-object AugSpx 𝔉 𝒜 (λ _ _ e u → e .fst .fst u) (λ _ → refl)
    AugSpx-path-object

List⁻-path-object : ∀ {w z} (𝒜 : reflexive-graph w z)
                  → rx.is-univalent 𝒜 → rx.is-univalent (List⁻ 𝒜)
List⁻-path-object 𝒜 =
  ctrv-poly-path-object AugSpx 𝔉 𝒜 (λ _ _ e u → Equiv.inv (e .fst) u) (λ _ → refl)
    AugSpx-path-object

```
