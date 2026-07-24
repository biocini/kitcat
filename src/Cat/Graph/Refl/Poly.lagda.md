Polynomials and partial products of reflexive graphs, after Sterling,
*Reflexive Graph Lenses*, § "Polynomials and partial products". A family with a
transport operator `push`/`pull` that is unital *up to a path* has a partial
product with any reflexive graph: the polynomial `Σ x , (vtx (B x) → vtx C)`, made
a reflexive graph by transporting `C`-reflexivity along the transport. It is a path
object whenever the base and `C` are, with no condition on `B`.

The transport is asked to be unital up to a *path* rather than definitionally, as
Sterling's definitional lenses are. A definitional lens' unit law is a judgemental
equality `push (rx x) ≐ id`, which no type in Martin-Löf type theory expresses; the
path `push-rx` is the propositional stand-in. At an instance where the equality does
hold judgementally, `push-rx` is `refl`, and the unitor is `C`-reflexivity up to the
regularity gap of `to-edge` on `refl`.

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Cat.Graph.Refl.Poly where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma using (fst)
open import Core.Equiv using (Equiv)
open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base
open import Cat.Graph.Refl.Properties
open import Cat.Graph.Refl.Lens
```

## Covariant partial product

A forward transport `push`, unital up to a path, over a family `B` on a base `A`.
The covariant partial product's component at `x` is the cotensor `vtx (B x) ⋔ C`;
its lax contravariant lens pulls a section back by precomposition with `push`, and
the unitor transports `C`-reflexivity along the path witnessing `push`'s unitality.

```agda

module _ {v e w z w' z'} (A : reflexive-graph v e) (B : rx.vfam A w z) (C : reflexive-graph w' z')
  (push   : (x y : reflexive-graph.vtx A) → reflexive-graph.edge A x y
          → reflexive-graph.vtx (B x) → reflexive-graph.vtx (B y))
  (push-rx : ∀ {x} (u : reflexive-graph.vtx (B x)) → push x x (reflexive-graph.rx A x) u ≡ u)
  where
  private module A = reflexive-graph A

  cov-pp : rx.vfam A (w ⊔ w') (w ⊔ z')
  cov-pp x = rx.cotensor C (reflexive-graph.vtx (B x))

  cov-pp-lens : lax-ctrv-lens A cov-pp
  cov-pp-lens .lax-ctrv-lens.has-pull x y p c u = c (push x y p u)
  cov-pp-lens .lax-ctrv-lens.has-unitor c u = rx.to-edge C (ap c (sym (push-rx u)))

  cov-poly : reflexive-graph (v ⊔ w ⊔ w') (e ⊔ w ⊔ z')
  cov-poly = rx.total A (lax-ctrv-lens.display cov-pp-lens)

  cov-poly-path-object : rx.is-univalent A → rx.is-univalent C → rx.is-univalent cov-poly
  cov-poly-path-object A-univ C-univ =
    total-path-object (lax-ctrv-lens.display cov-pp-lens) A-univ
      (ctrv-disp-path-object cov-pp-lens
        λ x → cotensor-path-object C (reflexive-graph.vtx (B x)) C-univ)
```

## Contravariant partial product

The dual: a backward transport `pull`, unital up to a path. The component is the
same cotensor; its oplax covariant lens pushes a section by precomposition with
`pull`, and the unitor again transports `C`-reflexivity along the path.

```agda

module _ {v e w z w' z'} (A : reflexive-graph v e) (B : rx.vfam A w z) (C : reflexive-graph w' z')
  (pull   : (x y : reflexive-graph.vtx A) → reflexive-graph.edge A x y
          → reflexive-graph.vtx (B y) → reflexive-graph.vtx (B x))
  (pull-rx : ∀ {x} (u : reflexive-graph.vtx (B x)) → pull x x (reflexive-graph.rx A x) u ≡ u)
  where
  private module A = reflexive-graph A

  ctrv-pp : rx.vfam A (w ⊔ w') (w ⊔ z')
  ctrv-pp x = rx.cotensor C (reflexive-graph.vtx (B x))

  ctrv-pp-lens : oplax-cov-lens A ctrv-pp
  ctrv-pp-lens .oplax-cov-lens.has-push x y p c u = c (pull x y p u)
  ctrv-pp-lens .oplax-cov-lens.has-unitor c u = rx.to-edge C (ap c (pull-rx u))

  ctrv-poly : reflexive-graph (v ⊔ w ⊔ w') (e ⊔ w ⊔ z')
  ctrv-poly = rx.total A (oplax-cov-lens.display ctrv-pp-lens)

  ctrv-poly-path-object : rx.is-univalent A → rx.is-univalent C → rx.is-univalent ctrv-poly
  ctrv-poly-path-object A-univ C-univ =
    total-path-object (oplax-cov-lens.display ctrv-pp-lens) A-univ
      (cov-disp-path-object ctrv-pp-lens
        λ x → cotensor-path-object C (reflexive-graph.vtx (B x)) C-univ)
```

## Partial map classifiers

The partial map classifier of `C` in a dominance `(S , T)` — a univalent family
whose fibres are propositions — is the polynomial `Σ φ , (T φ → vtx C)`. It lifts
to a path object by either partial product: the codiscrete family on `T` supplies
the fibres, and the base image of `T` supplies the transport, unital at
reflexivity. The lift is a path object whenever the family and `C` are; that the
fibres are propositions is what makes `(S , T)` a dominance, but the partial
product does not use it.

```agda

module _ {ℓ ℓ' w z} {S : Type ℓ} (T : S → Type ℓ') (C : reflexive-graph w z) where

  pmc⁺ : reflexive-graph (ℓ ⊔ ℓ' ⊔ w) (ℓ' ⊔ z)
  pmc⁺ = cov-poly (image T) (λ φ → codiscrete (T φ)) C (λ _ _ f u → f .fst u) (λ _ → refl)

  pmc⁻ : reflexive-graph (ℓ ⊔ ℓ' ⊔ w) (ℓ' ⊔ z)
  pmc⁻ = ctrv-poly (image T) (λ φ → codiscrete (T φ)) C (λ _ _ f u → Equiv.inv f u) (λ _ → refl)

  pmc⁺-path-object : is-univalent-family T → rx.is-univalent C → rx.is-univalent pmc⁺
  pmc⁺-path-object T-univ C-univ =
    cov-poly-path-object (image T) (λ φ → codiscrete (T φ)) C (λ _ _ f u → f .fst u) (λ _ → refl)
      T-univ C-univ

  pmc⁻-path-object : is-univalent-family T → rx.is-univalent C → rx.is-univalent pmc⁻
  pmc⁻-path-object T-univ C-univ =
    ctrv-poly-path-object (image T) (λ φ → codiscrete (T φ)) C (λ _ _ f u → Equiv.inv f u) (λ _ → refl)
      T-univ C-univ
```
