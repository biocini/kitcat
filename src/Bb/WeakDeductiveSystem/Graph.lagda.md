The framing in reflexive-graph language. A virtual graph's two twists
are two reflexive-graph structures on one underlying graph, and the
sequent vocabulary is that graph's fan calculus: a term is a cofan, a
coterm a fan, and the two argument halves are the centres the two
framings supply, one from each. Nothing here consumes an axiom, and this
is where the theory names `Core.Rx`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.WeakDeductiveSystem.Graph where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma

open import Core.Rx.Type
open import Core.Rx.Base

open import Bb.WeakDeductiveSystem.Type
open import Bb.WeakDeductiveSystem.Base using (opⱽ)
```

## The two graphs

Each twist is a reflexivity datum, so a framing is a pair of reflexive
graphs sharing vertices and edges.

```agda
graph⁺ graph⁻ : ∀ {o h} → virtual-graph o h → reflexive-graph o h

graph⁺ G .reflexive-graph.vtx  = virtual-graph.ob G
graph⁺ G .reflexive-graph.edge = virtual-graph.hom G
graph⁺ G .reflexive-graph.rx   = virtual-graph.twist⁺ G

graph⁻ G .reflexive-graph.vtx  = virtual-graph.ob G
graph⁻ G .reflexive-graph.edge = virtual-graph.hom G
graph⁻ G .reflexive-graph.rx   = virtual-graph.twist⁻ G
```

## The dictionary

Fans and cofans name no reflexivity, so the term and coterm families are
read off either graph. Their centres are not: the term half is the cofan
centre of the negative graph, the coterm half the fan centre of the
positive one, and the axiom pairs one from each.

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G

  term-is-cofan : ∀ x → term x ≡ rx.cofan (graph⁺ G) x
  term-is-cofan _ = refl

  coterm-is-fan : ∀ y → coterm y ≡ rx.fan (graph⁺ G) y
  coterm-is-fan _ = refl

  var-is-cofan-center : ∀ x → var x ≡ rx.cofan-center (graph⁻ G) x
  var-is-cofan-center _ = refl

  covar-is-fan-center : ∀ y → covar y ≡ rx.fan-center (graph⁺ G) y
  covar-is-fan-center _ = refl
```

Univalence is a condition on fans alone, so the two graphs satisfy it
together and the framing does not enter it.

```agda
  univalence-shared : rx.is-univalent (graph⁺ G) ≡ rx.is-univalent (graph⁻ G)
  univalence-shared = refl
```

## The opposite

Reversing edges exchanges the twists, so each graph of the opposite
virtual graph is the reflexive-graph opposite of the *other* graph of
the original.

```agda
op-graph⁺ : ∀ {o h} (G : virtual-graph o h) → graph⁺ (opⱽ G) ≡ rx.op (graph⁻ G)
op-graph⁺ _ = refl

op-graph⁻ : ∀ {o h} (G : virtual-graph o h) → graph⁻ (opⱽ G) ≡ rx.op (graph⁺ G)
op-graph⁻ _ = refl
```

## The two-sided base

A judgment is contravariant in the term index and covariant in the
coterm index, and the base carrying that pair of variances is the binary
product of the negative graph's opposite with the positive graph. Its
reflexive edge at a diagonal vertex is the pair of twists — the axiom,
as one edge.

```agda
module two-sided {o h} (G : virtual-graph o h) where
  open virtual-graph G

  base : reflexive-graph o h
  base = rx.binary-product (rx.op (graph⁻ G)) (graph⁺ G)

  base-vtx : reflexive-graph.vtx base ≡ (ob × ob)
  base-vtx = refl

  base-edge : ∀ x y x' y'
            → reflexive-graph.edge base (x , y) (x' , y') ≡ (hom x' x × hom y y')
  base-edge _ _ _ _ = refl

  base-rx-is-axiom : ∀ x y
                   → reflexive-graph.rx base (x , y) ≡ (var x .snd , covar y .snd)
  base-rx-is-axiom _ _ = refl
```

Both slots travel at once: the term half by the term action, the coterm
half by the coterm action. Each preserves its anonymous endpoint, so the
conclusion is untouched and no transport appears.

```agda
  bipush : ∀ {x y x' y'} → hom x' x → hom y y' → judgment x y → judgment x' y'
  bipush a b α γ = α (act a (γ .fst) , coact b (γ .snd))

  judgment-fam : rx.vfam base (o ⊔ h) (o ⊔ h)
  judgment-fam c = discrete (judgment (c .fst) (c .snd))
```

## The one-sided families

Each family sits over the graph of the twist its own axiom half does not
carry, since that is the twist its action is stated at.

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G

  term-fam : rx.vfam (graph⁻ G) (o ⊔ h) (o ⊔ h)
  term-fam x = discrete (term x)

  coterm-fam : rx.vfam (graph⁺ G) (o ⊔ h) (o ⊔ h)
  coterm-fam y = discrete (coterm y)
```
