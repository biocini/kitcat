The framing in reflexive-graph language. A twist family is a
reflexivity datum, so a framing is a pair of reflexive graphs
sharing vertices and edges, and the sequent vocabulary is that
graph's fan calculus: a term is a cofan, a coterm a fan, and the two
argument halves are the centres the two framings supply, one from
each. Nothing here consumes an axiom, and this is where the tree
names the live `Core.Rx`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Graph where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma

open import Core.Rx.Type
open import Core.Rx.Base

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding using (opⱽ)
open import Bb.VirtualGraphs.Framing
```

## The graph of a twist family

```agda
rxgraph : ∀ {o h} (G : virtual-graph o h)
        → ((x : virtual-graph.ob G) → virtual-graph.hom G x x)
        → reflexive-graph o h
rxgraph G t .reflexive-graph.vtx  = virtual-graph.ob G
rxgraph G t .reflexive-graph.edge = virtual-graph.hom G
rxgraph G t .reflexive-graph.rx   = t
```

The opposite carrier's graph at a family is the reflexive-graph
opposite of this carrier's graph at the same family; read at a
swapped framing, each graph of the opposite is the opposite of the
other graph of the original.

```agda
op-rxgraph : ∀ {o h} (G : virtual-graph o h)
             (t : (x : virtual-graph.ob G) → virtual-graph.hom G x x)
           → rxgraph (opⱽ G) t ≡ rx.op (rxgraph G t)
op-rxgraph G t = refl
```

## The dictionary

```agda
module graphs {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) where

  open framing G rx corx

  graph⁺ graph⁻ : reflexive-graph o h
  graph⁺ = rxgraph G corx
  graph⁻ = rxgraph G rx
```

Fans and cofans name no reflexivity, so the term and coterm families
are read off either graph. Their centres are not: the term half is
the cofan centre of the negative graph, the coterm half the fan
centre of the positive one, and the axiom pairs one from each.
Univalence is a condition on fans alone, so the two graphs satisfy
it together and the framing does not enter it.

```agda
  term-is-cofan : ∀ x → term x ≡ rx.cofan graph⁺ x
  term-is-cofan _ = refl

  coterm-is-fan : ∀ y → coterm y ≡ rx.fan graph⁺ y
  coterm-is-fan _ = refl

  var-is-cofan-center : ∀ x → var x ≡ rx.cofan-center graph⁻ x
  var-is-cofan-center _ = refl

  covar-is-fan-center : ∀ y → covar y ≡ rx.fan-center graph⁺ y
  covar-is-fan-center _ = refl

  univalence-shared : rx.is-univalent graph⁺ ≡ rx.is-univalent graph⁻
  univalence-shared = refl
```

## The two-sided base

A judgment is contravariant in the term index and covariant in the
coterm index, and the base carrying that pair of variances is the
binary product of the negative graph's opposite with the positive
graph. Its reflexive edge at a diagonal vertex is the pair of twists
— the axiom, as one edge. Both slots travel at once under `bipush`;
each action preserves its anonymous endpoint, so the conclusion is
untouched and no transport appears.

```agda
module two-sided {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) where

  open framing G rx corx
  open graphs G rx corx

  base : reflexive-graph o h
  base = rx.binary-product (rx.op graph⁻) graph⁺

  base-vtx : reflexive-graph.vtx base ≡ (ob × ob)
  base-vtx = refl

  base-edge : ∀ x y x' y'
            → reflexive-graph.edge base (x , y) (x' , y') ≡ (hom x' x × hom y y')
  base-edge _ _ _ _ = refl

  base-rx-is-axiom : ∀ x y
                   → reflexive-graph.rx base (x , y) ≡ (var x .snd , covar y .snd)
  base-rx-is-axiom _ _ = refl

  bipush : ∀ {x y x' y'} → hom x' x → hom y y' → judgment x y → judgment x' y'
  bipush a b α γ = α (act a (γ .fst) , coact b (γ .snd))

  judgment-fam : rx.vfam base (o ⊔ h) (o ⊔ h)
  judgment-fam c = discrete (judgment (c .fst) (c .snd))
```

## The one-sided families

Each family sits over the graph of the twist its own axiom half does
not carry, since that is the twist its action is stated at.

```agda
module families {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) where

  open graphs G rx corx

  term-fam : rx.vfam graph⁻ (o ⊔ h) (o ⊔ h)
  term-fam x = discrete (term x)

  coterm-fam : rx.vfam graph⁺ (o ⊔ h) (o ⊔ h)
  coterm-fam y = discrete (coterm y)
```
