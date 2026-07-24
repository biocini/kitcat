The foundation for the reflexive graph library, after Sterling's
*Reflexive Graph Lenses*. A reflexive graph is a type of vertices, a family
of edges between them, and a chosen edge at every vertex.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Graph.Refl.Type where

open import Core.Type

```

## Reflexive graphs

Vertices `vtx`, an edge family `edge`, and a reflexive edge `rx` at every vertex.

```agda

record reflexive-graph v e : Type₊ (v ⊔ e) where
  field
    vtx  : Type v
    edge : vtx → vtx → Type e
    rx   : (x : vtx) → edge x x
```

## Displayed reflexive graphs

A displayed reflexive graph over a base `G`: a family of vertices and edges
lying over those of `G`, together with a displayed reflexive edge.

```agda

record reflexive-graphᴰ {v e} v' e' (G : reflexive-graph v e) : Type (v ⊔ e ⊔ v' ₊ ⊔ e' ₊) where
  private module G = reflexive-graph G
  field
    vtx : G.vtx → Type v'
    edge : (x y : G.vtx) → G.edge x y → vtx x → vtx y → Type e'
    rx : {x : G.vtx} (u : vtx x) → edge x x (G.rx x) u u


