Inference measurement: a structure that *contains* its reflexive graph
loses the graph at use sites; one *indexed over* it keeps the graph.

Both records carry the same content — a ternary action over a
reflexive graph — and differ only in whether the graph is a field or a
parameter. Each probe is keyed on a displayed graph and must recover
the underlying graph from it.

The indexed form solves: the graph is record-headed in the display's
type, so unification reaches it. The bundled form does not: the graph
sits behind `vg-bundled.graph ?V`, a stuck projection on a variable —
the projection-reached tier. The negative half is recorded below
rather than typechecked, an unsolved metavariable being an error.

The consequence for a bundled record is not that it cannot be used,
only that graph-keyed signatures name the structure explicitly and the
interface is keyed off a module parametrized by it.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.RxBundle where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Rx.Type
open import Core.Rx.Base

-- (A) bundled: the graph is a field
record vg-bundled o h : Type₊ (o ⊔ h) where
  field
    graph : reflexive-graph o h
  open reflexive-graph graph public
  field
    reflect : ∀ {x y} → edge x y → ∀ w → edge w x → ∀ z → edge y z → edge w z

-- (B) indexed: the graph is a parameter, matching reflexive-graphᴰ
--     and the lens records
record vg-over {o h} (G : reflexive-graph o h) : Type (o ⊔ h) where
  private module G = reflexive-graph G
  field
    reflect : ∀ {x y} → G.edge x y
            → ∀ w → G.edge w x → ∀ z → G.edge y z → G.edge w z

over-probe : ∀ {o h v' e'} {G : reflexive-graph o h}
           → rx.disp G v' e' → Type o
over-probe {G = G} _ = reflexive-graph.vtx G

bundled-probe : ∀ {o h v' e'} {V : vg-bundled o h}
              → rx.disp (vg-bundled.graph V) v' e' → Type o
bundled-probe {V = V} _ = reflexive-graph.vtx (vg-bundled.graph V)

module _ {o h} (G : reflexive-graph o h) (D : rx.disp G 0ℓ 0ℓ) where

  -- (B) solves.
  use-over : Type o
  use-over = over-probe D

  -- (A) does not. Uncommenting yields
  --
  --   error: [UnsolvedMetaVariables]
  --   Unsolved metas at the following locations: <this line>
  --
  -- use-bundled : Type o
  -- use-bundled = bundled-probe D
```
