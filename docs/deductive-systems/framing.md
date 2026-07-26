# The framing

A virtual graph carries no identity. It carries two families of
endo-edges, one at each half of an argument.

```agda
twist⁺ twist⁻ : (x : ob) → hom x x

var   x = x , twist⁻ x        -- the term half's axiom
covar y = y , twist⁺ y        -- the coterm half's axiom
axiom x = (var x , covar x)
eval  α = α (var x , covar y)
```

## Futures and buffers

Read asynchronously, a term is a **future** and a coterm a **buffer**.
The negative twist is the pending read, the positive the pending write,
and where they meet they cancel — a ready value fulfilling an expected
delivery. A variable is a future you force; a covariable is a mailbox
you enqueue into.

This fixes the polarity everywhere: `var` carries `twist⁻`, `covar`
carries `twist⁺`, and evaluation at the axiom surrounds an edge with one
of each. `eval (reflect f)` is `f` transmitted — winding-neutral, and
formable, because its payload is three edges and its twists are one of
each sign.

## Winding

Give `twist⁺` the winding `+1`, `twist⁻` the winding `−1`, and an
ordinary edge `0`. By the arity count of
[virtual-graphs.md](virtual-graphs.md), an expression with `k` payload
edges carries `2n + 1 − k` twists, so its twist count has the parity of
`k + 1`.

Three consequences, and they shape the whole theory.

- A statement about a **single** edge (payload one) can be
  winding-neutral: two twists, one of each sign. This is where the unit
  tiers live — see [unitality.md](unitality.md).
- A statement about **two** edges — a unit law written as "composing
  with this edge changes nothing" — carries an odd number of twists and
  can never be neutral.
- A **cut** of two edges (payload four) likewise carries an odd number,
  so each cut necessarily carries one twist at its junction, and the two
  cuts carry opposite ones. See [actions.md](actions.md).

So the framing is not decoration on a graph that already had units. It
is what makes the two halves sayable at all, and its winding is carried
by every composite the theory forms.

## What the framing is not asked to be

Nothing in the axioms constrains the twists. VERIFIED
(`Test.SpikeFramedCut`): the path groupoid on an arbitrary type, framed
by two arbitrary families of loops, satisfies every tier — `PG-deductive`
holds with no condition on the framing and no h-level hypothesis on the
carrier.

What the axioms *do* is make each twist the uniquely determined inverse
of the other. The two are pinned as the centres of the two unit tiers,
and nothing above them decides whether they cancel to the identity: that
is one equation, the framing's own content, and the theory holds either
way.

VERIFIED (`Test.SpikeFramedCut`): `cancels` is a single equation — the
composite of the two twists at an object is trivial — and both hands'
cancellation conditions, `trivial⁻` and `trivial⁺`, follow from it.
