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

Read asynchronously, a term is a **future** and a coterm a
**buffer**. The negative twist is the pending read, the positive the
pending write, and where they meet they cancel: a ready value
fulfilling an expected delivery. A variable is a future you force. A
covariable is a mailbox you enqueue into.

This fixes the polarity everywhere: `var` carries `twist⁻`, `covar`
carries `twist⁺`, and evaluation at the axiom surrounds an edge with
one of each. `eval (reflect f)` is `f` transmitted: winding-neutral,
and formable, because its payload is three edges and its twists are
one of each sign.

## Winding

Give `twist⁺` the winding `+1`, `twist⁻` the winding `−1`, and an
ordinary edge `0`. By the arity count of
[virtual-graphs.md](virtual-graphs.md), an expression with `k`
payload edges carries `2n + 1 − k` twists, so its twist count has
the parity of `k + 1`.

Three consequences, and they shape the whole theory.

- A statement about a **single** edge (payload one) can be
  winding-neutral: two twists, one of each sign. This is where the
  invertibility tiers live. See [invertibility.md](invertibility.md).
- A statement about **two** edges (a unit law written as "composing
  with this edge changes nothing") carries an odd number of twists
  and can never be neutral.
- A **cut** of two edges (payload four) likewise carries an odd
  number. Each cut therefore carries one twist at its junction, and
  the two cuts carry opposite ones. See [actions.md](actions.md).

So the framing is not decoration on a graph that already had units.
It is what makes the two halves sayable at all, and every composite
the theory forms carries its winding.

## What the framing is not asked to be

Nothing in the axioms constrains the twists, and this holds on both
sides of the path-object boundary.

VERIFIED (`Test.SpikeFramedCut`): the path groupoid on an arbitrary
type, framed by two arbitrary families of loops, satisfies every
tier: `PG-deductive` holds with no condition on the framing and no
h-level hypothesis on the carrier. Its fans are singletons, so the
underlying graph is a path object whatever the framing does. Over
such a graph an edge is an identification and a framing is a family
of loops, its winding measured in the loop space of the vertices.

VERIFIED (`Test.FramedGroup`): an abelian group read as a one-object
virtual graph, framed by an arbitrary *pair* of its elements,
likewise satisfies every tier: `system : deductive-system`. Here a
fan is the whole group, so `univalent→prop` shows the graph is a
path object only when the group is a proposition. Off the boundary
the framing is free as well, and two of the theory's conditions
become arithmetic in that model:

```agda
→cancels    / cancels→    : the cancellation  ⟺  t⁻ · t⁺ ≡ e
→cuts-agree / cuts-agree→ : the cuts agree    ⟺  t⁻ ≡ t⁺
```

So the two cuts differ there by exactly the framing's own
discrepancy, and `both→` says holding both forces each element to be
its own inverse.

What the theory *does* is give each twist a uniquely determined
one-sided inverse: the center of that side's tier. Nothing above
decides whether that center *is* the other twist. That is one
equation per side, the framing's own content, and the theory holds
either way.

The two sides are moreover independent. VERIFIED
(`Test.ExtractedTwistCancel`), over the one-twist carrier of
`Test.ExtractedTwist`. The model is the Klein four-group, with the
reflection twisted by a three-cycle of its non-unit elements. Every
tier holds, one side's cancellation holds by construction, and the
other side's is refutable. In the two models above, `reflect` is a
plain composite and the two sides collapse into one equation. The
independence is invisible there.

VERIFIED (`Test.SpikeFramedCut`): over the path groupoid, `cancels`
is a single equation (the composite of the two twists at an object
is trivial), and both hands' cancellation conditions, `trivial⁻`
and `trivial⁺`, follow from it.
