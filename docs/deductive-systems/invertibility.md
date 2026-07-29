# Invertibility of the framing

Each side has a tier, and each tier is a contractible fiber of that
side's action map. Each delivers a center, and neither says anything
about the framing.

## The target

The target is the second projection:

```agda
is-invertible⁻ = ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
is-invertible⁺ = ∀ x → is-contr (fiber (act-π   {x} {x}) snd)
```

A side's center is therefore the uniquely determined edge whose
action on that family is the identity. Read through the argument,
the negative center is a right inverse of `twist⁻`. The positive
center is a left inverse of `twist⁺`. No twist appears in the demand
itself. Readback then places each center on a twist, which the last
section states.

## The cells

Beside each tier sits that side's cell: one twist read through the
other, so a pending read meets a pending write:

```agda
cell⁻ x γ = act-π   (twist⁻ (γ .fst)) (x , γ .snd)
cell⁺ x t = coact-π (twist⁺ (t .fst)) (x , t .snd)
```

A cell carries one edge and one twist of each sign, the cancellation
performed and never named as an edge of its own. It exists only as
the operation of performing it.

## The twists are the cells' centers

VERIFIED (`Bb.WeakDeductiveSystem.Gist.FramedCut`, at an arbitrary framing over an
arbitrary type, no h-level hypothesis):

- `twist⁺-centre`, `twist⁻-centre`: each twist is the center of the
  *other* hand's cell fiber.
- `twist⁺-unique`, `twist⁻-unique`: and the only edge that sits
  there.

No assumption places them. Membership of a cell fiber, read at the
axiom half of the argument, is the flank exchange. The argument half
is contractible, so it carries everywhere.

So there each twist is the uniquely determined inverse of the other.
A future is what a buffer fulfills, and each is the only thing that
fulfills the other.

## Propositional, and dual

VERIFIED (`Cat.Logic.Base`):

- `is-invertible⁻-is-prop`, `is-invertible⁺-is-prop`, and the
  bundling record `is-invertible` with `is-invertible-is-prop`.
- `op-invertible⁻`, `op-invertible⁺` are both `refl`: the opposite
  exchanges the argument halves and the twists, and the projection
  is the same demand read from either end, on the nose. So
  `op-invertible` transports one by swapping its two fields.

## What the tower consumes

Readback and each hand's own cut give the first two unit laws and
the two pairings, with no tier: `unitr⁺`, `unitl⁻`, `pair⁺` and
`pair⁻`. The rest is `tower.balanced`. It takes both tiers and
returns the two cancellations, the two absorptions, and the
remaining unit laws. So the tower does consume the tiers, and it
reads the centers they supply. See [towers.md](towers.md).

## Readback settles it

Whether a side's center *is* a twist was once a further equation,
the framing's own content. Readback decides it. VERIFIED
(`Cat.Logic.Base`, `tower.balanced`): `centre⁻-twist⁺` and
`centre⁺-twist⁻` derive each identification from the tiers alone. So
both cancellations are theorems, and the twists are mutually
inverse. The live carrier leaves nothing here to the framing.

The results below describe the readback-free stratum, which the
archive holds. They record what the tiers alone can do over a
carrier the live one has replaced.

The two sides are independent there. VERIFIED
(`Bb.OneTwist.Cancel`), over the one-twist carrier: a twisted
reflection on the Klein four-group has one cancellation and refutes
the other. Neither side's identification buys the other.

Over the path groupoid the sides meet in one equation. VERIFIED
(`Bb.WeakDeductiveSystem.Gist.FramedCut`): `cancels` gives both
`trivial⁻` and `trivial⁺`. The tier's center is a unit for its
hand's composition at every framing (`neutral⁻-unitr`,
`neutral⁺-unitl`). It coincides with the twist exactly when the
equation holds (`twist-is-neutral⁻`, `twist-is-neutral⁺`).

Off the path-object regime the same split is arithmetic. VERIFIED
(`Bb.WeakDeductiveSystem.Gist.FramedGroup`), in an abelian group
framed by an arbitrary pair. Each tier's center is the inverse of
that side's own twist: `ι t⁻` for the negative side, `ι t⁺` for the
positive. Then `absorber⁻-is-twist⁺` carries the first back to `t⁺`,
exactly under the cancellation.
