# Invertibility of the framing

Each side has a tier, and each tier is a contractible fiber of that
side's action map. Each delivers a centre, and neither says anything
about the framing.

## The target

The target is the second projection:

```agda
is-invertible⁻ = ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
is-invertible⁺ = ∀ x → is-contr (fiber (act-π   {x} {x}) snd)
```

A side's centre is therefore the uniquely determined edge whose action
on that family is the identity — equivalently, the inverse cancelling
the twist that action holds. No twist appears in the demand, so the
tiers constrain the framing not at all.

## The cells

Beside each tier sits that side's cell — one twist read through the
other, so a pending read meets a pending write:

```agda
cell⁻ x γ = act-π   (twist⁻ (γ .fst)) (x , γ .snd)
cell⁺ x t = coact-π (twist⁺ (t .fst)) (x , t .snd)
```

A cell carries one edge and one twist of each sign, the cancellation
performed and never named as an edge of its own — it exists only as the
operation of performing it.

## The twists are the cells' centres

VERIFIED (`Test.SpikeFramedCut`, at an arbitrary framing over an
arbitrary type, no h-level hypothesis):

- `twist⁺-centre`, `twist⁻-centre` — each twist is the centre of the
  *other* hand's cell fiber.
- `twist⁺-unique`, `twist⁻-unique` — and the only edge that sits there.

Nothing is assumed to place them. Membership of a cell fiber, read at
the axiom half of the argument, is the flank exchange; the argument half
is contractible, so it carries everywhere.

So there each twist is the uniquely determined inverse of the other. A
future is what a buffer fulfils, and each is the only thing that fulfils
the other.

## Propositional, and dual

VERIFIED (`Cat.Logic.Base`):

- `is-invertible⁻-is-prop`, `is-invertible⁺-is-prop`, and the bundling record
  `is-invertible` with `is-invertible-is-prop`.
- `op-invertible⁻`, `op-invertible⁺` are both `refl`: the opposite
  exchanges the argument halves and the twists, and the projection is
  the same demand read from either end — on the nose. So
  `op-invertible` transports one by swapping its two fields.

## The tower does not consume it

`tower`'s unit laws — `unitr⁺`, `unitl⁻`, `pair⁺`, `pair⁻` — come from
the `unital` module, whose hypotheses are the two pins and the two
cancellations. No derivation in `Cat.Logic.Base` reads the centre a tier
supplies; there the tier is carried by the package and crossed by
`op-invertible`. A unit law drawn from a tier directly is `neutral⁻-unitr`
and `neutral⁺-unitl`, VERIFIED (`Test.SpikeFramedCut`).

## What is left to the framing

Whether a side's centre *is* a twist is one further equation — that the
cancellation is the identity — and it is the framing's own content, not
a consequence of the tiers. VERIFIED (`Test.SpikeFramedCut`): `cancels`
gives both `trivial⁻` and `trivial⁺`; the tier's centre is a unit for
its hand's composition at every framing (`neutral⁻-unitr`,
`neutral⁺-unitl`), coinciding with the twist exactly when the equation
holds (`twist-is-neutral⁻`, `twist-is-neutral⁺`).

Off the path-object regime the same split is arithmetic. VERIFIED
(`Test.FramedGroup`): in an abelian group framed by an arbitrary pair,
each tier's centre is the inverse of the twist its action map holds —
`ι t⁻` for `coact-π`, `ι t⁺` for `act-π` — and `absorber⁻-is-twist⁺`
carries the first back to `t⁺` exactly under the cancellation.

A framed system therefore has a unit that need not be a twist. What the
cells pin is the framing; the unit is a fiber of the same map over the
projection.
