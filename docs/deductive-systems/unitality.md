# Unitality

Each hand has a tier, and each tier is a contractible fiber of that
hand's action map. What the two tiers pin is the framing.

## The target

The target is not the second projection. It is the argument half's own
edge with **one cancellation performed**:

```agda
cell⁻ x γ = act-π   (twist⁻ (γ .fst)) (x , γ .snd)
cell⁺ x t = coact-π (twist⁺ (t .fst)) (x , t .snd)

is-unital⁻ = ∀ x → is-contr (fiber (coact-π {x} {x}) (cell⁻ x))
is-unital⁺ = ∀ x → is-contr (fiber (act-π   {x} {x}) (cell⁺ x))
```

Each `cell` reads a hand's own twist through the *other* hand, so a
pending read meets a pending write. It carries one edge and one twist of
each sign: winding-neutral, and the cancellation is never named as an
edge of its own — it exists only as the operation of performing it.

The second projection carries no twist at all. A unit sitting over it
would be a bare twist for which a winding costs nothing, and a bare twist
is a loop: composing with it must cost, and only the opposite twist can
take that cost back.

## The twists are the centres

VERIFIED (`Test.SpikeFramedCut`, at an arbitrary framing over an
arbitrary type, no h-level hypothesis):

- `twist⁺-centre`, `twist⁻-centre` — each twist is the centre of the
  *other* hand's fiber.
- `twist⁺-unique`, `twist⁻-unique` — and the only edge that sits there.

Nothing is assumed to place them. Each tier's condition, read at the
axiom half of its argument, is the flank exchange; the argument half is
contractible, so it carries everywhere.

So the two tiers make each twist the uniquely determined inverse of the
other. A future is what a buffer fulfils, and each is the only thing that
fulfils the other.

## Propositional, and dual

VERIFIED (`Cat.Logic.Base`):

- `is-unital⁻-is-prop`, `is-unital⁺-is-prop`, and the bundling record
  `is-unital` with `is-unital-is-prop`.
- `op-unital⁻`, `op-unital⁺` are both `refl`: the opposite exchanges the
  hands and the twists, hence the targets, hence the tiers — on the nose.
  So `op-unital` transports a unitality by swapping its two fields.

## What is left to the framing

Whether either twist is a *unit* for its hand's composition is one
further equation — that the cancellation is the identity — and it is the
framing's own content, not a consequence of the tiers. VERIFIED
(`Test.SpikeFramedCut`): `cancels` gives both `trivial⁻` and `trivial⁺`;
and a unit exists at every framing regardless (`neutral⁻-unitr`,
`neutral⁺-unitl`), coinciding with the twist exactly when the equation
holds (`twist-is-neutral⁻`, `twist-is-neutral⁺`).

A framed system therefore has a unit that is not a twist. What the tiers
pin is the framing; the unit is a separate fiber of the same map.
