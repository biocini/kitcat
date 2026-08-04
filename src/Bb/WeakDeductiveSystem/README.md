# Bb.WeakDeductiveSystem

## The construction

A virtual graph is a graph, a framing, and one axiom. The framing
is two families of endo-edges, `twist⁺` and `twist⁻`, one of each
at every object. They close the two ends of an argument. The axiom
is `reflect`: every edge names a judgment over its own endpoints.
A judgment takes a term and a coterm, and returns an edge between
their far ends. The carrier declares neither composition. Both are
projections of fibers of `reflect`, one per argument slot.

A deductive system is a property of that carrier, in three tiers.
`is-stable` says representation is unique where it occurs, which
makes `reflect` an embedding. `is-composable±` says each cut has a
representative, as bare existence indexed by stability.
`is-invertible±` says each twist has a uniquely determined
one-sided inverse. Every tier is propositional, and the framing is
the only structure. The tree does not claim that the two inverses
are the twists themselves. That claim is the balanced layer's, one
level up.

Sixteen modules. `Type` holds the record. `Base` holds the derived
theory: the two towers and the valid mixed word `mixed-assoc`. It
also holds the withheld word `associates`, with the closures
`thunkable` and `linear` over it. `Graph` reads the framing as two
reflexive-graph structures on one graph. `Display` reads each
argument family as a lens and each cut as a fibration.

The twelve `Gist` modules certify those definitions. Three of them
settle a question by countermodel.

- `AssociatesCountermodel`: the associativity profile is exactly
  pre-duploid.
- `ThunkableSquare`: thunkability is data, and the length-4 square
  does not truncate it.
- `ReadbackTorsor`: the propositional form of balance is
  refutable.

## Provenance

Frozen 2026-07-28 at commit `1db09db`, from `Cat.Logic` as it
stood before the (D′) record cut of the same day. The session log
is `notes/2026-07-28-balanced-record-cut.md`.

The cut is what the archive marks. At (D′) the live
`virtual-graph` gained a `readback` field, the unit-free
correctness equation for normalization by evaluation.
`is-deductive-system` became contractible cuts plus invertibility,
and `stable` fell from a tier to a theorem. This tree is the
stratum below that: no readback, stability a tier, composability
existence-only and indexed by it. Lane ruled the same day that the
live tree carries no red modules. Five free-framing `Gist` spikes
moved here rather than break: `AssociatesCountermodel`,
`FramedCut`, `FramedGroup`, `NeutralUnit`, and `TwistFidelity`.
They state facts about the free framing, which the cut removes.
The `docs/` files that cite them point here.

The tree arrived with a `TODO.md`, converted into this README on
2026-07-28. The successor's open items were never this tree's, and
they live at `src/Cat/Logic/TODO.md`.

## Relationships

`Cat.Logic` is the successor, at (D′). Read the two side by side
to see what readback buys. Here the four unit laws and both
cancellations need the balanced layer. There each tier centre
reads back as the other twist, so both are theorems.

`Bb.NaiveVirtualGraph` is the ancestor. It carries one chosen edge
in place of the framing. Its `Gist` modules record why no
predicate pins that edge.

`Bb.OneTwist` is the rejected rival, which drops `twist⁺` and
takes the `⁺` tier centre in its place. Its two spikes run against
this tree: `Bb.OneTwist.Cancel` against `Gist.FramedInterchange`,
and `Bb.OneTwist.Models` against `Gist.FramedCut` and
`Gist.FramedGroup`.

`Bb.VgCategoryShape` is the one-twist collapse of the same
material, where the double twist is the identity.

Four modules here import the live `Core.Rx`: `Graph`,
`Display`, `Gist.FramedGroup`, and `Gist.RxDict`. A change there
can break this tree. The session log records that risk, accepted.
