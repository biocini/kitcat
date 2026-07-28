# Bb.NaiveVirtualGraph

## The construction

A virtual graph in the chosen-edge form: objects, edges, one
chosen edge `idn` at each object, and `reflect`. `reflect` is the
one axiom. It names, for every edge, a judgment over that edge's
own endpoints. The chosen edge fills both halves of an argument,
so `var a` is `(a , idn a)` and `covar y` is `(y , idn y)`. `Base`
holds that carrier and the vocabulary it supports before any
composability, unit, or stability hypothesis.

The twelve `Gist` modules are the spikes that measured the form.
`DeductiveSystem` packages the predicate over it, three tiers in
three records and one bundle. `PathGroupoid` inhabits the theory.
`StableFiber` states the stability tier as the design note
specifies it. `PerHandUnit` states the two compositions as what
the two displays push and pull.

`JudgmentLens` and `TwoSided` ask which lens carries `judgment`.
Mixed variance turns out to be a fact about the base. Over the
graph paired with its opposite the family has one variance.

The rest is a negative-result dossier, and it is why the form
lost. Nothing in `reflect` mentions the chosen edge, so the
carrier holds it freely. A predicate that makes the graph a
deductive system has to say the edge absorbs
(`AbsorbObstruction`). A unit datum is propositional only when it
is a fiber of the action map. Every such form projects its unit
from the fiber centre, never from the chosen edge
(`UnitCanonical`). Identifying the two is then a path in a hom
type (`StabilityShape`). No proposition over this carrier can
assert it.

Two spikes take the remaining routes. `ReflexiveVG` moves the unit
laws into the carrier as structure. `SelfUnit` asks whether the
unit needs a chosen edge at all. `CrossedUnit` then takes the two
axiom halves apart. The chosen family fills the term slot, and
the coterm hand's own fiber fills the other. Each tier then runs
over the crossed pairing. That is the framing, one move early.

## Provenance

Vendored 2026-07-28 from twelve `Test` spikes, with the `Spike`
prefix dropped. Each spike had carried its own copy of the data it
probed. A change to the live layer could then not retune it
silently. The copies agreed, and the vendoring extracted the
shared one into `Base`. Ten of the twelve read the carrier from
there. `PerHandUnit` and `SelfUnit` keep their own, which differ.

Three commits carry the spikes, on 2026-07-24 and 2026-07-25:
`48abd21`, `dd4461b`, and `165fbf8`. The framing landed in the
last of those, on 2026-07-25. A virtual graph gained `twist⁺` and
`twist⁻` and lost `idn`. The two unit tiers moved onto the crossed
pairing. That left these spikes stating facts about a carrier the
library no longer had. The review of the same day,
`notes/2026-07-25-cat-logic-decomposition.md`, records the
verdict: superseded rather than promotable.
`notes/2026-07-25-two-lineages.md` reads the framed carrier
against its two sources.

## Relationships

`Bb.WeakDeductiveSystem` is the successor stratum, and the
difference is one field. There a virtual graph carries two
families of endo-edges in place of the one chosen edge. The two
argument halves then take their fillers from two sources. The unit
tiers become the mutual comparison of two reflexive graphs on one
underlying graph. `CrossedUnit` here is the last spike before that
move, and it already carries the shape.

`Bb.VgCategoryShape` returns to a single chosen edge, and it is
not a return to this form. There the edge comes with readback,
which aligns the reflection with the edge. This carrier never had
it. Readback is what makes the unit laws and interchange theorems,
and its absence is what the dossier above measures.

Three modules here import the live `Cat.Graph.Refl`:
`Gist.DeductiveSystem`, `Gist.JudgmentLens`, and `Gist.TwoSided`.
A change there can break this tree.
