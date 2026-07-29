# The elementary theory of deductive systems

A *virtual graph* is a graph with three additions. The first is a
two-sided representable embedding of its edges into judgments. The
second is a **framing**: two families of endo-edges, one at each half
of an argument. The third is **readback**, which says that reifying
an edge at its own axiom returns that edge. A *deductive system* is a
virtual graph whose framing behaves: each twist with a uniquely
determined one-sided inverse, and both cuts representable
contractibly. Representation is then unique where it occurs, as a
theorem rather than a demand.

The framing and the readback are the structure. Everything asked of
them is property, and the package is a proposition.

These documents lay out the theory as it stands. Claims marked
VERIFIED name the module that checks them, in the discipline of
`docs/provenance.md`. The carrier is `Cat.Logic.Type`. The axioms,
the package and the towers are `Cat.Logic.Base`. The reflexive-graph
seam is `Cat.Logic.Graph`, and the displays over it
`Cat.Logic.Display`.

## The documents

| | |
| --- | --- |
| [virtual-graphs.md](virtual-graphs.md) | Terms, coterms, arguments, judgments, `reflect`, representability, the opposite |
| [framing.md](framing.md) | The two twists, futures and buffers and the crossing that fixes them, the axiom and evaluation, winding and what it forbids |
| [graphs.md](graphs.md) | The framing as two reflexive graphs, the fan dictionary, the opposite, the two-sided base |
| [actions.md](actions.md) | `act` and `coact` as displayed graphs on the term and coterm families, and the two cuts |
| [displays.md](displays.md) | Each family as a lens over the graph of the twist it does not hold, each cut as a fibration, interchange as a cospan |
| [stability.md](stability.md) | Representation unique where it occurs, cancellation, and why it is a theorem |
| [invertibility.md](invertibility.md) | The two tiers over the projection, the cells, and how readback places each centre |
| [composability.md](composability.md) | The two cuts' representability, existence against the contractible form |
| [the-package.md](the-package.md) | `is-deductive-system`, its propositionality, `deductive-system`, and the strict involution |
| [towers.md](towers.md) | The two compositions, distributivity, associativity and the valid mixed word, the four unit laws, the pentagon |
| [mediation.md](mediation.md) | Interchange: what identifying the two cuts adds, and what it collapses |

## The shape of the theory

Two principles run through it.

**The theory declares nothing it computes with.** Each composition
and each unit is the projection of a fiber, never a field with laws
attached. The framing is the only carried datum. Everything else is
a property of it.

**Everything comes in two hands.** An argument has a term half and a
coterm half. Each tier is one statement read at one half and at the
other. The opposite exchanges them, so one text serves both hands:
each construction appears once and instantiates twice.

The two twists are two reflexive graphs. A twist is a reflexivity
datum, so the framing is a pair of reflexive-graph structures on one
underlying graph. Each argument half is the center of its own graph,
and every tier that pairs them reads one against the other:
[graphs.md](graphs.md).

```
  virtual-graph      ob, hom, reflect, twist⁺, twist⁻, readback
    │
    ├── is-composable  both cuts representable, contractibly
    │                    ⇝ the two compositions, and stability
    │
    └── is-invertible  two contractible fibers of the action maps
                         ⇝ each side's centre, which is the other twist
```

The theory never identifies the two hands' compositions. That
identification is what a mediation buys, and it lies outside this
theory: adding it collapses the two twists into one edge (the twist
its own inverse), which then becomes a two-sided unit for a single
composition. [mediation.md](mediation.md) states exactly what a
mediation gains and what it spends.
