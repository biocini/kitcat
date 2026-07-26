# The elementary theory of deductive systems

A *virtual graph* is a graph together with a two-sided representable
embedding of its edges into judgments, and a **framing**: two families
of endo-edges, one at each half of an argument. A *deductive system* is
a virtual graph whose framing behaves — each twist the uniquely
determined inverse of the other, representation unique where it occurs,
both cuts representable.

The framing is the only structure. Everything asked of it is property,
and the package is a proposition.

These documents lay out the theory as it stands. Claims marked VERIFIED
name the module that checks them, in the discipline of
`docs/provenance.md`. The carrier is `Cat.Logic.Type`; the axioms, the
package and the towers are `Cat.Logic.Base`; the model and the boundary
are `Test.SpikeFramedCut` and `Test.SpikeNeutralUnit`.

## The documents

| | |
| --- | --- |
| [virtual-graphs.md](virtual-graphs.md) | Terms, coterms, arguments, judgments; `reflect`; representability; the opposite |
| [framing.md](framing.md) | The two twists; futures and buffers; the axiom and evaluation; winding, and what it forbids |
| [actions.md](actions.md) | `act` and `coact` as displayed graphs on the term and coterm families; the two cuts |
| [stability.md](stability.md) | Representation is unique where it occurs; cancellation; where the propositional weight sits |
| [unitality.md](unitality.md) | The two tiers, over one cancellation rather than over the projection; the twists as the centres |
| [composability.md](composability.md) | The two cuts' representability, existence only, indexed by a stability |
| [the-package.md](the-package.md) | `is-deductive-system`, its propositionality, `deductive-system`, and the strict involution |
| [towers.md](towers.md) | The two compositions, distributivity, associativity, the unit law each hand gets, the pentagon |
| [mediation.md](mediation.md) | Interchange: what identifying the two cuts adds, and what it collapses |

## The shape of the theory

Two principles run through it.

**Nothing the theory computes with is declared.** Each composition and
each unit is the projection of a fiber, never a field with laws attached.
The framing is carried; everything else is a property of it.

**Everything comes in two hands.** An argument has a term half and a
coterm half; each tier is one statement read at one half and at the
other. The opposite exchanges them, and every construction is written
once and instantiated twice.

```
  virtual-graph      ob, hom, reflect, twist⁺, twist⁻
    │
    ├── is-stable      representation unique where it occurs
    │
    ├── is-composable  both cuts representable         (over a stability)
    │                    ⇝ the two compositions
    │
    └── is-unital      two contractible fibers of the action maps
                         ⇝ the twists, as the unique centres
```

The two hands' compositions are never identified. That identification is
what a mediation buys, and it lies outside this theory: adding it
collapses the two twists into one edge, which then becomes a two-sided
unit for a single composition. [mediation.md](mediation.md) states
exactly what is gained and what is spent.
