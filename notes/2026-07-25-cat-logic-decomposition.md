# `Cat.Logic` — the module decomposition

> **Superseded.** This describes the formulation in which a virtual
> graph carries a single chosen edge `idn`, the tiers are stated over
> the second projection, and stability is a contractible fiber over a
> flank coherence carrying a `readback` family. The formulation of
> record is the framed one: a virtual graph carries `twist⁺` and
> `twist⁻` instead of `idn`, the unit tiers sit over one cancellation,
> stability is uniqueness of representation, and composability is bare
> existence indexed by it. `Cat.Logic.Type` and `Cat.Logic.Base` carry
> that formulation, and `docs/deductive-systems/` documents it.
>
> What survives here is the cut itself — layering by which axioms are
> consumed, and the account of what changes when a spike is promoted.
> The layer contents, the placement questions, and the ledger list
> below all name the earlier vocabulary.

The cut is by **which axioms are consumed**, not by subject matter.
Each layer below is closed under "everything statable with the axioms
available at that point", which is what makes the boundaries stable
under later additions.

| | layer | consumes | status |
| --- | --- | --- | --- |
| 1 | `Cat.Logic.Type` — the record and the sequent vocabulary | nothing | landed |
| 2 | the axiom-free layer | nothing | split, see below |
| 3 | the tiers and their propositionality | 2 | `Cat.Logic.Base` |
| 4 | derived theory over the bundle | 3 | in `Cat.Logic.Base` |
| 5 | the displays and lenses | 3, 4 | `Test/` |
| 6 | the displaced theory — `virtual-graphᴰ` | 1 | `Test/` |

## Layer 2 is two modules, not one

The axiom-free material splits on whether it mentions `Cat.Graph.Refl`:

- **Sequent-only.** `opⱽ`, `act`/`coact`/`act-π`/`coact-π`,
  `inj⁻`/`inj⁺`, `composite⁻`/`composite⁺`, `readback`. Every one is
  definable on a bare virtual graph and every claim about them is
  `refl`. These sit at the head of `Cat.Logic.Base`, above the tiers
  that consume them.
- **The reflexive-graph seam.** `graph`, the fan/cofan dictionary,
  `judgment±`/`hom±`, `two-sided`, `bipush`. This is where the
  `Cat.Graph.Refl` import belongs and where it should be confined.

Confining the import is the reason for the split. Layers 3 and 4 have
no business knowing about reflexive graphs, and the seam has no
business knowing about the tiers until layer 5 needs both.

## What is not yet placed

Layers 5 and 6 are still in `Test/`, and layer 5 has a dependency
knot: `Test.SpikeJudgmentLens` and `Test.SpikeTwoSided` build on
`Test.SpikeDeductiveSystem`'s copy of the tiers rather than on
`Cat.Logic.Base`'s, because the displays they need live in that
spike's appendix. The two copies are the same text; they will not
converge until the seam module exists and the appendix moves into it.
Nothing downstream should be built on the spike in the meantime.

## Promotion changes the shape of a definition

A spike may hypothesise its inputs as module parameters, state a
question in prose and answer it, and keep a route that leads nowhere
as evidence. A library module does none of those.

| spike form | promoted form |
| --- | --- |
| `SpikeRxDict.hand⁻` takes `contr⁻` as a parameter | open the tier record, project |
| `SpikeUnitCanonical.canonical` takes `(U⁻ U⁺ rb)` | derived theory over the bundle |
| `SpikeJudgmentLens.from-readback` takes `(U , rb)` | takes the bundle |
| `SpikeDeductiveSystem.appendix` takes `D` | already right |

Two things never promote, because their value is negative and a
library module has nowhere to put it:

- `half-adjoint-forces-truncation` — why the stability tier is wrapped
  in `is-contr` rather than stated as a pair.
- `from-readback` — that the lens unitors consume `is-unital` plus a
  bare readback family and never reach `absorb-coh`.

The `refl`-dictionaries are a third case. The definitions they certify
move; the certificates themselves are regression witnesses and belong
under the gate-exempt namespace, where a later edit that breaks a
definitional equality is caught rather than silently absorbed.

## What promotion drags with it

- `docs/gloss.md` has no entry for any of this. Ledger material: each
  tier's propositionality and the bundle's, the canonicity of `idn`,
  the two univalence certificates, `interchange→mediation`.
- `docs/roadmap.md` has no project for the framework, so the work
  currently has no gate.
- `docs/deductive-systems/` citations follow each piece as it lands.
- `Test.SpikePerHandUnit` is cited by the documents and is untracked.
