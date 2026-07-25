# The elementary theory of deductive systems

A *deductive system* is a reflexive graph whose edges act on the
arrows around them, coherently enough that composition, units and
normalisation all exist and are unique — and no more than that. It
carries no interchange law, no mediation between its two
compositions, and no truncation anywhere.

These documents lay out the theory as it stands. The mathematics is
machine-checked; every claim labelled VERIFIED names the module that
checks it, in the discipline of `docs/provenance.md`. The witnesses
are the spike modules `Test.SpikeDeductiveSystem`,
`Test.SpikeUnitCanonical`, `Test.SpikeRxDict` and
`Test.SpikePerHandUnit`, which stay in the tree as provenance for
this presentation; the foundation they build on is `Cat.Logic.Type`.

## The documents

| | |
| --- | --- |
| [virtual-graphs.md](virtual-graphs.md) | Terms, coterms, arguments, judgments; the embedding `reflect`; evaluation and representability; the involution |
| [actions.md](actions.md) | `act` and `coact` as displayed reflexive graphs on the term and coterm families; why the variance is mixed; the two composite judgments |
| [composability.md](composability.md) | The first tier: composition as a fiber center, and the slice and coslice as fibrations |
| [unitality.md](unitality.md) | The second tier: the unit as a fiber center, its uniqueness, and the canonicity of the chosen edge |
| [stability.md](stability.md) | The third tier: readback, the flank coherence, and why the coherence must be taken inside a fiber |
| [the-bundle.md](the-bundle.md) | The three tiers as one propositional predicate, and what the theory looks like from outside |

## The shape of the theory

One principle runs through all three tiers: **nothing the theory
computes with is declared.** Composition, the units and the readback
family are each the projected center of a contractible space, never a
field with laws attached. That is what keeps every tier a
proposition, so that being a deductive system is a *property* of a
virtual graph rather than structure on one.

```
  virtual-graph        ob, hom, idn, reflect
    │
    ├── is-composable  two contractible fibers of reflect
    │                    ⇝ the two compositions
    │
    ├── is-unital      two contractible fibers of the action maps
    │                    ⇝ the two units, and their absorptions
    │
    └── is-stable      one contractible fiber over the flank coherence
                         ⇝ readback, and the canonicity of idn
```

The other structural fact is that everything comes in **two hands**.
An argument has two slots, a term slot and a coterm slot; each tier's
two fields are the same statement read at one slot and at the other.
The two are exchanged by the involution on virtual graphs, so the
theory is written once and instantiated twice. Nothing identifies the
two hands' compositions with each other — that identification is what
a mediation would buy, and it is outside this theory.

Everything a virtual graph carries is displayed reflexive graph
structure over its own underlying graph. The two actions are the
transports of the term and coterm displays, whose displayed
reflexivity is the unit tier; the two compositions are the transports
of the slice and coslice displays, whose fibration conditions are the
composability tier. The two families have *opposite* variance —
covariant on terms, contravariant on coterms — which is forced by
which endpoint each is indexed at, and is what gives `judgment` the
variance profile of `hom`.

## Names

`act` and `coact` name the two actions, by the slot of an argument
each consumes, with `act-π`/`coact-π` the forms whose anonymous
endpoint is a parameter. `push` and `pull` keep their reflexive-graph
meaning throughout — the transports of a displayed family — which in
this theory are the two compositions. The spike modules use the same
names as these documents.

## Where the vocabulary comes from

The reflexive-graph layer — fans, cofans, displayed graphs,
fibrations, lenses and the total opposite — follows Sterling's
*Reflexive Graph Lenses* (`resources/sterling-reflexive-graph-lenses`)
and is formalised in `Cat.Graph.Refl`. Terms and coterms are that
suite's cofans and fans, and the tiers are its fibration conditions;
[composability.md](composability.md) and [the-bundle.md](the-bundle.md)
make the dictionary precise.

The reason a unit tier can be propositional at all without truncating
homs is the subject of Capriotti and Kraus,
*Univalent Higher Categories via Complete Semi-Segal Types*
(`resources/capriotti-kraus-semi-segal`), whose Theorem on the
uniqueness of identity structure shows the naive form is *not*
propositional; [unitality.md](unitality.md) explains what shape
escapes that.

The two-handed structure is the polarised one studied by Mangel,
Melliès and Munch-Maccagnoni, *Classical notions of computation and
the Hasegawa-Thielecke theorem* (`resources/mangel-classical-notions`),
where a non-associative category's thunkable and linear maps organise
exactly the phenomena a mediation-free composition exhibits. The
correspondence is CONJECTURED — nothing here is checked against that
paper's definitions.
