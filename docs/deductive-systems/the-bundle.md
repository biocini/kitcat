# The bundle

A deductive system is a virtual graph satisfying the three tiers.

```agda
record is-deductive-system : Type (o ⊔ h) where
  field
    composable : is-composable
    unital     : is-unital
    stable     : is-stable unital

  open is-composable composable public
  open is-unital     unital     public
  open stability     unital stable public
```

The bundle is iterated rather than a product because stability's
flanks are stated at the units the unit tier projects — an honest
type-former dependence. Opening the record exposes all three tiers'
contents, so a consumer opens one thing and has the compositions, the
units, the readback family and every derived identification.

## It is a proposition

```agda
is-deductive-system-is-prop : is-prop is-deductive-system
```

VERIFIED in `Test.SpikeDeductiveSystem`, field by field: the first
two components by the tiers' own propositionality, the third as an
`is-prop→PathP` over the path the unit component supplies. That last
step is the only place the dependency shows up in a proof.

So being a deductive system is a **property of a virtual graph**, not
structure on one. Two witnesses are equal; a map of virtual graphs
has nothing extra to preserve; and the moduli question for the theory
is a question about virtual graphs alone.

## What a system provides

```
    from is-composable      _⨾⁻_, _⨾⁺_          the two compositions
                            reflect-⨾⁻/⁺        their head rewritings

    from is-unital          unit⁻, unit⁺        the two units
                            unit⁻/⁺-absorb      their absorptions
                            unit⁻/⁺-unique-σ    uniqueness, with witness

    from is-stable          unit                the readback family
                            unit⁻/⁺-is-idn      idn is the unit, both hands
                            units-agree         the hands' units coincide
                            idn-absorb⁻/⁺       idn absorbs, both hands
                            flanks-agree        the one cross-hand fact
```

Everything in the left column is a projection. Nothing on the list is
a field with laws attached, which is what makes the tiers
propositional in the first place.

## Reading the tiers as reflexive-graph structure

`Cat.Graph.Refl` gives each tier a name of its own. With a bundle in
hand the slice and coslice are displayed reflexive graphs over the
underlying graph — the flank absorptions are exactly their displayed
reflexivity — and the composability fields are their fibration
conditions, handed over unchanged:

```agda
coslice-is-fibration _ _ _ p u = contr⁻ u p     -- rx.is-cov-fibration
slice-is-fibration   _ _ _ p w = contr⁺ p w     -- rx.is-ctrv-fibration
push-is-comp _ _ _ _ _ = refl                   -- cov.push  ≡ _⨾⁻_
pull-is-comp _ _ _ _ _ = refl                   -- ctrv.pull ≡ _⨾⁺_
```

VERIFIED in `Test.SpikeDeductiveSystem` (appendix). The unit fiber is
the shape `cov-lens-structure-is-prop` collapses to in
`Cat/Graph/Refl/Lens.lagda.md:111`, one level down; uniqueness by
contraction is `rx.univalence.to-id`'s move; the naturality argument
of [stability.md](stability.md) is the elementary form of what
straightening runs on in `Cat.Graph.Refl.Fibration`; and the exchange
of hands is `rx.op` with the total opposite on the displays.

One asymmetry is worth keeping in view. Wherever that suite
hypothesises `rx.is-univalent G` it is asking every fan to be a
proposition — that every coterm type is one. A deductive system does
not satisfy this, so the *uniqueness* theorems of `Lens` do not
transfer even though its vocabulary and its duality machinery do.
Univalence of the base is the path-object regime, and the theory here
is deliberately wider.

## Outside the theory

**Mediation.** Nothing identifies `_⨾⁻_` with `_⨾⁺_`. An
identification of the two composite judgments is an interchange, and
a virtual graph may admit none, one or many. A deductive system with
one point of that space is a category; the space itself is where
braiding and chirality live.

**Polarity.** The two-handed picture with no interchange is the
polarised one: in a non-associative category the maps for which
length-three paths associate are the *thunkable* ones, dually the
*linear* ones, and an object is positive or negative according to
which of these all its maps are (Mangel, Melliès and
Munch-Maccagnoni, `resources/mangel-classical-notions`,
`article.tex:1084,1694`; SOURCE-CHECKED). That a deductive system's
two hands are the two native compositions of a duploid is
CONJECTURED — nothing here has been checked against those
definitions, and the shapes differ in at least one respect worth
recording: a duploid's two disciplines are one composition read at
the two polarities of the middle object, where a deductive system's
are two operations projected from two fibers.

**Provenance.** The spike modules `Test.SpikeDeductiveSystem`,
`Test.SpikeUnitCanonical`, `Test.SpikeRxDict` and
`Test.SpikePerHandUnit` carry the machine-checked development these
documents present, and remain in the tree for that purpose.
