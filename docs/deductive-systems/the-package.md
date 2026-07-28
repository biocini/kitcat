# The package

```agda
record is-deductive-system (G : virtual-graph o h) where
  field stable     : is-stable G
        composable : is-composable G stable
        invertible : is-invertible G
```

Stability comes first because it indexes the composability field.
Neither cut's existence is a proposition on its own. The stability
the record carries is what makes it one.

VERIFIED (`Cat.Logic.Base`): `is-deductive-system-is-prop`. Being a
deductive system is a **property** of a virtual graph. The stability
field moves under the proof, so a path over the moving stability
fills the composability field, rather than a path in a constant
type. That is the content of indexing the record rather than listing
four flat fields.

## Structure and property

```agda
record deductive-system o h where
  field graph  : virtual-graph o h            -- structure
        axioms : is-deductive-system graph    -- property
```

One field each. The framing inside `graph` is the only structure the
theory carries. Everything in `axioms` is a proposition.

## The involution

```agda
opᴰ D .graph  = opⱽ (graph D)
opᴰ D .axioms = op-axioms _ (axioms D)
```

`op-axioms` assembles `op-stable`, `op-composable` and
`op-invertible`. The first two reindex along the exchange of
argument halves. The last swaps its two fields, since the two
invertibility tiers exchange definitionally.

VERIFIED (`Cat.Logic.Base`): `opᴰ-invol : opᴰ (opᴰ D) ≡ D`. The
carrier component is `refl`, because the opposite of a virtual graph
is a swap of two fields and `opⱽ-invol` is `refl`. The axioms
component is `is-deductive-system-is-prop`.

So the involution is as strict as it can be: on the nose where there
is structure, and by propositionality where there is property. That
is what the split is for.

## Inhabited

VERIFIED (`Test.SpikeFramedCut`): the path groupoid on an arbitrary
type, framed by two arbitrary families of loops, gives
`PG-deductive` and hence `PG-system : deductive-system u u`.
Representability there is total (`reflect` is an equivalence).
Stability, both cuts and both unit tiers therefore hold, with no
assumption on the framing and none on the carrier's h-level.
