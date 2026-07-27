# The package

```agda
record is-deductive-system (G : virtual-graph o h) where
  field stable     : is-stable G
        composable : is-composable G stable
        unital     : is-invertible G
```

Stability comes first because the composability field is indexed by it:
neither cut's existence is a proposition on its own, and it is the
stability the record carries that makes it one.

VERIFIED (`Cat.Logic.Base`): `is-deductive-system-is-prop`. Being a
deductive system is a **property** of a virtual graph. The stability
field moves under the proof, so the composability field is filled by a
path over the moving stability rather than in a constant type — which is
the content of indexing the record rather than listing four flat fields.

## Structure and property

```agda
record deductive-system o h where
  field graph  : virtual-graph o h            -- structure
        axioms : is-deductive-system graph    -- property
```

One field each. The framing inside `graph` is the only structure the
theory carries; everything in `axioms` is a proposition.

## The involution

```agda
opᴰ D .graph  = opⱽ (graph D)
opᴰ D .axioms = op-axioms _ (axioms D)
```

where `op-axioms` assembles `op-stable`, `op-composable` and
`op-invertible` — the first two by reindexing along the exchange of argument
halves, the last by swapping its two fields, since the two unit tiers
exchange definitionally.

VERIFIED (`Cat.Logic.Base`): `opᴰ-invol : opᴰ (opᴰ D) ≡ D`. The carrier
component is `refl`, because the opposite of a virtual graph is a swap of
two fields and `opⱽ-invol` is `refl`; the axioms component is
`is-deductive-system-is-prop`.

So the involution is as strict as it can be: on the nose where there is
structure, and by propositionality where there is property. That is what
the split is for.

## Inhabited

VERIFIED (`Test.SpikeFramedCut`): the path groupoid on an arbitrary type,
framed by two arbitrary families of loops, gives `PG-deductive` and hence
`PG-system : deductive-system u u`. Representability there is total —
`reflect` is an equivalence — so stability, both cuts and both unit tiers
hold with nothing assumed about the framing and no h-level hypothesis on
the carrier.
