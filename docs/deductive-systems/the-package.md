# The package

```agda
record is-deductive-system (G : virtual-graph o h) where
  field composable : is-composable G
        invertible : is-invertible G
```

Two flat fields, both propositions outright. `is-composable` asks
each cut for a *contractible* representability fiber, which carries
the representative and its uniqueness in one datum, so the field
needs no stability index. Stability is then a theorem rather than a
tier. See [stability.md](stability.md).

VERIFIED (`Cat.Logic.Base`): `is-deductive-system-is-prop`. Being a
deductive system is a **property** of a virtual graph. Both fields
are propositions in a constant type, so the proof is fieldwise and
takes no path over a moving index.

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

`op-axioms` assembles `op-composable` and `op-invertible`. The first
reindexes along the exchange of argument halves. The second swaps
its two fields, since the two invertibility tiers exchange
definitionally. `op-stable` crosses stability the same way, and the
tower consumes it as a theorem.

VERIFIED (`Cat.Logic.Base`): `opᴰ-invol : opᴰ (opᴰ D) ≡ D`. The
carrier component is `refl`, because the opposite of a virtual graph
is a swap of two fields and `opⱽ-invol` is `refl`. The axioms
component is `is-deductive-system-is-prop`.

So the involution is as strict as it can be: on the nose where there
is structure, and by propositionality where there is property. That
is what the split is for.

## Inhabited

VERIFIED (`Cat.Logic.Gist.BalancedWord`): the free framed point, a
carrier of eventual-translation descriptors with decidable equality.
`BW : virtual-graph` carries readback, and `BW-deductive :
is-deductive-system BW` assembles `BW-composable` and
`BW-invertible`. Stability arrives through `stable-from-hom-sets`,
since the carrier is a set.

The path groupoid no longer serves. VERIFIED
(`Bb.WeakDeductiveSystem.Gist.FramedCut`): it is a full system at
every framing over the readback-free carrier, and that framing
freedom is what readback removes. At `t⁻ = loop` readback fails by
`loop-nontrivial`.
