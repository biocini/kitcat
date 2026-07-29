# Composability

Each cut is representable.

```agda
is-composable⁺ = ∀ {x y z} (f : hom x y) (g : hom y z)
               → is-representable (composite⁺ f g)
is-composable⁻ = ∀ {x y z} (f : hom x y) (g : hom y z)
               → is-representable (composite⁻ f g)
```

## Existence, against the contractible form

The two predicates above ask for an inhabitant, not a contraction.
On its own each is data, and each becomes a proposition once a
stability is in hand. VERIFIED (`Cat.Logic.Base`):
`is-composable⁺-is-prop` and `is-composable⁻-is-prop`, each taking
that stability.

The record asks for more. It demands each cut's representability
*contractibly*, the representative and its uniqueness in one datum,
so it is a proposition outright and carries no stability index:

```agda
record is-composable where
  field contr⁺ : ∀ f g → is-contr (is-representable (composite⁺ f g))
        contr⁻ : ∀ f g → is-contr (is-representable (composite⁻ f g))
```

VERIFIED (`Cat.Logic.Base`): `is-composable-is-prop`, fieldwise from
`contr⁺-is-prop` and `contr⁻-is-prop`. The contractible negative cut
also proves stability, so the tier this record once carried is a
theorem. See [stability.md](stability.md).

Reading it as a fibration: for each object the coslice family sits
displayed over the graph. The displayed edge over `p` from `u` to
`w` is a representation of `composite⁺ u p`. Composability says that
display is a covariant fibration. The composition is its lift.

## Crossing the opposite

The opposite's positive composite is the negative composite of the
same pair read backwards. A representative therefore transports by
exchanging the argument halves, the same reindexing that carries
stability across.

VERIFIED (`Cat.Logic.Base`):

```agda
op-composable G : is-composable G → is-composable (opⱽ G)
```

with the two fields crossing: the opposite's `contr⁺` comes from the
original's `contr⁻`, and conversely.

## What it yields

The two compositions, and with them everything in
[towers.md](towers.md): distributivity of each action over the hand
it builds, associativity for both hands and for the valid mixed
word, and the pentagon. Two of the four unit laws come from readback
and each hand's own cut. The other two follow from the invertibility
tiers. The theory declares none of it and reads each off a fiber.
