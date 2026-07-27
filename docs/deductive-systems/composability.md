# Composability

Each cut is representable.

```agda
is-composable⁺ = ∀ {x y z} (f : hom x y) (g : hom y z)
               → is-representable (composite⁺ f g)
is-composable⁻ = ∀ {x y z} (f : hom x y) (g : hom y z)
               → is-representable (composite⁻ f g)
```

## Existence only

The statement asks for an inhabitant, not a contraction. On its own that
is data; it becomes a proposition exactly once a stability is in hand,
and so the record is indexed by one:

```agda
record is-composable (S : is-stable) where
  field contr⁺ : is-composable⁺
        contr⁻ : is-composable⁻
```

VERIFIED (`Cat.Logic.Base`): `is-composable⁺-is-prop`,
`is-composable⁻-is-prop` and `is-composable-is-prop`, each taking the
stability the record is indexed by. Uniqueness is stated once, in
[stability.md](stability.md), and recovered wherever wanted by
`contr-from-stable`.

Reading it as a fibration: for each object the coslice family is
displayed over the graph, the displayed edge over `p` from `u` to `w`
being a representation of `composite⁺ u p`, and composability is that
display being a covariant fibration. The composition is its lift.

## Crossing the opposite

The opposite's positive composite is the negative composite of the
same pair read backwards, so a representative transports by exchanging
the argument halves — the same reindexing that carries stability across.

VERIFIED (`Cat.Logic.Base`):

```agda
op-composable G S : is-composable G S → is-composable (opⱽ G) (op-stable G S)
```

with the two fields crossing: the opposite's `contr⁺` is built from the
original's `contr⁻`, and conversely.

## What it yields

The two compositions, and with them everything in
[towers.md](towers.md): distributivity of each action over the hand it
builds, associativity for both, one unit law per hand, and the
pentagon. None of it is declared; each is read off a fiber.
