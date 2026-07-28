# Bb.UnitalMagmoids

## The construction

A magmoid is a type of objects, a family of hom-types, and a
covariant Yoneda embedding `yon`. The embedding is an embedding in
the HoTT sense. Composition is derived: `f ⨾ g = yon g _ f`. A
virtual graph extends a magmoid with a contractible fiber that
witnesses the identity morphism.

Twelve modules. `Magmoid` states the two records, `magmoid` and
`magmoids`, and their virtual-graph extensions, `virtual-graph` and
`virtual-graphs`. `Base` restates thunkability and linearity as
composability conditions on the Yoneda action, and derives
associativity from them. It also proves the Yoneda embedding
injective.

`Neutral` develops divisibility, cancellability, and the
neutral-morphism theory those conditions support. `Neutral.Eq`
bundles a neutral morphism with left-associativity,
right-associativity, and mediality into the enriched relation
`_∻_`.

`Unit`, `Iso`, and `Eqv` build the unit, isomorphism, and
wild-equivalence theory over a chosen unital morphism. `Map`,
`Nat`, `Coh`, and `Het` cover functors, natural transformations,
pentagon coherence, and heteromorphisms between two magmoids.

`Prod` builds the product of two virtual graphs. Its embedding
proof, and the product magmoid it would support, stay disabled.
The retraction the proof needs closes only when hom-types are
sets, an assumption this suite does not make.

## Provenance

Extracted 2026-07-28 from `Bb.CatsWithExplicitInterchange.Magmoid`.
Nothing outside that suite's own directory imported it, apart from
the archive's index, so it stood on its own.
`docs/composite-rx-refactor/stage-4-cat-rebuild.md` named it under
the stale label `CatData`, and that citation now names this tree
instead.

`Bb.CatsWithExplicitInterchange.Magmoid` traces back further. On
2026-07-24, at commit `55038a9`, the pre-refactor `Cat.*`
development moved whole into `Cat.Depreciated`, and this suite was
nested there as `Cat.Depreciated.Magmoid.*`. Before that move, the
suite lived at the flat namespace `Cat.Data.*`. `Base`, `Het`,
`Neutral`, and `Unit` entered at commit `bbeb0fb` (2026-02-14).
`Coh`, `Eqv`, and `Iso` entered at commit `05fecf0` (2026-02-15).
`Magmoid` and `Map` entered at commit `37547bd` (2026-03-06). `Nat`,
`Neutral.Eq`, and `Prod` entered at commit `65a8507` (2026-03-07).

The suite already carried its Yoneda-embedding formulation at the
`Cat.Data.Magmoid` commit. An earlier, pre-Yoneda draft of the same
suite survives outside the library, at
`reference/magmoid-formulation/Data`. That draft takes composition
as a primitive field instead of deriving it from `yon`.

## Relationships

This suite is an early predecessor in the representable category
research programme. Its Yoneda-embedding formulation of
composition, and its per-morphism vocabulary of thunkability,
linearity, and mediality, feed the live `Cat.Logic` deductive-system
design.

`notes/2026-07-22-deductive-system-design.md:111` names the
connection directly. It states that the duploid texture of a
deductive system is the pattern of thunkable, linear, and medial
conditions per morphism. This suite's `Neutral` module already
inventories that pattern.

No module here imports `Cat.*`. The suite rests on `Core` alone.
