# Bb.CatsWithExplicitInterchange

## The construction

A category presented through a representable embedding of an edge
into the composite operators it induces. The carrier is a
reflexive graph. A composite between two objects is a function.
It takes any context based at those objects, and returns an arc
between that context's anonymous endpoints. `emb` is the two-sided
embedding `f ↦ λ (a , b) → b ∘ f ∘ a`. A composite is
representable when it lies in the image of `emb`, which is a fiber
condition. So the theory names one operation and derives the rest.

The axioms are four fields. `emb` is the embedding. `interchange♭`
says the two ways of splicing one representable composite into
another agree. `interchange f g : emb f ▾ g ≡ f ▴ emb g` is that
claim at two edges. `spine-contr` makes the coherence over
that instance contractible. `unit` says evaluation at the two
reflexive edges returns the edge. The records take the name
`category`. They are wild categories, since hom types are never
sets by fiat. The tree proves that higher coherences arrive
without a truncation assumption.

Forty-nine modules. The composite-witness development is `Type`,
`Base`, `Coherence`, `Displayed`, `Functor`, `Iso`, `Morphism`,
`Op`, `Properties`, `Terminal`, `Groupoid`, and the `Limits`. The
monoidal layer carries its own `Legacy` archive of the earlier
braid, hexagon, and twist material. The `Gist` modules hold the
Test spikes and probes vendored for this stratum.

## Provenance

Moved into the archive on 2026-07-28, from `Cat.Depreciated`.
Module declarations and internal imports carry the new prefix, and
the move re-points the citations in `docs/composite-rx-refactor/`.

`Cat.Depreciated` was itself a relocation. On 2026-07-24, at
commit `55038a9`, the pre-refactor `Cat.*` development moved there
whole. It stands as the reference tree for the new foundations,
`Cat.Logic` and `Core.Rx`. Nothing outside the tree
imported it then, and nothing does now. It measured 49 modules
and 15,545 lines at that move, and every module checked clean.

## Relationships

This is the category theory that precedes the virtual-graph line,
and interchange is the point of contrast. Here the record declares
one embedding, and a field says the two splices agree. In
`Bb.WeakDeductiveSystem` and its successor `Cat.Logic` nothing
declares a composition. Both cuts are projections of fibers of
`reflect`. The two hands genuinely differ, and the failure of
interchange measures the double twist. In `Bb.VgCategoryShape` the
two hands agree again, and interchange is a theorem rather than a
field.

The tree is the porting reference for the rebuild that the
deductive-system line owns (`docs/roadmap.md` project 1). That
rebuild ports it onto the deductive system and retires it unfixed.
Decision D8 of `docs/composite-rx-refactor/` holds it green until
then, and what `Core` keeps on its account carries a placement
contract. The contract gives each of the nineteen held
displaced-composition names two fates. Either a principled home
restates it over the disciplined backend, or it goes with the tree
that consumed it. The census is in
`docs/composite-rx-refactor/evidence.md`.

No module here imports `Cat.*`. The tree rests on `Core` alone,
so a change to `Core` is the only upstream change that can break
it.
