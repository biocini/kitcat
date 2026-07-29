# The lenses, and each cut as a fibration

`Cat.Logic.Display` states the two argument families in lens
vocabulary and each cut as a lifting condition. It consumes the seam
of [graphs.md](graphs.md) and the two cancellations. The fibration
reading also consumes stability and one cut.

## Each family is a lens over the graph of the twist it does not hold

A lens states its unitor at the base's reflexive edge. Each family's
lens takes the other graph as its base. The unitor is then a
cancellation, not an identity.

VERIFIED (`Cat.Logic.Display`):

```agda
term-lens   : oplax-cov-lens (graph⁻ G) (term-fam   G)   -- push = act,   unitor = absorb⁺
coterm-lens : lax-ctrv-lens  (graph⁺ G) (coterm-fam G)   -- pull = coact, unitor = absorb⁻
```

The covariant family transports forward and its cancellation points
back at the vertex. The contravariant one transports backward and
its cancellation points forward. The two unitor shapes a lens admits
are exactly the two absorptions.

Both families are discrete, hence path objects, so both displays are
univalent with no condition on the base. VERIFIED:
`term-disp-univalent`, `coterm-disp-univalent`. This matters because
the base of a deductive system is not in general a path object, and
every uniqueness theorem about lens *structure* hypothesizes that it
is.

## The absorptions consume no cut and no tier

`framed` takes the two cancellations and nothing else. Neither
representation's uniqueness nor either cut's existence appears in
it. VERIFIED (`Cat.Logic.Display`): `absorb⁻` and `absorb⁺` follow
there from the cancellations alone. Over a deductive system the two
tiers prove those cancellations, so the hypotheses arrive
discharged. See [invertibility.md](invertibility.md).

## The coslice, and the cut as a lift

The edges out of a fixed object, displayed over the positive graph,
with a displayed edge over `p` recording that its target represents
the positive composite:

```agda
coslice a .vtx z          = hom a z
coslice a .edge _ _ p u w = reflect w ≡ composite⁺ u p
coslice a .rx u           = the cancellation
```

Displayed reflexivity is the cancellation and nothing more. The
display's statement consumes no cut.

A displayed edge out of `u` over `p` is precisely a representation
of `composite⁺ u p`, so the lifting condition is that
representation's contractibility. VERIFIED (`Cat.Logic.Display`):

```agda
coslice-fibration a : rx.is-cov-fibration (graph⁺ G) (coslice a)
```

assembled from stability (uniqueness) and the coterm cut
(existence): the two halves of the tier split exactly along the two
halves of contractibility. And the fibration's operations are that
hand's own, on the nose:

```agda
push-is-cut     : F.push a y z p u ≡ u ⨾⁺ p
lift-is-witness : F.lift a y z p u ≡ reflect-⨾⁺ u p
```

The composition **is** the pushforward and the head-rewriting
witness **is** the lift. A free consequence: a fibration is a path
object as a display, so `coslice-univalent` holds with the base
unconstrained.

The negative hand is this text at `opⱽ`, where the coslice becomes
the slice and the covariant fibration the contravariant one.

## The two-sided display

Over the base of [graphs.md](graphs.md) the judgment family is the
vertex family of one covariant lens. VERIFIED (`Cat.Logic.Display`):
`judgment-lens` with transport `bipush` and unitor

```agda
bipush-axiom α : bipush (twist⁻ x) (twist⁺ y) α ≡ α
```

the two cancellations together. `judgment-disp-univalent` holds as
well, again with no condition on the base.

So mixed variance is a property of the presentation, not of
`judgment`.

## Interchange is a cospan, hence not an edge

Each composite judgment is the two-sided transport with one leg held
at its twist, applied to one factor's reflection. VERIFIED:

```agda
push-is-composite⁺ f g : bipush (twist⁻ x) g (reflect f) ≡ composite⁺ f g
push-is-composite⁻ f g : bipush f (twist⁺ z) (reflect g) ≡ composite⁻ f g
```

```
            (x , y)                     (y , z)
               \                           /
      (twist⁻ x , g)               (f , twist⁺ z)
                 \                     /
                     ‾‾‾ (x , z) ‾‾‾
```

The two sources are distinct vertices and the legs point the same
way, so the configuration is a cospan. Agreement of the two cuts is
agreement of its two pushforwards. VERIFIED both ways,
`cospan-from-cuts` and `cuts-from-cospan`.

No display of `judgment` can carry that agreement as an edge. A
displayed edge relates data over the two ends of *one* base edge,
and the reflections under comparison sit at `(x , y)` and `(y , z)`.
A base making those diagonal would make the composability relation
reflexive.

## What the lens is not

The two-sided transport composes, but the base edge it lands on
takes the one hand's composition on the backward coordinate and the
other's on the forward one. VERIFIED (`Cat.Logic.Display`):

```agda
bipush-comp : bipush a' b' (bipush a b α) ≡ bipush (a' ⨾⁻ a) (b ⨾⁺ b') α
```

No single composition makes the lens functorial. A lens is exactly
the structure that survives without a mediation: transport and a
unitor, no functoriality. What a mediation buys, read here, is that
functoriality. See [mediation.md](mediation.md).
