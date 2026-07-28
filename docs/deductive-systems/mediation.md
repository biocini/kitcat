# Mediation

A *mediation* identifies the two cuts.

```agda
is-interchanging = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → composite⁺ f g ≡ composite⁻ f g
```

Cutting through a pending read and cutting through a pending write
deliver the same judgment. Nothing below it implies it. The two
composite judgments carry opposite windings at their junction, and
equating them is a coherence.

## What it adds

VERIFIED (`Cat.Logic.Gist.NeutralUnit`), over a stability, both
composabilities, the two pins and the cancellation:

**The two compositions become one.** `⨾-agree : f ⨾⁺ g ≡ f ⨾⁻ g`, by
`reflect-lc`: agreeing judgments have equal representatives.

**Each hand gains the unit law it was missing.** `unitl⁺` and
`unitr⁻`, each the other hand's law transported across `⨾-agree`. So
the single composition is unital on both sides.

**A shared neutral unit.** The composite of the two twists (either
juxtaposition, since the compositions are one) is a two-sided unit
for both cuts:

```agda
ι x = twist⁻ x ⨾⁺ twist⁺ x
ι-either  : twist⁻ x ⨾⁻ twist⁺ x ≡ ι x
ι-unitl⁺  : ι x ⨾⁺ g ≡ g          ι-unitr⁺ : f ⨾⁺ ι y ≡ f
ι-unitl⁻  : ι x ⨾⁻ g ≡ g          ι-unitr⁻ : f ⨾⁻ ι y ≡ f
```

None of these is a new axiom about units. All four laws are the two
the framing already gives, transported.

## What it spends

```agda
twists-agree : ∀ x → twist⁻ x ≡ twist⁺ x
```

Derived, in one line: a left unit and a right unit for one
composition meet at their own composite. Once the two cuts agree,
**the positive and negative twists are the same edge**.

So a framing with two genuinely distinct twists and a shared
two-sided unit for **both** cuts is not a shape that exists.

## Collapsing the framing is less than mediating

The one-line derivation uses a left and a right unit for *one*
composition, not the agreement of the two. So it goes through on
either missing unit law alone. VERIFIED (`Cat.Logic.Base`):

```agda
collapse⁺ : (∀ {x y} (g : hom x y) → twist⁻ x ⨾⁺ g ≡ g) → ∀ x → twist⁻ x ≡ twist⁺ x
collapse⁻ : (∀ {x y} (f : hom x y) → f ⨾⁻ twist⁺ y ≡ f) → ∀ x → twist⁻ x ≡ twist⁺ x
```

A mediation *supplies* those laws, so each hypothesis above is
weaker as a statement than interchange. Two collapses then need
telling apart:

- **framing collapse**: the twists are one edge
- **cut collapse**: the compositions are one operation

Interchange gives both. Either missing unit law gives the first, and
nothing in this theory carries it to the second.

Whether the two are actually separable is open. In the group model
(`Cat.Logic.Gist.FramedGroup`) they are not: VERIFIED there, agreement of the
two cuts is *equivalent* to equality of the two framing elements
(`cuts-agree→` and `→cuts-agree`). The reason is visible in that
model, and it is a constraint on where a separating one could live.
Its `reflect` is an associative product, so the two cuts differ only
by the junction's twist, and identifying the twists identifies them.
A model separating the collapses must have a `reflect` that is not
of that form. Such reflections exist: `Test.ExtractedTwistCancel`
twists one by a permutation. Whether one of them separates the
collapses is untested.

## Where the boundary sits

The deductive-system fragment is the first case: two cuts, opposite
windings, one unit law per hand, and no tier relating them. Each
hand carries its own tower, and `ι` is what appears the moment the
fragment is left.

That is also where the asynchronous reading stops being a metaphor.
The two cuts are two disciplines (take from a future, put into a
buffer), and mediating them is a synchronous cut. A theory that
mediates has no framing left to speak of, because its two twists
have become one edge.
