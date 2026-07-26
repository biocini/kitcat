# Mediation

A *mediation* identifies the two cuts.

```agda
is-interchanging = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → composite⁻ f g ≡ composite⁺ f g
```

Cutting through a pending read and cutting through a pending write
deliver the same judgment. It is not a consequence of anything below it:
the two composite judgments carry opposite windings at their junction,
and equating them is a coherence.

## What it adds

VERIFIED (`Test.SpikeNeutralUnit`), over a stability, both
composabilities, the two pins and the cancellation:

**The two compositions become one.** `⨾-agree : f ⨾⁻ g ≡ f ⨾⁺ g`, by
`reflect-lc` — agreeing judgments have equal representatives.

**Each hand gains the unit law it was missing.** `unitl⁻` and `unitr⁺`,
each the other hand's law transported across `⨾-agree`. So the single
composition is unital on both sides.

**A shared neutral unit.** The composite of the two twists — either
juxtaposition, since the compositions are one — is a two-sided unit for
both cuts:

```agda
ι x = twist⁻ x ⨾⁻ twist⁺ x
ι-either  : twist⁻ x ⨾⁺ twist⁺ x ≡ ι x
ι-unitl⁻  : ι x ⨾⁻ g ≡ g          ι-unitr⁻ : f ⨾⁻ ι y ≡ f
ι-unitl⁺  : ι x ⨾⁺ g ≡ g          ι-unitr⁺ : f ⨾⁺ ι y ≡ f
```

None of these is a new axiom about units. All four laws are the two the
framing already gives, transported.

## What it spends

```agda
twists-agree : ∀ x → twist⁻ x ≡ twist⁺ x
```

Derived, in one line: a left unit and a right unit for one composition
meet at their own composite. Once the two cuts agree, **the positive and
negative twists are the same edge**.

So a framing with two genuinely distinct twists and a shared two-sided
unit is not a shape that exists. Either the twists differ and each cut
keeps its own one-sided unit — the theory of these documents — or they
are identified and the two cuts collapse to one with a two-sided unit.
There is nothing between.

## Where the boundary sits

The deductive-system fragment is the first case: two cuts, opposite
windings, one unit law per hand, and no tier relating them. Each hand
carries its own tower, and `ι` is what appears the moment the fragment
is left.

That is also where the asynchronous reading stops being a metaphor. The
two cuts are two disciplines — take from a future, put into a buffer —
and mediating them is a synchronous cut. A theory that mediates has no
framing left to speak of, because its two twists have become one edge.
