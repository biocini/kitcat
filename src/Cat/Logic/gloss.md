# Cat.Logic: gloss

Extended commentary on `Cat.Logic`'s constructions: why a shape is
what it is, or an account spanning modules. The theorem statements
themselves, with their citations, are in
[lemmata.md](lemmata.md), under the same number.

## The framed deductive-system theory

**Retired, 2026-08-03.** `virtual-graph`/`is-deductive-system`
(`Cat.Logic.Type`, `Cat.Logic.Base`) cannot express duploidal
structure: balanced strength collapses polarity, so no carrier has
P and N genuinely distinct, and a duploid needs exactly that
(`src/Cat/Logic/TODO.md`, item 7, the reflection theorem). The
entries below remain machine-checked facts about that construction.
The human vouching for its correspondence to *deductive system*
(`docs/provenance.md`, practice 3) is withdrawn: read this section as
a frozen record, not a foundation to build on.

**T25.** `deductive-system` splits as one structure field and one
property field, and `opᴰ` is an involution. `opⱽ-invol` and
`op-eval` are `refl`. `opᴰ-invol` is `refl` on the carrier, with
the axioms component held by propositionality.

**T26.** Univalence does not depend on the framing
(`univalence-shared` is `refl`). The opposite is the swap of the
two graphs, composed with `rx.op` (`op-graph⁺`, `op-graph⁻`, both
`refl`). The two-sided base is `rx.binary-product (rx.op graph⁻)
graph⁺`. Its reflexive edge is the framing itself: at a diagonal
vertex, the axiom rule becomes one edge.

**T27.** The coslice display takes its displayed reflexivity from
the cancellation alone. Its covariant lifting condition is exactly
stability (uniqueness) plus the coterm cut (existence). `push` is
the composition, and `lift` is the head-rewriting witness, both on
the nose. The absorptions consume no tier. They sit over the pins
and the cancellation alone.

**T29.** The two-sided transport composes onto a base edge. That
edge takes one hand's composition on one coordinate, and the
other's on the other. No single composition makes the lens
functorial. What a mediation buys, read here, is that
functoriality.

The 📐 point: a displayed edge relates data over the two ends of
one base edge. The reflections compared sit at distinct vertices.
A base making them diagonal would make composability reflexive.
This is an argument, not a formalized impossibility.

**T30.** In the group model of the archived `FramedGroup` instance,
the two collapses are equivalent, and the reason localizes the
search: there `reflect` is an associative product, so the cuts
differ only by the junction's twist. A separating model needs a
`reflect` not of that form.

**T35.** The projection model uses a constant reflection over
`Bool`, with both hands as projections. It satisfies the towers
and the readback record of
`Bb.WeakDeductiveSystem.Gist.FramedInterchange`. It computes
`associates f g h` to `h ≡ f`, and it has no thunkable or linear
edge. So it refutes both `associates` and the invertibility tier
at once.

The four-reader model (`Bool × Bool`) is a full
`is-deductive-system`. Its tier centres are its only thunkable and
linear edges. It refutes `associates` for every middle edge,
without refuting invertibility.

The profile is Munch-Maccagnoni's Definition 1 (pre-duploid).
Three associativity laws fix to a polarity pattern on the middle
two objects, `(••)`, `(◦◦)`, `(•◦)`. These match `assoc⁺`, `assoc⁻`,
and `mixed-assoc`.

The identification is SOURCE-CHECKED against
`resources/munch-maccagnoni-duploids` (Definition 1, l.180). It is
cross-checked against `resources/mmmm-classical-notions`, an
independent source that transcribes the same triple (§2,
l.1552-1562, `Statements verified: 7/7 CONFIRMED`, 2026-07-28).
That munch-maccagnoni-duploids entry's certification was withdrawn
2026-07-28, but its Definition 1 digest is among those an
independent read confirmed faithful.

The transcription reverses composition order. The sources compose
applicatively, kitcat diagrammatically, so `(h • g) ◦ f = h • (g ◦ f)`
over `A -f→ N -g→ P -h→ B` becomes `(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)`,
which is `mixed-assoc`. Whether the generic-`associates` refutation
has a counterpart in either source is a separate question. Neither
paper's statement audit addresses it, and this entry does not claim
it. The identification here covers only the associativity profile,
not a broader duploid-source theorem.

**T36.** The defect gives T35's independence a mechanism. The
correction is a power of the bicyclic defect, already on record as
the obstruction to `associates` (T35's countermodel). It is
trivial exactly at the closures `is-deductive-system` already
distinguishes. So the pre-duploid profile is not an arbitrary
cutoff. It is the exact strength at which the correction survives,
and duploid strength is the exact strength that removes it.

The result is a theorem about the free point only. The correction
indices read the model's own edges, and the bare point has no
generators. The generator-bearing word model is the next
instrument.
