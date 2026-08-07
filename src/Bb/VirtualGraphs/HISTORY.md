# History: Bb.VirtualGraphs

The narrative record of this tree. `README.md` states what the
construction is. `CHANGELOG.md` logs what changed and what the checker
said. Neither carries narrative, by the rule in `src/Bb/CLAUDE.md`.
This file is the namespace's one exception. It holds the whole arc: the
attempts, the failures, the renames, and the later corrections.

Every beat below names where its content lives now. A beat that ended
in a dead end says so instead.

---

## Before there was a carrier (2026-07-14 to 2026-07-21)

The arc starts in a different subject. Through mid-July 2026 the work
was monoidal coherence: the pentagon, the triangle, and the displaced
cells above them. Three habits formed there. All three survive in this
tree.

The first is the wit calculus, named in
`notes/2026-07-19-wit-calculus-triangle.md`. That session tried four
routes to `assoc⋉₁-nrm`. Every one failed on the same obstruction,
which the note calls the fst-wobble. A bridge between two lifts in a
contractible fiber keeps an uncontrolled interior, and the object type
carries no truncation. The fix was not a better bridge. The associator
became a projection out of the representability fiber instead.

That is the one-construction principle. The same session built a
`Cat.Displayed` module, where `is-representable[_]` was literally the
fiber of `emb[_]` over a witness. That module no longer exists. The
principle it carried does, at every projection in this tree.

The second habit is coherence by contractibility of a representability
fiber. `Pentagon.lagda.md` runs exactly that argument today. The five
bracketings of a four-fold cut are five points of one fiber of
`reflect`. The embedding condition makes that fiber a proposition,
so any two paths between two of its points agree.

The third is a ruling. `notes/2026-07-21-unpinned-spine-brief.md`
records it verbatim: "Never index by the invariant you intend to
derive" (Lane, 2026-07-21). An intermediate proposal graded the spine
axiom over the integers, and Lane ruled it wrong-shaped. The brief also
names the fork the session had to settle. An overlay posits the half-twist
as data. An un-pinned spine derives it. The brief takes the second
route and forbids starting with the first.

The braided and ribbon work of the same days
(`notes/2026-07-20-braided-layer.md`,
`notes/2026-07-20-ribbon-arc.md`) is a concurrent thread, not this one.
It matters here for one reason. It set the target vocabulary that the
later naming audit found this tree had borrowed too early.

---

## The design that named the tiers (2026-07-22)

`notes/2026-07-22-deductive-system-design.md` is where the object
appears. A virtual graph is a reflexive graph plus a ternary
representable action, called `emb` there. A deductive system is that
graph plus three propositional tiers: `is-composable`, `is-unital`, and
`is-stable`. The name comes from Lambek and Scott, with homs read as
deductions and composition as cut.

Two commitments in that note run through everything after it. Never
declare a composition, declare a contractible fiber and project it.
And a deductive system has two compositions, not one. A single
composition is exactly what a mediation buys.

Lane ruled the third tier's name the same day. It follows Abel's
stability, the normalization-by-evaluation law that reading back an
evaluated term returns the term. That name survived thirteen days of
development and then lost an audit. It is `reflect-is-embedding` here
now, in `Embedding.lagda.md`.

The note also lists obligations O1 through O6. O4 asks for the
truncated-regime certificate, that hom sets give stability.
`Embedding.lagda.md` discharges it as `embedding-from-hom-sets`.

---

## The backend, and where `rx` comes from (2026-07-24)

`docs/composite-rx-refactor/` opened as the plan of record for the
reflexive-graph machinery underneath. It carries the naming ruling:
the promotion target is `Core.Rx`, on Lane's suggestion of `Rx` over
`Graph.Refl`, 2026-07-24. The namespace was `Cat.Graph.Refl` at the
time. The rename itself waited until commit `8f4be13` on 2026-08-04.

`Rx` is not a coinage. `Core.Rx.Type` declares `reflexive-graph` with
three fields, and the third is `rx`, the reflexive edge at every
vertex. The namespace took the field's name. Eleven days later the
field's name took over the half-twist families, for reasons the naming audit
gives below.

Lane ruled two more names there. The composability tier is
`is-composable`, correcting prose that had drifted to `is-composite`.
The ternary action is `emb` in the backend and `reflect` in the
frontend. One operation carries two vocabularies that agree
definitionally. `reflect` is the carrier's one axiom field in
`Type.lagda.md` today.

`notes/2026-07-24-refl-inference-policy.md` settled which arguments an
edge-indexed signature may hide. Its verdict was that a family never
determines its base, so endpoints stay explicit. Every theory module in
this tree still names its endpoints.

The refactor itself never ran. `docs/roadmap.md` gates it behind the
deductive-system line reaching a category presentation. Its own README
expects a rewrite rather than an execution. The presentation it waited
for is `Presentation.lagda.md`.

---

## The chosen edge, and why it lost (2026-07-24 to 2026-07-25)

The first carrier was not framed. It carried objects, edges, one chosen
edge `idn` at each object, and `reflect`. The chosen edge filled both
halves of an argument, so `var a` was `(a , idn a)` and `covar y` was
`(y , idn y)`. Twelve spikes probed it across 2026-07-24 and
2026-07-25.

They produced a negative-result dossier, and the dossier is why the
form lost. Nothing in `reflect` mentions the chosen edge, so the
carrier holds it freely. A predicate that makes the graph a deductive
system has to say the edge absorbs (`AbsorbObstruction`). A unit datum
is propositional only as a fiber of the action map. Every such form
projects its unit from the fiber centre, never from the chosen edge
(`UnitCanonical`). Identifying the two is then a path in a hom type,
which no proposition over that carrier can assert (`StabilityShape`).

On 2026-07-25 a pair of half-twist families replaced the chosen edge, and
the two unit tiers moved onto the crossed pairing. That left the twelve
spikes stating facts about a carrier the library no longer had.
`notes/2026-07-25-cat-logic-decomposition.md` records the verdict as
superseded rather than promotable. The spikes moved to
`Bb.NaiveVirtualGraph` on 2026-07-28.

Two of that dossier's results live here. `UnitShape.lagda.md` carries
the shape computation. Its `datum≃path` proves the identification datum
is a path in a hom type, and the self-referential variant closes the
file. `Engine.lagda.md` carries the chosen-edge theory itself. It
proves the fiber-contractibility engine over composability and
unitality alone, with no readback and no embedding-condition
hypothesis. The rest of the dossier's rows landed 2026-08-06 —
`CrossedUnit.lagda.md`, `Reflexive.lagda.md`, `Stable.lagda.md`,
`Curried.lagda.md`, `Groupoid/Engine.lagda.md`, and extensions to
`Engine.lagda.md` and `UnitShape.lagda.md` itself — with
`Lens.lagda.md` and `Displaced.lagda.md` following the same day, once
a displayed carrier no longer ruled out a second record. Only the
`PathGroupoid` model stays unvendored.

---

## Two lineages meet on one carrier (2026-07-25)

`notes/2026-07-25-two-lineages.md` read the framed carrier against two
corpora at once. Sterling's reflexive-graph lens theory sat on one
side, and the Melliès and duploid material on the other. The two axes
turned out not to be orthogonal. The duploid line's own carrier, a
non-associative category, is a reflexive graph with a composition law.
Sterling's carrier is the duploid line's carrier.

The identification that follows is the one this tree still runs on. A
half-twist is a reflexivity datum. A virtual graph therefore carries two
reflexive-graph structures on one underlying graph, differing only in
which family supplies the reflexivity. `Graph.lagda.md` says exactly
that. `Display.lagda.md` reads each argument family as a lens over the
other hand's graph, with each cut a fibration. Both import the live
`Core.Rx`, and they are two of the four modules here that do.

The same note found the crossing that `Framing.lagda.md` now states as
its own authority. The term half's centre comes from one graph and the
coterm half's from the other. The axiom pairs one from each. That
crossing is what the framing is, and not an artefact of naming.

The note also corrected a claim in the documentation of the time. A
missing unit law alone gives the framing collapse, where the half-twists
become one edge. That is weaker than a mediation. `collapse⁺` and
`collapse⁻` sit in `Tower.lagda.md` with the crossed pairing as an
explicit hypothesis. Whether framing collapse separates from cut
collapse was left open, and it is still open.

---

## The one-half-twist proposal loses (2026-07-27)

The negative tier mentions `coact-π`, hence `var`, hence one half-twist
alone. So the tier is stateable before a second half-twist exists, and its
centre defines one. That was the one-half-twist proposal: hold one family,
extract the other, and drop a field.

A countermodel settled it against on 2026-07-27. The deciding lemma is
the term-side cancellation. The model is the Klein four-group on
`Bool × Bool` under componentwise exclusive or. Its reflection reads
the edge through a three-cycle of the non-unit elements. Extraction
walks the cycle, so the extracted half-twist and the positive tier's centre
sit one step apart, and the cancellation fails.

`notes/2026-07-27-one-half-twist-verdict.md` records why the countermodel
needed a half-twisted reflection. Where `reflect` is a plain composite,
one-sided identities meet and manufacture a unit. Groups, monoids, and
path groupoids therefore satisfy the cancellation automatically. That
closed the obvious search and forced the permutation.

The proposal's evidence became `Bb.OneTwist` on 2026-07-28, and all of
it is here now. `Extraction.lagda.md` holds the general construction,
where the negative tier's centre defines the positive family and the
unit laws come free. `Bool/Klein.lagda.md` holds the countermodel, with
`no-cancel⁺` and `no-agree` refuting the cancellation and the centre
agreement at once.

`Groupoid/Path.lagda.md` and `Group/Abelian.lagda.md` hold the positive
controls, which showed the refutation was narrow rather than a blanket
failure. In `Group/Abelian.lagda.md` the one-half-twist module proves
`corx-forced`. Whatever proof the negative tier receives, its centre is
the inverse of the posited element.

---

## Three renames and one vacuous pair (2026-07-27)

The same days carried a rename pass. The old forms are worth naming,
because two of them were wrong rather than merely different.

The unit tier was misnamed. Working the string out shows what the two
clauses say. One half-twist has a unique right inverse, and the other has a
unique left inverse. That is invertibility of the framing and not
unitality. The name was a holdover from the single chosen edge. So
`is-unital⁻` and `is-unital⁺` became `is-invertible⁻` and
`is-invertible⁺`. They are `is-absorbing⁻` and `is-absorbing⁺` here
now, after a 2026-08-05 pass found "invertible" wrong for the opposite
reason.

The handedness labels on the two towers ran backwards against the
duploid dictionary. The pass swapped the composition register to fix
it, and left the framing register untouched. That is why the two
registers cross in `Framing.lagda.md` today.

The third rename repaired a real defect. `mixed-leading` and
`mixed-trailing` had closed over the valid mixed word, which is a
theorem of the embedding condition and the two cuts. So the closures
held for every edge and said nothing. They moved to the failing word
and took the names `thunkable` and `linear`, after the duploid
literature. `Tower.lagda.md` now carries `mixed-assoc` as a theorem in
its `mixed` module. `associates` is the withheld word, with `thunkable`
and `linear` closing over it.

---

## The record cut (2026-07-28)

The cut is the largest single change in the arc. `virtual-graph` gained
a `readback` field, the correctness equation of normalization by
evaluation, stated unit-free. The predicate became contractible cuts
plus invertibility. And the `stable` field went, because at that
strength it is a theorem of the contractible negative cut.

What readback buys is a short list, and `Readback.lagda.md` holds all
of it. Each composition is its own action read at the axiom. Each hand
gains the unit law at its own half-twist. The negative composite at the
half-twist is a reflection, so a contractible negative cut yields the
embedding condition. The module's `residues` names what readback does
not reach.

What the two absorption tiers then buy sits in `Cancellation.lagda.md`.
Each tier's centre reads back as the other half-twist, which is
`centre⁻-corx` and `centre⁺-rx`. Both cancellations therefore become
theorems, the absorptions follow, and each hand gains its far unit law.
The result is two unital magmoids on one graph, offset by the double
half-twist.

An inference failure surfaced during the cut and produced a standing
guideline. The unifier recovers an implicit record parameter by eta.
That recovery is complete only while every field occurs in the unfolded
predicates. `readback` occurs in none of them, so the cut broke every
such signature at once. The carrier became an explicit parameter. Every
theory module here takes its carrier explicitly, and this is why.

Lane ruled that the live tree carries no red modules. Five free-framing
spikes stated facts that readback removes, so they moved to the archive
rather than break. `AssociatesCountermodel` is here as part of
`Bool/Readers.lagda.md`. `FramedCut` is `Groupoid/Path.lagda.md`.
`FramedGroup` is `Group/Abelian.lagda.md`. `NeutralUnit` and
`TwistFidelity` are the second and third parts of
`Interchange.lagda.md`.

The label `(D′)` had named the adopted position against two rejected
ones. It left live prose the same week, because it read as one variant
among several when it was the definition.

---

## The archive opens (2026-07-28)

The `Bb.*` namespace opened on 2026-07-28 to hold the cut's residue,
and four trees landed in one day. `Bb.WeakDeductiveSystem` is
`Cat.Logic` frozen immediately before the cut, so reading the two side
by side shows what readback buys. `Bb.OneTwist` is the rejected
carrier. `Bb.NaiveVirtualGraph` is the chosen-edge dossier.

`Bb.VgCategoryShape` is a staging tree. Its record `hcategory` carries
one chosen edge together with readback, which is a different form from
the chosen edge without it. It is the direct source of
`Diagonal.lagda.md`.

Its `Parity` module carried a refutation. The two-element heap carries
two structures on one graph and one reflection, differing only in the
origin. So no condition on `reflect` alone selects the chosen edge.
That is `Bool/Heap.lagda.md` here, and `half-twist-moves-the-origin` is the
lemma that carries one origin to the other.

One lemma did not survive the port, and its absence is the point.
`Parity`'s `same-reflection` compared two separately bundled instances.
Here the redundancy it closed never opens, because one graph aligns
both origins. What the lemma proved is definitional.

---

## Thunkability is data, and the free point (2026-07-28)

Two results settled the shape of the theory in the same week.

The first is that thunkability is data and not property. A length-four
compatibility square went over any carrier with both cuts, and the
circle model refuted propositionality of `thunkable` and of the
square-refined closure. The reason is general. The freedom in a witness
is a loop-space action, uniform shifts are natural, and no coherence
tower truncates that. The path groupoid was the wrong test bed. A hom
type with its own fundamental group is what reaches it.
`Circle/Thunkable.lagda.md` carries the argument, and the model itself
is `Circle/Model.lagda.md`.

The second is the free balanced point. Bounded congruence closure to
six leaves solved the word problem empirically, before anything was
formalized. Two hand-derived normal-form grammars had already died on
critical pairs. The congruence data, not inspection, chose the carrier:
weakly monotone eventual translations of the naturals, presented by
canonical descriptors with no quotient.

That model refutes generic associativity at the free point. So the
associativity profile is exactly pre-duploid plus the mixed law, the
four unit laws, and the half-twist-flanked family. It also carries an
integer grade on endo-homs, with the double half-twist as the generator.
`Word/Carrier.lagda.md` holds the descriptors, `Word/Model.lagda.md`
the carrier and its tiers, and `Word/Polarity.lagda.md` the generation
theorem `gen-all` with the two refutations.

---

## The defect, measured (2026-07-29)

The countermodel said associativity fails at the free point but named
no relation between the two bracketings. This session found the
relation, and it is sharper than a failure.

The search enumerated every well-typed placement of a correcting word
between the two bracketings. Sixteen placements, fourteen refuted
outright at two concrete triples, two survivors. Each survivor reads
one flanking edge alone, and holds for every triple with no failure
hypothesis. No uniform word exists in any placement, so the defect is
not a framing constant.

`Word/Defect.lagda.md` holds all of it. `defect⁺` corrects on the
leading side, through the value of the edge at zero. `defect⁻` corrects
on the trailing side, through the length of the trailing edge's zero
plateau. The module also carries the refutations and
`shift-associates`, which proves the two bracketings always agree in
winding grade.

The result gave the axioms a reason rather than a stipulation. The
leading correction vanishes exactly when the leading edge is thunkable.
The trailing one vanishes exactly when the trailing edge is linear.

Two process facts from that session are on record, because they cost
time. A first attempt stopped by hand and did not resume, since a
user-initiated stop and a self-paused agent are different states. The
relaunched attempt only produced work once its instructions demanded
concrete checks against the checker rather than abstract reasoning.

---

## The polarity collapse, and what it closed (2026-07-29)

Polarity crossed over with nothing truncated. An object is positive
when every edge out of it is linear. It is negative when every edge
into it is thunkable. `Polarity.lagda.md` carries the definitions and
the citation.

The citation itself was a defect, found by adversarial review and
fixed. The source is Clairambault and Munch-Maccagnoni, *Duploid
situations in concurrent games* (GaLoP XII, 2017). It is not Definition
1 of the duploids paper, which states polarity as primitive data rather
than deriving it. The wrong citation had already spread into three
files before the review caught it.

Two models measured the h-level and disagreed usefully. At the circle
both polarities hold at the one object, and neither is a proposition.
The pointwise shift of a witness is again a witness, one winding away
(`Circle/Polarity.lagda.md`, with `filler-distinct`). At the word model
homs form a set, both polarities are propositions, and both are empty
(`Word/Polarity.lagda.md`).

Then the headline. The two half-twist conditions at an object imply each
other, at every object of every full system. So positive and negative
are one predicate, and no carrier separates them. That closes the two
models retroactively. Holding both and holding neither are the only two
ways the equivalence can hold. The collapse sits at the end of
`Cancellation.lagda.md`, in its `collapse` module, with `from-linear`
and `from-thunkable` running the two directions.

The consequence was not a theorem but a blockage. The capstone target
asks for a system's polarized and balanced core to be a duploid. There
is no such core to work with. Balance is exactly the strength at which
polarity collapses. `src/Cat/Logic/TODO.md` records the target as
blocked, and not merely undone.

Two other results landed the same day and both are here.
`Presentation.lagda.md` reformulates a fully cancelling carrier as a
wild category with one endo-operator, in both directions. Hom sets
discharge the residue, which stands open over wild homs.
`Circle/Shift.lagda.md` settles the reflection square at the circle for
two readbacks that differ by one winding. Exactly two presentation laws
move under the retuning.

A dispatch failure is on record from that session, because it changed
later practice. The polarity-distinguishing spike went first to a model
that ran fifty-four minutes with zero tool calls and produced nothing.
A retry elsewhere demanded a file artifact and a checker run early, and
completed. Every remaining open-ended construction spike that session
went the second way.

---

## Recognition, and the torsor correction (2026-08-02 to 2026-08-03)

The polarity collapse ended one line and opened another. The shipped
construction cannot express the target concept, so a replacement
candidate was worth trying. The candidate was to stop giving the half-twist
pair and start recognizing it.

That line runs on a genuinely minimal carrier: objects, edges, and
`reflect`, with no half-twist fields at all. `Type.lagda.md` is that
carrier, ported unchanged from the spike tree on 2026-08-04. Thirteen
spikes ran against it across 2026-08-02 and 2026-08-03. They pinned the
pair by a Kraus-style argument instead of positing it.

Then Lane found a methodological error running through the whole
sequence. The spikes had scored circle-model results by asking whether
the space of satisfying pairs is contractible, and read non-contraction
as flat failure. The correct criterion asks whether the free pairs form
a torsor, an orbit under exactly the group the canonical generator
generates. The note states the incoherence plainly. Conflating "a
canonical generator exists" with "the group it generates is trivial"
demands the generator's existence while demanding it generate nothing.

`notes/2026-08-03-vgds-torsor-correction.md` is the correction, and it
is careful about scope. The Agda is sound everywhere. Five spikes'
prose verdicts are contaminated. Degree-balance and vacuous-instance
refutations do not depend on the criterion and stand. Word model
results are untouched, because the invertible centre is trivial there,
so generator uniqueness and orbit collapse coincide.

The correction is prose so far. Nobody has pinned it as a checkable
predicate, and until that happens the five spikes' verdicts stay
unrewritten. The plan behind this tree's consolidation therefore
carried a binding rule. Theorem statements cross over. No "succeeds"
or "refutes" framing crosses over from a contaminated reading.
`TODO.md` repeats the rule for the vendoring still to come.

The naming residue is visible in `Circle/Torsor.lagda.md`. Its theorem
is named `torsor` and it refutes contractibility, which reads oddly
against the noun. The 2026-08-05 audit noted this and left the name
alone.

The same session deleted `docs/deductive-systems/`, twelve files
written between 2026-07-24 and 2026-07-28. The grounds were premature
documentation of a construction now known inadequate to its target.
Retirement banners went onto the `Cat.Logic` ledgers and the module
header, and the individual statuses stayed untouched. They are still
true and still machine-checked, and they are not a foundation to build
on. The deletion landed in commit `8f4be13` on 2026-08-04, alongside
the `Cat.Graph.Refl` to `Core.Rx` rename planned eleven days earlier.

---

## The consolidation (2026-08-04)

The tree opened on 2026-08-04 with the carrier alone. It grew to thirty
modules the same day, in dependency order, with a checker run gating
each landing.

One architectural rule governed the whole vendoring. `virtual-graph` is
the only record in the tree. Every further assumption enters as an
explicit parameter of the lemma module that needs it. One statement
therefore covers every stratum that can supply the parameters. That is
why `Framing.lagda.md` splits three ways, along which family each
definition reads. It is also why `Tower.lagda.md` gives each hand its
own telescope. `tower⁺` takes one half-twist, the embedding condition, and
the positive cut. `tower⁻` takes the mirror. Only `tower` needs both.

The general theory landed first. Then the frame theory, the extraction,
and the diagonal. Then the presentation and the reflexive-graph
reading. Then the engine and the models. The per-module source mapping
is in `CHANGELOG.md`, and the plan that produced the layout is
`outputs/.plans/virtual-graphs-vendor.md`.

The scope rule was committed sources only. Material that exists solely
in `Test.*` waited, which is why the recognition line's own results are
not here yet. `TODO.md` names the thirteen files, and repeats the
torsor rule that governs importing them.

---

## The naming audit (2026-08-05)

The audit checked every named phenomenon in the thirty modules against
established usage. It is `outputs/virtual-graphs-naming-audit.md`. Its
own methodology changed between passes, which is the more useful half
of the story.

An earlier pass asked whether a reader could guess the right sense. The
final pass asks two harder questions. Does the machine-checked content
establish what the cited concept requires? And would a future reader
taking the name as vetted assume theorems the corpus does not earn?
Under the stricter test three verdicts moved. Two names the earlier
pass had excused as adequately hedged in prose became conflicts.
Documented intent explains why a name is present. It is not evidence
that the object satisfies the concept. Three more names dropped from a
full match to a qualified one, on missing components or missing
evidence.

The audit also corrected itself on a matter of fact. An earlier pass
wrote that the half-twist families "are not natural, and they are not
mutually inverse until the `Balanced` layer makes them so". That runs
three conditions together and is wrong on two. The cancellation layer
does not make the half-twists mutually inverse. It does not make them equal
either. It makes each a two-sided unit for its own hand, after which
naturality becomes derivable and empty. The same pass withdrew two
proposed alternative names, since the tree's own `pair⁺` and `pair⁻`
refute them.

Five names were corrected tree-wide on 2026-08-05.

- `half-twist⁻` and `half-twist⁺` became `rx` and `corx`. Neither carries a
  ribbon-half-twist or a naturality claim, and `rx` continues
  `Bb.VgCategoryShape`'s own name for the same role.
- `Balanced.lagda.md` became `Cancellation.lagda.md`, with the internal
  module renamed to match. A balanced monoidal category needs a tensor
  and a braiding, so the defining law was never statable here. The
  fragment that is statable is refuted by `pair⁺`.
- `is-invertible⁻` and `is-invertible⁺` became `is-absorbing⁻` and
  `is-absorbing⁺`, matching the `absorb⁻` and `absorb⁺` lemmas already
  downstream. The tier gives one-sided absorption and never a two-sided
  inverse.
- `Stability.lagda.md` became `Embedding.lagda.md`, and `is-stable`
  became `reflect-is-embedding`, with every derived name following. The
  predicate is definitionally `is-embedding reflect`. The old name
  borrowed the least related sense of the most overloaded adjective
  available.
- `is-interchanging` became `cuts-agree`, with `full-cuts-agree`,
  `judgment-cuts-agree`, and `cuts-agree→involutive` following. None of
  these states the two-categorical interchange law. All state that the
  two hands' compositions agree. `Aligned.lagda.md`'s own bare
  `interchange` theorem became `hands-agree`, kept distinct to avoid a
  scope clash.

`Aligned.lagda.md` became `Diagonal.lagda.md` in the same pass, for a
different reason. The old name stated a hypothesis the module shares
with its source tree. The new one states what distinguishes it. The
diagonal framing sets the two families equal, and that is the condition
under which the two-hand theory collapses to one category.

One correctness bug surfaced during the pass, independent of naming
philosophy. `Groupoid/Path.lagda.md` and `Group/Abelian.lagda.md` each
named its cuts for the half-twist each mediates with, inverting the rule
`Framing.lagda.md` states. Both files used the correct form elsewhere
in themselves. Both compiled, because both passed the inverted names
into the positions the types demand. Fixing `Group/Abelian.lagda.md`
also required swapping two lemmas that had baked in the inverted
correspondence.

Prose followed the identifiers over two entries. The first swept
"invertibility", "balanced", and "aligned" as descriptive words. The
second swept "stability" and "stable" across sixteen files. Local
bindings named `stable` at a model stay untouched, since they are
informal local names and not the audited identifier. Generic "half-twist" as
an ordinary descriptive word stays untouched throughout. Unlike
"stability" it imports no specific established concept the corpus fails
to earn.

---

## The negative pentagon (2026-08-05)

The pentagon held for one hand only, over `tower⁺`. The audit noted
that a reader must not assume coherence for the other. The gap closed
the same day, and not by writing the proof twice.

`Embedding.lagda.md` gained `reflect-lc-fiber`. Two representations of
one judgment name a path of edges twice, and the lemma identifies the
two routes. `tower⁺` and `tower⁻` build their associators along those
two routes respectively. That is what lets either be read as the other.

`Tower.lagda.md` gained `op-tower`, which instantiates `tower⁺` at the
opposite carrier and proves two correspondences. `op-⨾⁺` says the
opposite's positive cut is the negative cut with its factors exchanged,
definitionally. `op-assoc⁺` relates the two associators. A
positive-hand construction transports to the negative hand along those
two.

`Pentagon.lagda.md` gained `pentagon⁻`. It reads `pentagon⁺` at the
opposite carrier with the four factors reversed, rewrites each of the
five sides, and turns the identity around. The negative pentagon is the
positive theorem read through the duality, and not a second path
argument.

---

## What the tree does not carry

Three things are worth naming, so that a reader does not go looking.

The recognition line's own results are not here. Thirteen spike files
hold them. `TODO.md` lists all thirteen with the rule for importing
them. Restate the checker-verified theorems about each model, and do
not import a file's own verdict prose. The torsor correction never got
a checkable criterion.

One `Bb.NaiveVirtualGraph` row stays unvendored: the `PathGroupoid`
model.

And the concept this whole arc aimed at is not here. The shipped
construction cannot express duploidal structure, because balance is
exactly the strength at which polarity collapses. That is a proved
theorem about the definition, and not a gap in the work. This tree is a
consolidation meant to prepare a definition that does not yet exist.
That is why the naming audit treated a borrowed name as a liability
rather than a label.
