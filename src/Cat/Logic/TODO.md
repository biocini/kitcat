# Cat.Logic — open items

State as of 2026-07-28, end of the morphisms session. `src/Cat`
typechecks, 21 modules, with `Cat.Depreciated` moved to the
archive. `src/Test` typechecks, 9 modules, under the spike-zero
policy of `src/Test/CLAUDE.md`. `src/Bb` typechecks, 98 modules:
six frozen trees and the `Bb.index` aggregator, each tree with a
README and CHANGELOG per `src/Bb/CLAUDE.md`. Lint is clean at
the 100-column width. The `Mag` rebuild remains pending; its
program of record is `src/Bb/VgCategoryShape/README.md`, the
vendored staging tree.

`Cat.Logic.Gist` is new: the certified spikes on `Cat.Logic`'s
definitions, vendored out of `Test` with the `Spike` prefixes
dropped. Nine modules: `AssociatesDefect`, `BalancedBase`,
`BalancedProfile`, `BalancedWord`, `FramedInterchange`,
`ReadbackTorsor`, `ReflectFiber`, `RxDict`,
`ThunkableSquare`. Five more live only in the archive, the
retired block below. The one-twist trio is archived at
`Bb.OneTwist`: it probes the rejected rival carrier, not these
definitions.

Committed through `f12dfcd` on `master`. This session's work sits
in the working tree, uncommitted: the polarity prose corrections,
the `docs/deductive-systems/` reconciliation, and
`Test.SpikeMorphismInitial` (staged).

Prose is gated by the `writing` skill alone. Its bundled linter is
the only prose gate: a changed `docs/` file must score at or under
2.0 violations per 100 words. `bin/lint` covers width and flags, and
the skill triggers on any technical-prose creation or edit. The
skill is the normative statement and
`docs/guidelines/prose-and-comments.md` states the scope. Keep new
prose in that register. Open: whether the gate should also cover
module prose under `src/`, which the retired porcelain gate never
measured either.

## Settled: the record cut

Naming (Lane, 2026-07-28): the label `(D′)` is retired from the live
tree and from `docs/roadmap.md`. It named a position only against
the rejected `(C)` and `(D)`, so it reads as one variant among
several when it is in fact the definition. Live prose says
"deductive system", and the archived weaker notion is already marked
by the `Bb.WeakDeductiveSystem` namespace. Where the difference
needs naming, the live carrier bears readback and the archived
stratum is readback-free. This ledger keeps the letters below as a
record of the decision.

Cut 2026-07-28, adopting position (D′). `virtual-graph` carries
`readback`, stated through `reflect` at `var`/`covar`, so it is
`eval ∘ reflect ≡ id` on the nose. `is-deductive-system` is
contractible cuts plus invertibility — propositional fieldwise,
no `is-prop→PathP` step — and `stable` is gone as a field.
Theorems now, in `Cat.Logic.Base`: `axioms→stable`
(`contr-cut⁻.stable-from-contr-cut⁻`, through `composite⁻-twist`
and `image-fibers-contr→is-embedding`); `unitr⁺` and `unitl⁻`
unconditional in `tower`, from `hand⁺`/`hand⁻`; and under the two
tiers, `tower.balanced`: `centre⁻-twist⁺`, `centre⁺-twist⁻`,
`cancel⁻`, `cancel⁺`, `absorb⁻`, `absorb⁺`, `unitl⁺`, `unitr⁻` —
all four unit laws, two unital magmoids on one graph offset by
the double twist. `opⱽ` carries the readback leg unchanged and
`opⱽ-invol` stays `refl`. The `absorption` and `unital` hypothesis
modules are gone; `Display.framed` takes the two cancellations.
One inference ruling: readback never appears in the axioms'
types, so an implicit-`G` application no longer pins `G` by eta —
recovery held before only because every field of the record
occurred in the predicates' unfolded types, an inventory fact no
signature can see change. Per the no-principal-argument clause of
`docs/guidelines/elaboration.md`, the carrier is explicit in
`tower`, `coherence`, and any future signature whose hypotheses
are all predicates over it.

## Retired to the archive by the record cut

Five `Gist` modules are deleted from the live tree. Their subject
is the free-framing regime, which readback ends, and their green
form is the archive's: `Bb.WeakDeductiveSystem.Gist`, where every
`docs/` citation of the five now points. Deciding Lane's ruling
of 2026-07-28: the live tree carries no red modules.

- `AssociatesCountermodel`: the four-reader carrier has no
  readback — a constant reads back as a projection. The
  weak-stratum profile verdict lives in the archive; the balanced
  profile is `Gist.BalancedProfile`.
- `FramedCut`: its subject is a full system at every framing, and
  readback kills framing freedom — at `t⁻ = loop` it dies by
  `loop-nontrivial`.
- `FramedGroup`: the abelian group at an arbitrary framing pair;
  readback forces the pair to sum to the unit, which erases the
  spike's free-framing fan.
- `NeutralUnit`: consumes `unital`'s hypothesis interface, now
  derived; its question is answered at (D′) by `tower.balanced`.
- `TwistFidelity`: audits the `pin`/`K` hypotheses, which no
  longer exist; framing invertibility is `balanced.cancel⁻` and
  `balanced.cancel⁺`.

## Done

The rename pass is applied.

- `is-unital±` → `is-invertible±`, with `is-invertible-is-prop`,
  `op-invertible±`, and the `is-deductive-system` field renamed
  `invertible`.
- Composition register flipped: `composite±`, `inj±`,
  `is-composable±`, `contr±`, `⨾±`, `assoc±`, `unitl`/`unitr`,
  `tri±`, `collapse±`, `pentagon±`, `pair±`, `C±`,
  `push-is-composite±`. Framing register untouched.
- `mixed-leading` → `thunkable`, `mixed-trailing` → `linear`.
- Consumers fixed: `Bb/WeakDeductiveSystem/Gist/FramedGroup`, `Bb/WeakDeductiveSystem/Gist/TwistFidelity`,
  `Bb/WeakDeductiveSystem/Gist/FramedCut`, `Bb/WeakDeductiveSystem/Gist/NeutralUnit`.
- The three-register naming rule is written into `Cat.Logic.Type`,
  beside the twist fields.

Checks that landed as predicted: `mixed-assoc` is now
`(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)` — the classical-notions paper's
valid word — and
`unitr⁺ : f ⨾⁺ twist⁺ y ≡ f`, `unitl⁻ : twist⁻ x ⨾⁻ g ≡ g` now agree
with `Cat/Logic/Gist/FramedInterchange` on the nose.

Module prose in `Base`, `Display` and `Graph` has been reread and
rewritten against the new labels. `Base`'s header no longer claims the
twists are mutually inverse — it says each has a uniquely determined
one-sided inverse, and names `absorption` as where the mutual claim
lives. `push-is-composite±` in `Display` were relabelled so each matches
the composite it produces.

`docs/deductive-systems/` and `docs/gloss.md` are reconciled.
`unitality.md` is now `invertibility.md`, retitled and relinked from
`README.md` and `framing.md`. `mediation.md` needed no change: after the
swap its pending-read / pending-write sentences and both `collapse±`
hypotheses already read correctly. The two `notes/2026-07-25-*` files
are dated records, so they carry a relabelling banner rather than a
rewrite.

### Still to do from the pass

Nothing. The remaining work is the `Mag` rebuild against
`src/Bb/VgCategoryShape/README.md`, and the fresh briefing block for
the sibling agent.

## Settled this session

1. **The unit tier is misnamed.** Read through the string,
   `coact-π e ≡ snd` is `t⁻ · e · k ≡ k`, i.e. `t⁻ · e = 1`; and
   `act-π e ≡ snd` is `e · t⁺ = 1`. So the two tiers say *`twist⁻`
   has a unique right inverse* and *`twist⁺` has a unique left
   inverse* — invertibility of the framing, not unitality. The name
   is a holdover from the one-`rx` reflexive-graph formulation.
   Rename to `is-invertible⁻` / `is-invertible⁺`, record
   `is-invertible`.

2. **Form B, and position (C).** The tier stays the `snd`-target
   form. The cancellation (`pin ∙ K`, equivalently `t⁻ · t⁺ = 1`,
   equivalently "the twists are mutually inverse") is **not** a
   field of `virtual-graph` and **not** a tier — it is structure in a
   ribbon layer above the deductive system, which is where the
   literature puts a twist: a balanced category is a braided one
   *equipped with* θ. `virtual-graph` and `is-deductive-system` stay
   as they are, all-property and propositional.

3. **The handedness labels on the towers are backwards** relative to
   the duploid dictionary, and must be swapped. Names and docs only —
   the operations are unchanged and no proof moves.

4. **`mixed-leading` / `mixed-trailing` are the classical-notions
   paper's thunkable and linear** — the universal closures of the one
   failing mixed word at a fixed leading/trailing edge, which is that
   paper's definition. Align the
   naming. Note the prefix rule: neither is a proposition, so no
   `is-`. Attachment corrected 2026-07-27: the code closed them over
   the valid word. See the duploid section below.

## Settled: the handedness swap

The rename pass executed the swap, and the Done block above records
the flip. The live tree is post-swap on both sides. The
three-register note says the `⁺` hand is built from the coterm-side
coaction and carries the negative twist
(`src/Cat/Logic/Type.lagda.md:96-98`). `mixed-assoc` is stated
`(f ⨾⁻ g) ⨾⁺ k ≡ f ⨾⁻ (g ⨾⁺ k)`
(`src/Cat/Logic/Base.lagda.md:504-505`).

The docs carry no residue. In `actions.md` and `towers.md` the `⁺`
hand cuts through the implicit `twist⁻` and takes from a future.
The `⁻` hand cuts through the implicit `twist⁺` and puts into a
buffer. No `docs/deductive-systems/` file reverses that pairing
(swept 2026-07-28). Item 4 of the open questions in
`notes/2026-07-28-balanced-record-cut.md` calls the swap an
unstarted pass. This block supersedes that item.

## Docs reconciliation

Swept 2026-07-28, whole of `docs/deductive-systems/`, against the
record cut. Eleven of the twelve files were stale and are now
current: `README.md` (the carrier omitted `readback` and the diagram
drew `is-stable` as a tier), `the-package.md` (the pre-cut
three-field record, and `FramedCut` cited as the inhabitant, which
readback rules out — now `Gist.BalancedWord`), `composability.md`
(the stability-indexed record and `op-composable`), `stability.md`
(stability as a tier that "comes first"), `towers.md` (one unit law
per hand, now four), `invertibility.md` and `framing.md` (the centre
left to the framing, now `centre⁻-twist⁺` and `centre⁺-twist⁻`),
`displays.md`, `actions.md`, `graphs.md`, `mediation.md`. The
retired `pin`, `K`, `unital` and `absorption` names are gone from
`docs/` and from the register list in `Cat.Logic.Type`. All twelve
files pass the prose gate. The one surviving `pins` reference, in
`mediation.md`, correctly describes the archived `NeutralUnit`,
which does take those hypotheses.

Remaining items, none of them record-cut debt:

- **Interchange is the ultra-thin / involutive line, not the cyclic
  line.** It is `θ⊥² = id`; cyclic is `θ⊥ = id` and is strictly
  stronger. Correct wherever glossed.
- **Twist locus.** Melliès' dialogical twist is one automorphism of
  the pole, unique by Yoneda; ours is a per-object pair, i.e. the
  balanced `θₓ`/`θₓ⁻¹`. Keep the two distinct in prose; they meet
  only at the pole.
- **Twists replacing identities has no source.** Phrase per
  `docs/provenance.md` as "not aware of a prior unit-free
  formulation; searched the vendored sources", naming them.
- **Do not call the framed carrier a duploid**, nor the towers its
  subcategories. A duploid is a unital magmoid — one two-sided
  identity per object — so per-hand one-sided unitality sits strictly
  below it. The nearest duploid *phenomenon* is `ω_X`; say
  "analogous", never "corresponds".

## Settled: the one-twist virtual graph

Decided 2026-07-27, against the proposal, by countermodel. The brief
was `notes/2026-07-27-one-twist-virtual-graph.md`, since deleted
(the verdict note `notes/2026-07-27-one-twist-verdict.md` stands,
banner-noted). Its §5 caveat is
confirmed, and its §9 needs the attachment correction recorded in
the duploid section below.

The deciding lemma is refutable, so the derived twist does not
cancel on the term side. `Bb/OneTwist/Cancel.lagda.md`
extends the one-twist carrier of `Bb/OneTwist/Base.lagda.md` with
the `⁺` tier. Its model is the Klein four-group, with the reflection
twisted by a three-cycle of the non-unit elements. Every field and
both tiers are inhabited, and `no-cancel⁺` refutes
`act-π (twist⁻ x) ≡ snd`. By contractibility the cancellation is the
agreement of the `⁺` centre with the posited twist
(`cancel⁺→agree`, `agree→cancel⁺`). The agreement is also
op-involutivity at the twist field. So `no-agree` settles both
halves of the experiment. The same model shows the §5 reduction does
not transpose to the readback-free carrier:
`⨾⁻twist⁺-cancellable` holds while `no-frame⁻` refutes the frame
law.

The §11 checks, in order. More property: passes. `twist⁺` with its
`cancel⁻` becomes the centre of the `⁻` tier, which is a
proposition. No more structure: passes on counts, five sections to
four plus a propositional tier in the carrier. No truncation:
passes. `Bb/OneTwist/Models.lagda.md` runs the path groupoid
over an arbitrary type at an arbitrary `t⁻`, with no h-level
hypothesis, and the abelian group at an arbitrary element. There
`twist⁺-forced` pins the extraction to the inverse, and
`group-cancel⁺` shows a group model cannot witness the failure.
What the checks do not measure, the countermodel does: the proposal
breaks the opposite. The op moves up a level, its square posits the
`⁺` centre, and the centre is not the twist.

`virtual-graph` keeps its five fields, and position (C) stands. The
extraction trick belongs to the balanced layer. There both
cancellations are asserted anyway, and the remaining datum over a
one-twist carrier is exactly the centre-agreement path family.

## Settled: the duploid dictionary, statement-checked

A statement-level pass over the brief's §9 anchors ran 2026-07-27,
in both vendored sources. Confirmed: the valid mixed word is
Definition 1's (•◦) clause, junction for junction, with ⁻ as ◦ and
⁺ as •. The transcription reverses the order, since the source
composes applicatively and this library diagrammatically: over
`A -f→ N -g→ P -h→ B`, `(h • g) ◦ f = h • (g ◦ f)` becomes
`(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)`, which is `mixed-assoc`. A
transcription that keeps the source order reads the word backwards
and makes the two labels look inverted (re-checked 2026-07-28, after
that reading raised a false alarm against the whole suite). The
failing word is the one whose middle map runs positive to negative. Thunkable and linear close over all length-3 paths at
a fixed leading or trailing edge. A unital magmoid carries a
two-sided identity. The shift unit ω has a two-sided pointwise
inverse and is still not an isomorphism, since that notion asks
thunkable and linear of both maps. P is the Kleisli category of the
monad. The duploid of an adjunction is associative exactly when the
monad is idempotent. Idempotent is equivalent to every map
thunkable, and commutative to every map central, for strong monads.
Not found in either source: the "∗-autonomous" leg of §9's collapse
chain. Treat that leg as unchecked.

The full statement audits ran 2026-07-28, independent of this pass
(`outputs/duploids-statement-audit.md`). Both entries are cleared to
load-bearing citation (`Statements verified:` on each; `just
resources-verify` reports "audited"; see Resources below). Four of
the claims above were independently re-checked against the audit and
agree: the pre-duploid triple and its transcription (Definition 1),
`P` as the Kleisli category (Remark 11), and the idempotence
correspondence (the adjunction-duploid theorem). Three rest on this
2026-07-27 pass alone, not independently re-verified by the full
audit: the `ω` two-sided-inverse-not-isomorphism note, the
idempotent/commutative-central-for-strong-monads claim, and the
∗-autonomous leg above.

The pass found one defect in the tree, now fixed. `thunkable` and
`linear` closed over the valid word, and `stable` with the two cuts
proves that word for every triple. `mixed-assoc` is that theorem
now, in `Cat.Logic.Base`'s `tower` (the module `mixed` carries the
common judgment). The property is the failing word, named
`associates`, and the closures attach to it. `towers.md` carries
the same correction. `Test/MixedWord.lagda.md` held the proof
during the check and is deleted, since checking `Base` checks the
theorem.

The open lines from this pass are items 1 to 4 of the investigation
list below.

## Settled: the associativity profile

Decided 2026-07-27, by countermodel: `Bb/WeakDeductiveSystem/Gist/AssociatesCountermodel`,
machine-checked. The deductive-system axioms prove exactly the
pre-duploid triple — `assoc⁺`, `assoc⁻`, `mixed-assoc` — and
`associates` is independent. No correlation-space or game machinery
was needed; four elements suffice.

Two models. The projection model (constant reflection over `Bool`,
both hands projections) satisfies the towers and every field of the
readback record in `Cat/Logic/Gist/FramedInterchange`, computes
`associates f g h` to `h ≡ f`, and has no thunkable and no linear
edge. So the readback record does not derive `associates` either:
the classes bite with units present, not only in the unit-free
regime. The same model refutes the invertibility tier, which is why
the second model exists.

The four-reader model (`Bool × Bool`; an edge reads the argument as
a projection onto one flank or a constant at one projection) is a
full `is-deductive-system` in which `associates π₁ g π₂` computes to
a refutable path for every middle edge. Its classes are exactly the
tier centres: the `⁻` centre `π₂` is the one thunkable edge, and the
`⁺` centre `π₁`, which is also both twists, is the one linear edge.
So the axioms prove no twist thunkable. The model does not decide
the balanced layer — its absorption hypotheses fail there — so
whether balance forces thunkable twists stays open with line 5.

## Settled: thunkability is data

Decided 2026-07-27, by countermodel: `Cat/Logic/Gist/ThunkableSquare`,
machine-checked. The spike states the length-4 compatibility
square, `compat`, over any stable virtual graph with both cuts.
The square consumes a thunkable witness at `(g , h)` and at
`(g , h ⨾⁺ k)`. Its other three edges are `mixed-assoc` twice and
`assoc⁺` once. So it is the least coherence a choice of
associators can carry: naturality of the choice as the trailing
edge grows through the valid mixed word. Growth by `⨾⁻` gives a
pentagon with three witness instances instead. Growth at the
leading edge makes witnesses for composites, not a law. Over hom
sets the closure and the square are both propositions.

The countermodel is the circle as a one-object system: homs the
circle, reflection multiplies the edge between the flanks, both
twists at `base`. It is a full deductive system with wild homs,
and `associates base g h` computes to the loop space at
`mult g h`. `thunkable-not-prop`: the constant witness and its
`rot`-shift are provably distinct, so the axioms leave
thunkability as structure. `coherent-not-prop`: both witnesses
satisfy the square, through the `mult`-equivariance of `rot`, so
the square-refined closure is not a proposition either. No
coherence law over the same data cuts a set-level shift freedom.

The verdict on the dichotomy: the bare closure does not
self-improve to a property, and coherence does not restore it. A
fiber-shaped propositional refinement is therefore strictly
stronger than inhabitation, and the circle model separates the
two: a contractibility demand on this witness space fails there
while `thunkable` holds. So the group-like models pay for any
tier-style thunkability, and the working notion stays structure,
as polarity already is in line 4. The path groupoid was the wrong
test bed. Over any base its homs are path types, so witness
freedom sits at the second loop space of the base, out of reach
of the library's types. A hom type with its own fundamental group
reaches it, which is what the circle provides.

## Settled: the (D′) profile, at the free balanced point

Measured 2026-07-28, `Cat.Logic.Gist.BalancedWord`: the word model of
the bare framed point at (D′) strength. Normal forms are
eventual-translation descriptors, both cuts admissible functions
on them, no quotient, equality decidable, the carrier a set. The
model satisfies the live record on the nose: `virtual-graph` with
readback, the two-field predicate, stability through
`stable-from-hom-sets`.

- `associates t⁻ t⁺ t⁺` is refuted: the left bracketing
  normalizes to `t⁺`, the right to the descriptor `([1], 1)`.
  Generic `associates` is underivable at (D′). The profile is
  exactly: pre-duploid, `mixed-assoc`, the four unit laws, and
  the twist-flanked family. The gate of `Gist.BalancedProfile`
  closes on the countermodel side.
- Bound for line 3: `t⁻` is not thunkable and `t⁺` is not linear
  at the free point, so refutation kills both candidates
  outright.
- The winding conjecture holds as designed. The endo-homs carry
  a ℤ-grade, `shift`: additive over `⨾⁺`, predecessor of the sum
  over `⨾⁻`, every grade inhabited, the double twist
  `t⁺ ⨾⁻ t⁺` the `+1` generator. The obstruction to `associates`
  is one-sided invertibility on the nose:
  `(t⁺ ⨾⁻ t⁺) ⨾⁺ t⁻ ≡ t⁺` by `refl`, and the reverse composite
  is not `t⁺`.
- verified: `just check Cat.Logic.Gist.BalancedWord`, 2026-07-28,
  zero warnings, no holes, no postulates. inferred: that this
  model is the free object — certified empirically through six
  leaves (64 classes, 64 distinct descriptors, reachability
  complete; scripts and results at
  `outputs/.notes/balanced-word-model-*`), with formal
  initiality deferred to items 2 and 3 of the initial-model
  program.

## Settled: the associates defect is a framing word, per flanking edge

Measured 2026-07-29, `Cat.Logic.Gist.AssociatesDefect`, over the free
balanced word model. The 2026-07-27 independence said the two
bracketings differ. This session says how. Each bracketing
determines the other up to a twist word, and the word reads one
flanking edge alone. Sixteen placements of a correcting word
connect `L = (f ⨾⁺ g) ⨾⁻ h` and `R = f ⨾⁺ (g ⨾⁻ h)`. Eight flank
the whole word, eight sit at a seam. All are well typed at the
point, and one-sided invertibility keeps them pairwise distinct.
Exactly two survive, one per hand, each at every triple with no
failure hypothesis.

- `defect⁺`: `R ≡ w⁺ (rise f) ⨾⁺ L`, where `rise f` is the value
  of the leading edge at zero.
- `defect⁻`: `L ≡ R ⨾⁻ w⁻ (zrunW h)`, where `zrunW h` is the
  length of the zero plateau of the trailing edge.

The corrections are twist words by construction, powers of the
bicyclic defect. `w⁺ (S Z)` is the reverse bicyclic composite
`t⁻ ⨾⁺ (t⁺ ⨾⁻ t⁺)` on the nose, the recorded obstruction of the
profile block above. The defect is not a framing constant.
`no-uniform⁺` and `no-uniform⁻` refute one word for all triples.
The fourteen dead placements each fail for every `w` at one
concrete triple (`A1`-`A8`, `S1`-`S8`, legend in the spike).

Triviality is the two closures, exactly. `w⁺` is the unit at
`rise f ≡ 0`, which is thunkability of `f` (`thunkable→rise`,
`rise→thunkable`). `w⁻` is the negative unit at `zrunW h ≡ 0`,
which is linearity of `h`. So the universal closures of
`associates` attach to the leading and the trailing edge. Those
are the edges whose corrections can vanish.

Balance kills the measured defect. `shift-associates`: the two
bracketings agree in winding grade at every triple, so the whole
defect lives in the fiber the grade forgets. `shift-w⁺` and
`shift-w⁻` compute the grades of the matching units.

The grade map is the collapse in which the reverse bicyclic
composite becomes the unit, i.e. the twists cancel two-sidedly.
`bicyclic-persists` holds the word model strictly above that
collapse. The ℤ image itself satisfies `associates` at all
sampled triples, computed only
(`outputs/.notes/associates-defect-*`). The ℤ point carries no
deductive-system instance, so that claim has no kernel witness.
Net: at the free point the pre-duploid profile has a reason
rather than a bare countermodel. `associates` fails by exactly
the one-sided-invertibility residue, and the collapse that makes
the inverses two-sided erases it.

Scope. This is a theorem about the free balanced point. The
correction indices read the model's edges, so nothing here
transfers verbatim to an arbitrary deductive system. The bare
point has no generators either. The generator-bearing word model
(initial-model program, item 1 sequels) is the instrument for the
next strength. verified: `just check Cat.Logic.Gist.AssociatesDefect`,
2026-07-29, zero warnings, no holes, no postulates.

## Settled: the h-level of polarity, at two models

Measured 2026-07-29, `Cat.Logic.Gist.PolarityHLevel`, a spike under
the spike-zero policy. `positive` and `negative` transcribe the
Polarity definition of Clairambault and Munch-Maccagnoni, *Duploid
situations in concurrent games* (GaLoP XII, 2017), over the tower
(`resources/mmmm-classical-notions/article.tex:1694-1700`). An
object is positive when every edge out is linear, and negative when
every edge in is thunkable. The transcription truncates nothing. The
names drop `is-` per the prefix rule above.

This settles the h-level question in line 4 below. The RULED
note there, that mode separation is not a candidate foundation,
is a separate and narrower verdict. This block does not touch
it.

- Circle model: polarity is structure. `mult-assoc` makes every
  edge thunkable and every edge linear, so both polarities hold
  at the one object. The `rot`-shift of a witness is a second
  witness, one winding away (`positive-distinct`,
  `negative-distinct`). So neither polarity is a proposition,
  and neither witness space is contractible. The freedom of the
  thunkability block above is uniform one quantifier up.
- The freedom reaches consumers. `positive-assoc` reads the
  mixed associator of a positive-objects subcategory off the
  positivity witness. `filler-distinct`: the two witnesses fill
  one `associates` cell in two distinct ways. A subcategory of
  positive objects over this model carries its associator as a
  choice, not a law.
- Word model: polarity is a property, and the property is
  empty. Hom sets make both polarities propositions
  (`positive-is-prop`, `negative-is-prop`). A positivity
  witness yields linearity of `ε̂`. A negativity witness yields
  thunkability of `τ̂`. The profile block above refutes both,
  so the free balanced point has no positive and no negative
  object.
- Emptiness at the word model measures the free point, not the
  theory. The circle model is a full deductive system in which
  both polarities hold. No impossibility claim stands here.
- verified: `just check Cat.Logic.Gist.PolarityHLevel`, 2026-07-29,
  zero warnings, no holes, no postulates.

## Settled: polarity is a twist condition, at two strengths

Measured 2026-07-29, `Cat.Logic.Gist.PolarityTwist`, a spike under
the spike-zero policy. Both twists at an object sit under both
polarity quantifiers, so instantiation gives four forward
clauses. The spike proves the converse at two strengths and
names the one that stays open.

This settles the closure lemma in line 4 below, and it reshapes
the countermodel question: no deductive system separates the
twist condition from the polarity.

- Closure, over the bare tower: `thunkable` and `linear` close
  under both cuts (`thunkable-⨾⁺`, `thunkable-⨾⁻`, `linear-⨾⁺`,
  `linear-⨾⁻`). No unit law, no hom set, no invertibility. Two
  closures are one-sided. `linear-⨾⁺` reads only its leading
  factor, and `thunkable-⨾⁻` only its trailing factor.
- Generated carriers: `gen` says an edge is a cut word in the
  twists. Where every edge is generated, two linear twists at
  `x` make `x` positive, and two thunkable twists make it
  negative (`positive-generated`, `negative-generated`). The
  hypotheses sit at `x` alone. `gen-diag` transports them along
  the loop a derivation forces.
- Full deductive-system strength: one edge, no generation.
  `unitl⁺` with `linear-⨾⁺` turns a linear `twist⁺ x` into
  `positive x`. `unitr⁻` with `thunkable-⨾⁻` turns a thunkable
  `twist⁻ x` into `negative x` (`full.positive-of-twist⁺`,
  `full.negative-of-twist⁻`). A countermodel must therefore
  live below invertibility.
- The twists generate the word model: `gen-sem` writes every
  canonical descriptor as a cut word in `ε̂` and `τ̂`, and the
  recursion consumes weak monotonicity alone (`gen-all`). The
  two-edge check holds there vacuously. Each hypothesis pair
  fails on exactly one twist: `τ̂` is linear and `ε̂` is not,
  `ε̂` is thunkable and `τ̂` is not.
- Open: a stable and composable carrier that is neither
  invertible nor generated. A countermodel needs both twists
  linear at an object and a non-linear edge out of it, or the
  thunkable dual, on such a carrier. No impossibility claim
  stands here.
- Known duplication: `positive`/`negative` restate
  `Cat.Logic.Gist.PolarityHLevel`'s definitions rather than
  importing them, since that module is `--cubical` and this one
  is `--erased-cubical`. The natural future home is one shared
  definition beside `thunkable`/`linear` in `Cat.Logic.Base`.
- verified: `just check Cat.Logic.Gist.PolarityTwist`, 2026-07-29,
  zero warnings, no holes, no postulates.

## Settled: polarity does not split at full strength

Measured 2026-07-29, `Cat.Logic.Gist.PolarityCollapse`, a spike under
the spike-zero policy. The two twist conditions at an object are
equivalent, so `positive` and `negative` are one predicate over
every deductive system. No carrier separates them, and the
distinguishing-model search closes with the tiers.

This settles the countermodel question in the twist block above, at
full deductive-system strength. The open case there sits below
invertibility, and this block does not touch it.

- The framing is a category and one operator. `assoc⁺` with
  `unitl⁺` and `unitr⁺` makes the edges a category whose identity
  is `twist⁺`. `mixed-assoc` with `unitl⁺` rewrites every negative
  cut (`cut⁻-cross`): `f ⨾⁻ g` is `(f ⨾⁻ twist⁺) ⨾⁺ g`. So each
  polarity statement is a statement about `_⨾⁻ twist⁺`.
- One direction, `from-linear`: a linear `twist⁺ x` makes that
  operator a positive cut against `cross⁻ (twist⁺ x)`, on every
  edge into `x` (`cross⁻-into`). `pair⁻` makes the fixed edge a
  right inverse of `twist⁻ x` (`twist⁻-centre`). The operator then
  retracts the negative twist's positive cut (`retract`).
  `cross⁻-cut⁺` passes the operator through any positive cut at `x`
  (`cross⁻-left`), which is `thunkable-twist⁻`.
- The dual direction, `from-thunkable`: the same five steps
  through `twist⁻ x ⨾⁺_`, `unitl⁻`, and `pair⁺`, ending at
  `linear-twist⁺`.
- The polarities follow by the one-edge theorem of the block
  above (`positive→negative`, `negative→positive`).
  `no-positive-split` and `no-negative-split` refute a
  distinguishing model at each candidate object, `p` and `n`.
- Cross-check at the word model: `word-check` derives
  `¬ thunkable τ̂` from `linear-refuted`, and `¬ linear ε̂` from
  `thunkable-refuted`. The free balanced point's two refutations
  are one fact.
- The obstruction is a tier, not a carrier. The collapse consumes
  `mixed-assoc`, `assoc⁺`, `assoc⁻`, `unitr⁺`, `unitl⁻`, `pair⁺`,
  `pair⁻`, `unitl⁺`, and `unitr⁻`. A stratum where the polarities
  differ drops one of them: the mixed law, one hand's
  associativity, or the invertible framing.
- verified: `just check Cat.Logic.Gist.PolarityCollapse`, 2026-07-29,
  zero warnings, no holes, no postulates.

## Settled: the carrier is a category with one operator

Measured 2026-07-29, `Cat.Logic.Gist.OperatorCarrier`, a spike under the
spike-zero policy. The collapse block above rewrote every negative
cut as one positive cut after `_⨾⁻ twist⁺`. This block states the
carrier that rewriting leaves, and measures how far it reaches. The
structure of a deductive system returns in full. The axioms do not.
The carrier is now stated for the two open questions of the twist
and collapse blocks, and this block answers neither.

- The record is `presentation`: a wild category (`unit`, `_⨾_`,
  `assoc`, `unitl`, `unitr`), one endo-operator `cross` on the
  edges, a second endo-edge family `pivot`, and three laws
  (`cross-pivot`, `pivot-unitr`, `cross-cut`). No general category
  record exists elsewhere in `Cat`, so the spike inlines its own,
  per the spike convention.
- Forced, not chosen. The category is the positive cut with
  `twist⁺` for its identity. `cross-pivot` is `pair⁻`,
  `pivot-unitr` is `cut⁻-cross` against `unitr⁻`, and `cross-cut`
  is `cross⁻-cut⁺`. The backward direction consumes every field, so
  no law is idle. `pivot-forced` pins the pivot from one law of each
  family, so that family is determined up to a path. The one free
  choice is the operator's direction, and `op-cross` shows `opᴰ`
  exchanges `cross⁻` and `cross⁺` on the nose.
- The structure returns with no hypothesis. `carrier.graph` is a
  virtual graph, readback included: `reflect f γ` is the flanked
  word `(cross s ⨾ f) ⨾ k`, and readback is that word at the axiom.
  `composable⁺`, `composable⁻`, `cancel⁻` and `cancel⁺` inhabit all
  four tier fibers. `reflect-injective`, from readback alone, then
  forces each fiber's edge (`cut⁺-forced`, `cut⁻-forced`,
  `centre⁻-forced`, `centre⁺-forced`).
- The residue is an h-level, not an equation. What the four tiers
  ask beyond the presentation is `residue`: stability, plus one
  propositionality demand per invertibility fiber. Contractibility
  is then `prop-inhabited→is-contr` on the forced witnesses.
  `hom-sets→residue` discharges all three, so a presentation with
  hom sets is a full deductive system (`system`). Over wild homs the
  residue stands open. The spike neither derives it nor refutes it.
- Round trips, componentwise. Presentation side: `ob`, `hom`,
  `unit`, `pivot` and the cut return on the nose, and `cross`
  returns up to `unitr (cross f)`, since the rebuilt negative cut
  ends at the unit. Graph side: `ob`, `hom`, `twist⁺` and `twist⁻`
  return on the nose, and `reflect` returns up to `round-reflect`.
  Its proof is `reflect-word`, every reflection a flanked word, from
  `⨾⁻-is-act`, `⨾⁺-is-coact` and readback.
- The record-level identity of graphs is exactly one square,
  `readback-square`. `round-graph` and `round-system` derive both
  records from it, the axioms by `is-deductive-system-is-prop`. The
  homs are wild, so nothing here identifies the two readbacks. No
  countermodel either, and the same shape blocks the presentation's
  own law fields.
- The operator dictionary. `associates f g h` says right
  multiplication by `h` erases the defect between `cross⁻ (f ⨾⁺ g)`
  and `f ⨾⁺ cross⁻ g` (`associates→cross`, `cross→associates`).
  `thunkable f` erases that defect outright, one trailing edge at a
  time (`thunkable→cross`, `cross→thunkable`). `linear h` erases it
  by right multiplication, at every pair (`linear→cross`,
  `cross→linear`). `positive x` and `negative x` are one condition,
  `represents x`: the operator restricted to the presheaf
  `hom(-, x)` is right multiplication by a single edge.
  `represents-forced` pins that edge to `cross⁻ (twist⁺ x)`, the
  operator's value at the identity, so the representing element is
  read off the fiber over the identity.
- Where the balanced laws go. `unitl⁺` is the presentation's
  `unitl`, spent on readback, on the positive cut, on `cancel⁻`, and
  on the forcing lemmas. `unitr⁻` enters as `pivot-unitr`, and
  `cancel⁺` is its only consumer. So a stratum below balance loses
  the positive invertibility centre first.
- verified: `just check Cat.Logic.Gist.OperatorCarrier`, 2026-07-29,
  zero warnings, no holes, no postulates.

## Settled: the readback torsor stops at the presentation

Measured 2026-07-29, `Cat.Logic.Gist.ReadbackShift`, a spike under the
spike-zero policy. The carrier block above left one obligation,
`readback-square`. It named `Cat.Logic.Gist.ReadbackTorsor` as the
one instrument in the library that varies a readback over wild homs.
This block measures what that instrument reaches. It refutes nothing.
At the circle model the square holds, at both readbacks.

- The readback is free structure. `is-deductive-system` names
  `reflect` and the two twists, and never the readback. So
  `retune-axioms` carries every tier's witness across a change of
  readback, with no proof. `retune` then gives two deductive systems
  over the circle model that differ in the readback alone, `rb₀` and
  its one-winding shift `rb₁` (`readbacks-differ`).
- The presentation does not follow. Six components return on the nose
  (`same-ob`, `same-hom`, `same-unit`, `same-pivot`, `same-cut`,
  `same-cross`). `assoc` returns up to a path, since stability carries
  it into a fiber that is a set (`same-assoc`). `cross-pivot` and
  `unitr` each gain one winding and do not return
  (`cross-pivot-differs`, `unitr-field-differs`). The carrier returns
  on the nose, so no identification of the two presentations holds the
  carrier fixed. The torsor produces no refuting pair.
- Every word the round trip writes at the axiom is a loop at `base`.
  Both twists sit there and both cuts are the multiplication. That
  loop space is commutative: every self-path family is central, and
  `conj` writes each loop as one such family. The bookkeeping is then
  a signed count of readback occurrences. Each unit word gains one
  winding, the flanked word loses one, and the stability associators
  do not move (`mixed-same`).
- The two sides of the square move together. The derived readback
  gains `κ₀ ∙ loop ∙ loop` (`derived-shift`). The reflection square
  against the field gains the same (`round-shift`). `κ₀` is the shift
  of the positive hand's left unit law, which cancels, so the spike
  names it and does not compute it. The square therefore transfers
  both ways (`square→`, `square←`). A wild readback's winding is
  invisible to it.
- The square holds at the circle model. At the axiom the two unit
  laws reduce to the two cut witnesses, and the flanked word to their
  joint inverse. What is left is the triviality of the mixed
  associator (`square→mixed`, `mixed→square`). That associator is
  `refl` (`mixed-base`), because the model reads the positive cut
  witness through `mult-assoc base`. `square₀` and `square₁` follow,
  and `round-graph` closes the graph round trip at each readback
  (`graph-returns₀`, `graph-returns₁`).
- No truncation enters. The circle is a groupoid and not a set, so the
  square at an edge is a proposition and not a triviality. What the
  argument spends is the commutative loop space and the degeneracy of
  `mult-assoc` at `base`. Both are facts about this model.
- Open: `readback-square` in general, and with it `round-system` for a
  presentation without hom sets. A proof needs the same cancellation
  without a commutative loop space, and without a cut witness that
  degenerates at the axiom. No impossibility claim stands here.
- verified: `just check Cat.Logic.Gist.ReadbackShift`, 2026-07-29, zero
  warnings, no holes, no postulates.

## Stale in light of the polarity collapse

The three polarity gists above settle more than their own headline
claims. Read together, they close a specific hoped-for route through
lines 6 and 7 below, and change what "define the subcategories" in
line 4 can mean. This block names which investigation items that
touches, and why. Nothing here is a new measurement; it draws the
consequences of the settled blocks above.

**The chain.** `Cat.Logic.Gist.PolarityCollapse` proves `positive x ⟺
negative x` at every object of every full deductive system — full
strength meaning stable, both composability tiers, and both
invertibility fibers, which is balanced strength (`tower.balanced`,
the record-cut section above). No deductive system has an object that
is positive and not negative, or negative and not positive.
`Cat.Logic.Gist.PolarityTwist`'s open case — a carrier that is stable
and composable but not invertible — is the only place this could
still fail, and nothing here touches it.

**Item 4's "subcategories" residue.** That line asked to "define the
subcategories of thunkable maps, linear maps, positive objects and
negative objects over the towers." At balanced strength that plan now
has an answer before it is attempted: the positive-object subcategory
and the negative-object subcategory, if built as object classes, are
the same class of objects in every deductive system. A carrier can
have positive-and-negative objects (the circle) or neither (the free
balanced point), never one without the other. This is not "still
open" in the sense the line originally meant — it is closed,
negatively, at balanced strength. Below invertibility it is genuinely
open, per the twist block's own unresolved case.

**Item 6, shifts as representability.** BLOCKED. The line's own text
already named the dependency: "Needs line 4 for `linear` to have
content." At balanced strength, `linear` at an object's defining
twist never has content independent of `thunkable` at the same
twist — one is exactly the other, by the collapse. A shift's
universal property meant to say something about positive objects that
is not already true of negative ones cannot be stated non-vacuously
against object-level polarity in the current framework. The route to
this line, as written, is closed by a proved theorem, not by absence
of effort.

**Item 7, the reflection theorem.** BLOCKED, and this is the
load-bearing one. The target was "the polarized, balanced core of a
deductive system is a duploid." Balanced is exactly the strength at
which polarized collapses. There is no polarized-and-balanced core to
extract a duploid from: any object balanced enough to be usefully
positive is, in the same breath, negative. A duploid needs P and N to
differ. This framework's balance and this framework's polarity cannot
both hold non-trivially at the same object. The reflection theorem as
targeted has no carrier to land on.

**What this does not touch.** Items 1, 2, 3, 8, and 9 are unaffected —
none of them depend on polarity separating objects. Item 5's own text
already named the shape of this outcome ("turns the comparison table
there into a depolarization theorem") without having the theorem; the
collapse is arguably that theorem, reached by a different road (twist
equivalence, not the θ² magmoid merge). Cross-reference, don't
conflate: item 5's depolarization is the two hands' units merging
under θ²; the collapse is `linear`/`thunkable` merging at a twist.
Whether they are the same fact under two descriptions is not
established here.

**The decision this reopens.** Item 4's RULED note (Lane, 2026-07-28)
rejected primitive polarity as a foundation on the strength of one
clause: "Modes return, if at all, as a derived presentation of the
balanced core through lines 6 and 7." That clause is now false for
the balanced core as defined. It does not follow that primitive
polarity is right — only that the alternative the ruling bet on has
failed the way a ruling can fail: by a proved theorem rather than a
stalled attempt. Munch-Maccagnoni's own Definition 1 states polarity
as primitive data, a partition map `ϖ : |D| → {+, ⊖}`, not derived —
worth weighing now that the derived route is closed. Reopening the
ruling is Lane's call, not this block's; recorded here so the next
session does not re-derive the collapse before finding out it already
answers the question the ruling deferred.

## Lines of investigation: toward higher duploids

Enumerated 2026-07-27, from the duploid comparison. Each line names
its question and a first move. Lines 4 to 7 are ordered: each needs
the ones before it.

1. **Bound the associativity profile.** SETTLED 2026-07-27: the
   profile is exactly pre-duploid, at full deductive-system
   strength. See the settled section above and
   `Bb/WeakDeductiveSystem/Gist/AssociatesCountermodel`.

2. **Thunkability: property or data.** SETTLED 2026-07-27: data,
   and the square does not truncate it. See the settled section
   above and `Cat/Logic/Gist/ThunkableSquare`. What remains is
   narrower: whether the square holds for every witness in every
   deductive system. The circle model validates rather than
   refutes it, since its witness freedom is set-level and uniform
   shifts are natural. A refutation needs a hom type with
   nontrivial parallel 2-cells, which the library does not
   currently provide. The syntactic half of the residue, whether
   propositionality returns on initial models, is line 9.

3. **Inhabitants.** Narrowed 2026-07-27 by the countermodel. The
   readback question is answered: the record does not derive
   `associates`. The twists are dead as candidates — the
   four-reader model's twists are linear and not thunkable. Live
   candidates: the tier centres, `centre⁻` thunkable and `centre⁺`
   linear, which the model supports and nothing yet proves. A proof
   cannot go through judgment identity — the two bracketings still
   represent distinct judgments at a centre — so it needs either
   the balanced layer or a new mechanism, and a refuting model
   would need tiers with a non-thunkable centre. No positive
   inhabitant theorem exists yet. The word model of line 9 is the
   cheapest executioner: refutation there kills a candidate
   outright, and derivability questions become computations.
   Executed 2026-07-28: the word model refutes thunkability of
   `t⁻` and linearity of `t⁺` (the settled profile block above),
   so the inhabitant question reduces to the unit-law fragment.

4. **Polarity in the wild setting.** The classical-notions paper's
   definitions are stateable verbatim: positive when every map out is linear,
   negative when every map in is thunkable. Neither is a
   proposition here, so polarity is structure until refined or
   truncated. Decide its status, then define the subcategories of
   thunkable maps, linear maps, positive objects and negative
   objects over the towers. Closure of thunkable and linear under
   the compositions is the first lemma, with a portable template:
   the closure proofs in the origin mechanization consume no unit
   laws and no hom sets. RULED (Lane, 2026-07-28): mode separation
   is not a candidate foundation. It cannot be stated below
   unitality, and the origin mechanization is itself one-carrier,
   with adjunctions only as what the structure theorem
   reconstructs. Modes return, if at all, as a derived
   presentation of the balanced core through lines 6 and 7.
   Settled 2026-07-29, the h-level half: polarity is structure
   at the circle model and an empty property at the word model.
   See the settled block above and `Cat.Logic.Gist.PolarityHLevel`.
   Settled 2026-07-29, the closure lemma and the twist
   reduction: `thunkable` and `linear` close under both cuts
   over the bare tower, and polarity reduces to its twists on
   generated carriers, from one twist at full deductive-system
   strength. See the twist-condition block above and
   `Cat.Logic.Gist.PolarityTwist`. Settled 2026-07-29, the polarity
   split: the two twist conditions at an object are equivalent, so
   the two polarities are one predicate and no deductive system
   separates them. See the collapse block above and
   `Cat.Logic.Gist.PolarityCollapse`. The subcategories do not stay
   open in the sense first meant here — see "Stale in light of the
   polarity collapse," above this list, for what closes and what
   does not. The twist reduction below invertibility on
   non-generated carriers is the one piece that is still genuinely
   open.

5. **The fully balanced layer.** Not blocked — its own content (the
   unit laws, largely proved by the record cut above; the `Mag`
   comparison) stands on its own. Its role as a stepping stone toward
   lines 6 and 7 is diminished, since those are now blocked — see
   "Stale in light of the polarity collapse," above this list. Its
   own "depolarization theorem" phrase, below, named the shape of
   that outcome before this session had the theorem, and is worth
   reading against it. String computation, unverified:
   with both cancellation orders, each hand is two-sided unital
   with its own twist as unit. That is two unital magmoids on one
   graph, offset by θ². State the layer, check the four unit laws,
   and compare with `absorption`. This is where the duploid
   identity apparatus should reappear. First consumer: the `Mag`
   re-founding program in `src/Bb/VgCategoryShape/README.md`, which reads
   `hcategory` as the θ² = id merge of the two magmoids and turns
   the comparison table there into a depolarization theorem.

   Readback is independent of the deductive-system axioms, so no
   derivation search is worth a session: `Bb.WeakDeductiveSystem.Gist.FramedCut`
   gives a full system at every framing, and at `t⁻ = loop`,
   `t⁺ = refl` over the circle, readback at `refl` dies by
   `loop-nontrivial`. The centres, by contrast, carry their
   one-sided absorption from the tiers, so the layer is exactly
   the agreement family: the twists are the centres.

   The layer's structural cost is bounded, and the bound should
   be pushed down before the layer is packaged. Upper bound,
   machine-checked: one self-dual field, `readback` in
   `Cat.Logic.Gist.FramedInterchange`, with op keeping the field
   on the nose. Over a deductive system its marginal purchase is
   the unit laws and the twist pairings only: `mixed-assoc` and
   stability are theorems of the bare tower already, and the
   readback record only rederives them because its own axiom
   base lacks the stability tier. Candidate compression, one loop per object
   instead of a path per edge: `cancels` in
   `Bb.WeakDeductiveSystem.Gist.FramedCut`, with naturality derived from
   stability rather than posited, in the way stability already
   manufactures associativity. First moves: attempt that
   derivation over the tower, mixed-σ style, and run the
   nonabelian group model at `t⁻ = g`, `t⁺ = g⁻¹` as the expected
   countermodel, since per-object cancellation holds there while
   conjugation fixes only central edges. If the countermodel
   kills the derivation, the residue is exactly a naturality
   clause, and the question becomes whether it has a fiber shape.
   No impossibility claim stands anywhere here: propositional
   shapes are exhausted only as far as spiked, which is the
   lesson of the interchange precedent in
   `src/Bb/VgCategoryShape/README.md`.

   The propositional form of balance,
   `is-contr (Σ readback-data , filler)`, is refutable on
   motivating models, not merely on instruments. Over the circle
   model the coherent readbacks are a torsor over the centre: the
   `rot` family shifts any readback edgewise by winding, and
   fillers stated in the doctrine's language are expected
   centre-equivariant by the uniform-shift mechanism of
   `Cat.Logic.Gist.ThunkableSquare`, so the total space keeps ℤ
   components at every coherence depth. The classical shadow is
   the non-uniqueness of ribbon structure, super vector spaces
   carrying two. So a contractible form defines uniquely-balanced
   systems, a strictly smaller class that excludes the phase
   fragment the program studies. Spike to pin it: two coherent
   readbacks on the circle model, machinery on the shelf. The
   framing-existentialized variant fails one level down, the
   integers model giving centre-many balanced framings. Both
   verdicts say the same thing: the balance moduli is content,
   so balance enters any definition as structure.

   Position (D), reopened (Lane, 2026-07-28): balance as base,
   readback a structure field beside the framing, the record
   carrying the choice the moduli shows is real. Placement, per
   Lane: the field goes into `virtual-graph`, never into
   `is-deductive-system`, so the axioms stay all-property and
   propositional and the ledger keeps its shape. At that level
   the field is plausibly op-invariant on the nose, since `opⱽ`
   swaps the twists and the opposite's `var` is `covar`, the
   `Mag` observation verbatim, so `opⱽ-invol` may stay `refl`
   with the field aboard. RULED (Lane, 2026-07-28) regardless:
   strict op-involution is not required, involution up to a path
   of deductive systems is acceptable, so the mechanical gate is
   gone either way.

   The semantic reading (Lane, 2026-07-28): readback is the
   correctness equation of normalization-by-evaluation, stated
   unit-free. `reflect` evaluates an edge into the judgment
   domain, `eval` reifies at the axiom, the framed generic
   environment, and readback says reification retracts
   evaluation: representing any element at the axiom produces
   the element. Below balance the transmission `eval ∘ reflect`
   is the double twist, so readback's failure measures the
   framing anomaly. Two checks this adds to the (D) rehearsal:
   whether `Mag`'s stability-from-readback derivation transplants
   to two twists, in which case `stable` demotes from tier to
   theorem and the predicate shrinks; and the alignment with
   line 9, where the coherence theorem is an NbE construction
   and `Gn.equal` of roadmap project 5 is evaluate-then-reify,
   so a readback-bearing record states its own normalization
   correctness. Remaining gates are mathematical
   only. The tower theorems survive verbatim, since `tower` is
   parameterized by the tiers and not the record. The four-reader
   and Klein instruments die, so the associativity profile and
   the one-twist verdict need balanced-strength witnesses,
   restated or reopened; the circle model cannot serve, since
   every edge there is thunkable. No motivating model is lost:
   the circle, the cancelling group models, the cancelling
   path-groupoid framings, and the ribbon targets all carry
   readback. Melliès treats balance as fundamental. Position (C)
   stands only until the (D) port is attempted.

   Spiked 2026-07-28: the propositional form of balance is buried,
   `Cat.Logic.Gist.ReadbackTorsor`. `torsor : ∀ F → F rb₀ → F rb₁ →
   is-contr (Σ readback F) → ⊥`. A filler now dies on two witnesses.

   Rehearsed 2026-07-28, `Cat.Logic.Gist.BalancedBase`: `bgraph` is
   `virtual-graph` plus a readback field. (1) landed — `opᴮ` reuses
   the readback term and `opᴮ-invol` is `refl`, so the strict
   involution survives (D). (2) BLOCKED from readback alone (wrong
   head: readback fixes reflect at the reflected edge's axiom
   environment only); with a cut, `⨾⁻-is-act` and `⨾⁺-is-coact`
   land and reduce each hypothesis to its residue — `K⁻`/`K⁺` to
   the hand's missing unit law at its own twist, `pin⁻`/`pin⁺` to
   the two crossed pairings — all four unproved. (3) landed without
   absorption or stability: `unitr⁺` and `unitl⁻` from readback
   plus that hand's cut, the tower's statements verbatim.
   (4) reduced to its price: `composite⁻-twist` is a theorem (the
   cut's witness against `unitl⁻`, no absorption spent), and
   `stable-from-contr-cut⁻` closes stability through Core's
   `image-fibers-contr→is-embedding` once one cut's fiber arrives
   contractible — the one datum existence-only `is-composable⁻`
   lacks. Verdict: (D) keeps the strict involution, and the
   predicate shrinks iff the cut field is stated contractible;
   with existence-only cuts `stable` stays a tier.

   Addendum, position (D′), named 2026-07-28 from that verdict:
   `virtual-graph` plus readback, predicate = contractible cuts
   plus invertibility, `stable` a theorem. Over any stable system
   an inhabited representability fiber is contractible, so
   existence-only and contractible cuts agree on every intended
   model: the choice is which is primitive. (D′) is flatter than
   the current predicate, since contractible cuts are
   propositional outright and the stability-indexed
   `is-composable` record with its `is-prop→PathP` step
   disappears. The NbE reading favors it: a contractible
   representability fiber says the judgment has a unique
   representative, normalization with uniqueness. And (D′) is
   `hcategory` with two twists — contractible cuts, readback,
   stability-as-theorem — so the `Mag` re-founding and the (D)
   port meet at one record family, `hcategory` its θ²-collapsed
   one-twist instance. Ruling still waits on the profile
   re-litigation, whose prompt stands.

   Gated 2026-07-28, `Cat.Logic.Gist.BalancedProfile`, the last gate on
   (D′). The derivation direction lands beyond expectation: at
   (D′) strength each tier centre reads back as the other twist,
   so both cancellations are theorems, all four unit laws hold
   (`unitl⁺` and `unitr⁻` are the new pair; this item's string
   computation is now machine-checked), and `associates f t⁺ t⁻`
   holds for every `f`. Interchange stays out: the two units are
   offset by θ². Carriers: (1) projection plus a reading point —
   readback and both tiers land, `no-cut⁻` refutes the negative
   cut, the composite of a constant against the twist being a
   mixed reader the carrier lacks; (2) the four readers
   reindexed, twists at the two projections — readback, tiers,
   centres the other twists on the nose, `no-cut⁺` refutes the
   positive cut at `π₂ ⨾⁺ π₁`, constant at a projection. Verdict:
   open after two carriers: obstructions — readback pins every
   constant reader to its own value while the mixed composites
   manufacture readers constant at a projection; the units reach
   only twist-flanked words, so neither a countermodel nor a
   general derivation exists yet.
   The (C) versus (D′) matrix as the evidence leaves it. Strict
   op-involution: both, `opᴰ-invol` and `opᴮ-invol` both refl.
   Predicate: (C) carries the stability tier and the indexed
   `is-composable` with its `is-prop→PathP` step; (D′) is flat —
   contractible cuts plus tiers, `stable` a theorem. Balance:
   (C) posits absorption as four hypotheses; (D′) proves the
   cancellations and all four unit laws. Profile: (C) exactly
   pre-duploid, machine-checked; (D′) adds the twist-flanked
   `associates` family, the general instance open both ways —
   and its countermodel supply is thin, since finite reader
   carriers cannot close a cut under readback. Closed 2026-07-28:
   the free balanced word model supplies the countermodel. See
   the settled profile block.

6. **Shifts as representability.** BLOCKED — see "Stale in light of
   the polarity collapse," above this list. The positive shift's
   universal property is a unique linear factorization through a
   thunkable `ω`. State it as a fiber condition in the house style.
   Needs line 4 for `linear` to have content, and at balanced
   strength `linear` at a twist has no content independent of
   `thunkable` there. Reopens only if line 4's ruling is revisited or
   the target is restated below invertibility.

7. **The reflection theorem.** BLOCKED — see "Stale in light of the
   polarity collapse," above this list. The target that makes the
   comparison a theorem: the polarized, balanced core of a
   deductive system is a duploid, and the correspondence extends
   the adjunction characterization. Its expected home is the
   notion the two source literatures imply and do not define, a
   balanced duploid, with plain duploids as the trivially framed,
   polarized, set-level case. At this framework's balanced strength
   there is no polarized-and-balanced core: balance is exactly what
   collapses polarity. The theorem has no carrier to land on as
   targeted.

8. **Prior art on one-sided unitality.** Neither vendored source
   mentions skew structures. Run a literature pass on
   skew-monoidal and adjacent one-sided-unital settings before any
   novelty claim for the framed carrier.

9. **The initial-model program.** Enumerated 2026-07-27, from the
   thunkability verdict. `thunkable-is-prop` in
   `Cat.Logic.Gist.ThunkableSquare` already gives propositionality
   over hom sets, so the syntactic question reduces to one
   coherence conjecture: the free deductive system on a set-level
   signature has hom sets. The full brief is the initial-model
   section below. Next session starts here. The open profile
   question of the (D′) gate transfers here: the free balanced
   word model — item 1 at (D′) strength — is now the profile
   oracle.

## The initial-model program

Planned 2026-07-27, for the next session. The question: does
propositionality return on the initial objects of the theory? It
factors. Hom sets make `thunkable` a property in any system
(`thunkable-is-prop`, machine-checked in `Gist.ThunkableSquare`).
So the whole open content is the coherence conjecture: the free
deductive system on a set-level signature has hom sets.

Two structural constraints pin the construction.

- No set-quotient can be the free object. Set-quotient recursion
  eliminates into sets only, and the universal property must hold
  against wild targets, the circle model among them. The free
  system is an untruncated HIT, and hom-set-ness can only be a
  theorem about it, never a definition.
- Every identification the theory forces is fiber-internal. The
  HIT's path constructors make `reflect`'s fibers propositional,
  and forced edge equalities are `ap fst` of paths in those
  fibers. Props are sets, so fiber-internal identifications
  cohere, which is the `pentagon⁺` mechanism. Proof strategy for
  the conjecture: every derivable identification factors through
  propositional fibers. The refutation shape is equally real: if
  the two hands manufacture a loop from set generators, then
  thunkability is data even syntactically, and wildness is not
  conservative over syntax. Either outcome is a theorem.

The work items, in order.

1. EXECUTED 2026-07-28 as `Cat.Logic.Gist.BalancedWord`, results in
   the settled profile block. The spec that ran, kept for the
   generator-bearing sequels: the word model of the framed
   point, as a spike. Generating
   data (Lane, 2026-07-28): the bare framed point first, the
   smallest oracle, with generator-bearing versions after the
   point is understood. At (D′) the centres are not generators:
   each tier centre reads back as the other twist. An inductive
   type of normal words in `t⁻`, `t⁺` under the two cuts. The
   rewriting is post-cut: `assoc⁺`, `assoc⁻`, `mixed-assoc`, and
   the four unit laws, each hand two-sided unital at its own
   twist. Readback is the transmission relation. `reflect f` at
   an argument is the flanked word `a ⨾⁻ f ⨾⁺ b`, one judgment
   by `mixed-assoc`, and the field's equation is flanking at the
   axiom, which `unitl⁻` then `unitr⁺` discharge. Decidable
   equality, then the deductive-system axioms, all set-level on
   `--erased-cubical`. Construction: cut-free. Define the normal
   forms as the inductive type and both cuts as admissible
   functions on them. No quotient, so no confluence obligation,
   and item 3's coherence theorem becomes cut admissibility. See
   the internal-language seam, line 1. Decidable equality makes
   the free point the (D′) profile oracle: `associates` at
   generic words is a computation. The closing measurement is
   the winding conjecture: the endo-homs of the free balanced
   point are ℤ-graded, and the surviving grade is the double
   twist. Payoff immediately: a derivability bound for line 3.
   Refutation in the word model kills a candidate outright.
   Inhabitation is evidence only, until item 3 upgrades it.
2. Morphisms. Started 2026-07-28, half landed.
   `Test.SpikeMorphismInitial` carries the statement level, with
   its own inlined carrier per the spike convention: `_⇒_` with
   `map`, `hmap`, `pres-twist⁺`, `pres-twist⁻`, `pres-reflect`,
   then `is-initial G = ∀ G' → is-contr (G ⇒ G')` and
   `is-initial-is-prop`.

   Three verdicts, machine-checked. Initiality truncates no hom: it
   asks contractibility of one type, not an h-level of the theory's
   homs. It is satisfiable, `empty-is-initial`. It is not vacuous:
   the codiscrete graph on two points restates the four axiom
   leaves (`contr⁺`, `contr⁻`, `fiber⁻`, `fiber⁺`) and has two
   distinct self-maps, so `codisc-hom-not-contr` and
   `codisc-not-initial`. No axiom of the theory makes system maps a
   proposition, so contractibility can only be a fact about a
   particular source.

   Reviewed 2026-07-28, adversarially, `reviewer` at xhigh. The
   record is at `outputs/.drafts/system-morphisms-review.md`. The
   kernel evidence is sound and the inlined carrier does not drift.
   Six findings, and two of them are false statements rather than
   gaps. Fix both before the spike leaves `Test/`.

   - FATAL. `is-initial` binds its target at the *source's* levels,
     `(G' : virtual-graph o h)`, while `_⇒_` is polymorphic in all
     four. The prose says "every target" and means it. The damage
     is asymmetric: `empty-is-initial` is weakened to level-zero
     targets, for nothing, since its proof is level-generic;
     `codisc-not-initial` is unharmed, since refuting the smaller
     statement refutes the larger. `Typeω` is available
     (`Core.Type`), so the unrestricted form is statable. Decide
     the level policy, then make the prose match the quantifier.
   - The spike's own open question is false as posed. A higher
     mapping type does *not* need a target hom with a loop. Put
     `Circle` in the object slot of the `codisc` pattern, keep
     `hom _ _ = ⊤`: no target hom carries a loop, and yet the
     mapping type reduces to `Bool → Circle`, which is not a set.
     `winding` and `winding-loopⁿ` in `HData.Circle.Properties`
     separate the two paths. Roughly twenty lines on a `--cubical`
     variant, and the machinery is already on the shelf.
   - No result exercises `pres-twist⁺`, `pres-twist⁻` or
     `pres-reflect`. `empty` discharges them by absurd pattern and
     `codisc` by `refl` into `⊤`. Every theorem survives deleting
     all three fields, so nothing here is evidence about the record
     itself. A probe needs a target with non-contractible homs.
   - `_⇒_` constrains no readback. Over untruncated homs that
     square is real content, not a consequence: `ap hmap` of the
     source readback and the target readback give two paths with
     the same endpoints, and nothing identifies them. So the record
     is *lax*. That may be right, and the choice is undisclosed.
     Settle it when `Cat.Logic.Morphism` is written, together with
     the reviewer's question of whether a morphism should preserve
     `var` and `covar` on the nose, which would make
     `argument-map (var x , covar y)` reduce and simplify the
     square.
   - "Carries the full deductive-system axioms" is an eyeball
     claim. The spike imports no `Cat.Logic` module, so the kernel
     confirms no part of it, and the inlined carrier can never be
     fed to the live predicate. A conversion plus one term of type
     `is-deductive-system` would make it checked and would double
     as a drift alarm on every inlined copy.
   - Minor: the closing conclusion is about propositionality while
     the theorem refutes contractibility, which is stronger, so
     state `¬ is-prop (codisc ⇒ codisc)`; the `is-composable`
     analogy overstates a shared mechanism where only "no h-level
     on homs" is shared; `Core.Data.Bool.Properties` already has
     the Bool disequality the spike re-derives; and the top-level
     `open _⇒_` publishes `map` and `hmap`, which collide on
     promotion.

   Remaining, and the next session starts here. The live module,
   `Cat.Logic.Morphism`: the same record with every
   implicit/explicit call settled by the probes of
   `docs/guidelines/elaboration.md`, which have not been run; the
   derived `pres-var`, `pres-covar`, `pres-act`, `pres-coact`;
   identity and composition; and the composition-preservation
   theorem `pres-⨾⁺`/`pres-⨾⁻`. That last one has a price.
   `f ⨾⁺ g` is a fiber centre, so passing from equal reflections to
   equal edges needs `reflect-lc`, hence the target's stability,
   hence a deductive system on the target rather than a bare graph
   map. State that hypothesis rather than weakening the theorem.
   The brief is `outputs/.plans/system-morphisms-T1.md`, its shared
   context and style divergences `outputs/.plans/system-morphisms.md`.
   On promotion the spike becomes `Cat.Logic.Gist.MorphismInitial`
   under the spike-zero policy, and its inlined carrier retires in
   favour of the live record.

   Open from the spike: whether a mapping type is ever
   non-trivially higher, two maps equal in more than one way. The
   answer is close, and the earlier statement of this question here
   was wrong. Loops in the target's *homs* are not what it takes. A
   target with `Circle` for objects and `⊤` for every hom already
   makes the mapping type `Bool → Circle`, which is not a set.
   Build it and the question closes. Whether the free system
   attains contractibility against every wild target is item 3.
3. The free system as an untruncated HIT, its initiality, and the
   coherence theorem: free equivalent to the word model. This is
   where the conjecture is decided.

Decided (Lane, 2026-07-28): the point theory is stated over the
bare framed graph first, the smallest oracle. Generator-bearing
free framings follow once the point is understood. At (D′) the
centres carry no separate laws, since each tier centre reads
back as the other twist.

Anchors. Roadmap project 5 already wants `Gₙ` with `Gn.equal`
deciding free hom-equality, and project 2 names the S¹ no-UIP
model, so the program lands on committed ground. Führmann's
thunkable-equals-value characterization and the duploid sources'
syntactic models are CONJECTURED anchors only: Führmann is not on
the shelf, the two vendored sources are unaudited, and all build
syntax at set level by fiat, which the wild setting cannot.

## The internal-language seam: CatColab RFC 0004

Enumerated 2026-07-28, from one fetch of
<https://next.catcolab.org/rfc/0004>, "Internal languages for
models", Evan Patterson, 2026-04-10. SOURCE-CHECKED at that depth
only. The document is not vendored, so nothing below supports a
citation. Vendoring and a statement audit come before any of this
reaches code, docs, or the ledger.

The proposal, as fetched. A two-level type theory parameterized
by a modal double theory. The outer theory speaks of models, the
inner theory of morphisms, through judgment forms that carry a
domain term and a codomain term. Composition in the inner theory
is admissible, not primitive, so cut-freeness enforces canonical
forms. Doctrines are virtual double categories under an "almost
representable" condition. Models are Set-valued. The apparatus
assumes the doctrine is flat, at most one cell per boundary, on
the ground that pointful notation has no syntax for cells. Its
future work opens with coherence theorems that prove flatness for
finite presentations.

The relation to this framework, in two sentences. The kinship is
structural: composition as a property-witnessed representative,
representability as the organizing notion, and a judgment form
that is the one-sided shadow of `judgment x y`. The divergence is
the truncation policy: flatness plus Set-valued models is the
hom-set regime, where `thunkable-is-prop` makes the thunkability
question a proposition by fiat, while the circle model holds
ℤ-many coherent witnesses on one boundary that such a language
cannot name.

The lines of inquiry.

1. **Cut-freeness as the word-model construction.** Adopted into
   the initial-model program, item 1: normal forms as an
   inductive type, both cuts admissible, no quotient. The
   coherence conjecture becomes a cut-admissibility theorem. No
   further reading needed, the discipline stands on its own.
2. **The polarity fork.** RULED (Lane, 2026-07-28): resolved
   against the modes, see line 4 of the investigation list. What
   survives of this line: when the RFC's adjoint-logic extension
   lands, compare it with the derived presentation lines 6 and 7
   reconstruct, as an external check, not as a foundation
   question.
3. **Expressibility of the framed carrier.** Can a pre-duploid,
   or a deductive system, be presented as a modal double theory
   at all? Virtual double categories paste multicells
   associatively, and the carrier sits below that floor: the
   provable profile is exactly pre-duploid
   (`Gist.AssociatesCountermodel`). First move, after vendoring:
   a statement-level pass over the RFC's definitions to locate
   where pasting associativity enters, and whether the "almost
   representable" weakening leaves room below it.
4. **Syntactic indiscernibility.** The RFC justifies flatness
   because pointful terms cannot name cells. Read against wild
   models, that suggests a theorem: no internal language of this
   kind separates the circle model's coherent witnesses, so
   pointful syntax is complete only for the set truncation. State
   it precisely once morphisms of systems exist, initial-model
   program item 2, since "a language" then means a map out of a
   free system. This is the external face of the coherence
   conjecture, and the RFC's flatness future-work item is the
   same theorem one level down.
5. **The framed variable rule.** The RFC's identity rule is a
   fresh, unframed variable. Here `var x = (x , twist⁻ x)`: a
   variable arrives with a pending read, and a covariable with a
   pending write. For effectful doctrines, the RFC's Markov and
   promonad examples, the framed rule may be the honest one.
   Export direction, low priority, a note for any future contact
   with that community rather than a work item here. The
   algebraic-effects anchor (Lane, 2026-07-28): Kiselyov's
   "Having an Effect" page, reconstructing Cartwright and
   Felleisen's Extensible Denotational Language Specifications.
   Its slogans map clause for clause, SOURCE-CHECKED at fetch
   depth: an effect is an interaction with the context;
   dereferencing a variable is also an effect, `ReqVar` sent to
   a handler, which is `var` as the pending read; the meaning of
   a phrase is a computation that may request from its
   environment, which is `reflect` as denotation into
   interactions. Their driving problem is stable denotations,
   and `is-stable` is a stable-denotation condition: the
   judgment determines the edge. See the Resources entry.

## Resources

- `resources/munch-maccagnoni-duploids/` — vendored 2026-07-27,
  committed at `0cf05bf`, hash verified. Statement-audited 2026-07-28:
  24/24 CONFIRMED, digest-level (`Statements verified:` on the entry;
  full report `outputs/duploids-statement-audit.md`). Supports
  load-bearing citation. Not yet Lane-vetted (no `Vetted:` line — `just
  resources-verify` reports "audited — load-bearing capable; Lane
  discretion open"). The duploid dictionary above leans on it.
  `src/Cat/Logic/gloss.md` T35 cites the pre-duploid identification
  against it.
- `resources/mmmm-classical-notions/` — vendored 2026-07-24. Statement-
  audited 2026-07-28: 7/7 CONFIRMED, digest-level, same report and same
  standing as above. The duploid dictionary above cross-checks its
  transcription of the pre-duploid triple against it too.
- `resources/kiselyov-having-effect/` — vendored 2026-07-28,
  hash-verified, PROVISIONAL with no statement audit, so it
  supports no load-bearing citation yet. The internal-language
  seam, line 5, records the mapping: variables as `ReqVar`
  requests, `var` as the pending read, `is-stable` as a
  stable-denotation condition. The frontmatter uses
  `format: html`, admitted into the format authority's schema
  (Lane, 2026-07-28).
- Worth vendoring: Cartwright and Felleisen, "Extensible
  Denotational Language Specifications" (TACS 1994), the paper
  the Kiselyov page reconstructs, cited at l.514 of the vendored
  copy.
- Worth vendoring: CatColab RFC 0004, "Internal languages for
  models" (Patterson, 2026-04-10). The internal-language seam
  above depends on it, and lines 3 and 4 there need its
  definitions at statement depth.
- Local prior mechanization, the origin of this program:
  `~/TypeTopology/source/Duploids` (Sterling, 2022), set-level
  duploids over Munch-Maccagnoni. To mine: `idn-thunkable` and
  `idn-linear` consume one unit law each, twice, which is the
  template whose porting gap is investigation line 3;
  `cut-thunkable` and `cut-linear` consume no units and port to
  line 4; `Depolarization` (depolarized deductive system is a
  precategory) is the set-level shadow of the `Mag` collapse; the
  announced univalent structure theorem is absent from the
  checkout, so line 7 has no finished set-level precedent there.
  Cite by path and commit after a custody decision.
- Worth vendoring: Melliès, *Asynchronous Games 3*. It is the only
  place the future/buffer gloss could be source-checked at all —
  *future*, *buffer*, and any treatment of asynchrony, buffering,
  scheduling or delay appear nowhere in the six Melliès-authored
  sources currently on the shelf. Meanwhile the gloss carries an
  intrinsic rationale, recorded 2026-07-28 in
  `docs/deductive-systems/framing.md`: a twist is a traced crossing
  and a crossing orders two events, so `twist⁺` (over-under, send
  before receive) is the buffer and `twist⁻` the future. That reading
  is the theory's own and is CONJECTURED, not source-checked. It is
  what fixes `var` to `twist⁻` against the sorts' opposite polarity.
- What the gloss does shadow, and can be honestly re-anchored to, is
  the classical-notions paper's order-of-evaluation semantics: CBN
  parks a **"frozen"**
  expression (buffer-like), CBV demands a value first (future-like),
  and that attaches to the two *compositions*, not to the twists.
- The sourced side-assignment is term = proof/program side, coterm =
  counter-proof/stack side. `framing.md`'s "a covariable is a mailbox
  you enqueue into" is on the sourced side and stands.

## Also pending

A fresh briefing block for the sibling agent, written after the
renames land, so the narrative and the identifiers change together.
