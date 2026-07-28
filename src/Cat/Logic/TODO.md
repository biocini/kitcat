# Cat.Logic — open items

State as of 2026-07-28. `src/Cat` typechecks, 71 modules, and
`src/Test` typechecks, 33 modules. Lint is clean. The `Mag` rebuild
against `src/Mag/TODO.md` remains pending.

`Cat.Logic.Gist` is new: the certified spikes on `Cat.Logic`'s
definitions, vendored out of `Test` with the `Spike` prefixes
dropped. Nine modules: `AssociatesCountermodel`, `FramedCut`,
`FramedGroup`, `FramedInterchange`, `NeutralUnit`, `ReflectFiber`,
`RxDict`, `ThunkableSquare`, `TwistFidelity`. The one-twist trio
(`ExtractedTwist*`) stays in `Test`: it probes the rejected rival
carrier, not these definitions.

Committed through the seam-and-programs commit on
`cat-logic-polarity`, on top of `7f1cf05`, the `Gist` vendoring.
Untracked: `src/Mag/`,
the `Test` spikes `ExtractedTwistCancel` and
`ExtractedTwistModels`, the one-twist brief in `notes/`, and
`resources/selinger-graphical-languages/`.

Prose is gated by the `writing` skill alone. Its bundled linter is
the only prose gate: a changed `docs/` file must score at or under
2.0 violations per 100 words. `bin/lint` covers width and flags, and
the skill triggers on any technical-prose creation or edit. The
skill is the normative statement and
`docs/guidelines/prose-and-comments.md` states the scope. Keep new
prose in that register. Open: whether the gate should also cover
module prose under `src/`, which the retired porcelain gate never
measured either.

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
- Consumers fixed: `Cat/Logic/Gist/FramedGroup`, `Cat/Logic/Gist/TwistFidelity`,
  `Cat/Logic/Gist/FramedCut`, `Cat/Logic/Gist/NeutralUnit`.
- The three-register naming rule is written into `Cat.Logic.Type`,
  beside the twist fields.

Checks that landed as predicted: `mixed-assoc` is now
`(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)` — Mangel's valid word — and
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
`src/Mag/TODO.md`, and the fresh briefing block for the sibling agent.

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

4. **`mixed-leading` / `mixed-trailing` are Mangel's thunkable and
   linear** — the universal closures of the one failing mixed word at
   a fixed leading/trailing edge, which is his definition. Align the
   naming. Note the prefix rule: neither is a proposition, so no
   `is-`. Attachment corrected 2026-07-27: the code closed them over
   the valid word. See the duploid section below.

## The handedness swap — scope

`Cat.Logic.Base` currently has `composite⁻` carrying the `var`
junction (hence `twist⁻`) and `composite⁺` carrying `covar` (hence
`twist⁺`). `Mag` and `Cat.Logic.Gist.FramedInterchange` have it the other way,
and that is the one the literature selects: aligning the provable
mixed word with Mangel's valid word forces

> ⁺ = the `twist⁻`-carrying junction (CBV, value-demanding)
> ⁻ = the `twist⁺`-carrying junction (CBN, "frozen")

So `Cat.Logic` moves and `Mag` does not; afterwards both read the
same way.

Identifiers affected: `composite±`, `inj±`, `is-composable±`,
`cell±`, the `op-*` lemmas, and whatever `Cat/Logic/Display.lagda.md`,
`Cat/Logic/Graph.lagda.md`, `Cat/Logic/Gist/FramedGroup.lagda.md` and
`Cat/Logic/Gist/TwistFidelity.lagda.md` inherit.

Docs affected: `actions.md` and `towers.md`, whose pending-read /
pending-write sentences swap with the names — landing on ⁺ = future
and ⁻ = buffer, which is the CBV/CBN alignment.

## Docs reconciliation

- `Cat.Logic.Base`'s header, `docs/deductive-systems/README.md`,
  `framing.md`, `towers.md` still describe the form-A tier. Under the
  ribbon layer they are describing the balanced layer, not the base
  notion — relocate rather than rewrite.
- `invertibility.md` and `Cat.Logic.Base`'s mid-file prose already
  describe form B; they need the rename only.
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
is `notes/2026-07-27-one-twist-virtual-graph.md`. Its §5 caveat is
confirmed, and its §9 needs the attachment correction recorded in
the duploid section below.

The deciding lemma is refutable, so the derived twist does not
cancel on the term side. `Test/ExtractedTwistCancel.lagda.md`
extends the one-twist carrier of `Test/ExtractedTwist.lagda.md` with
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
passes. `Test/ExtractedTwistModels.lagda.md` runs the path groupoid
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
⁺ as •. The failing word is the one whose middle map runs positive
to negative. Thunkable and linear close over all length-3 paths at
a fixed leading or trailing edge. A unital magmoid carries a
two-sided identity. The shift unit ω has a two-sided pointwise
inverse and is still not an isomorphism, since that notion asks
thunkable and linear of both maps. P is the Kleisli category of the
monad. The duploid of an adjunction is associative exactly when the
monad is idempotent. Idempotent is equivalent to every map
thunkable, and commutative to every map central, for strong monads.
Not found in either source: the "∗-autonomous" leg of §9's collapse
chain. Treat that leg as unchecked. The full statement audits
remain pending, and the PROVISIONAL standing of both entries is
unchanged.

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

Decided 2026-07-27, by countermodel: `Cat/Logic/Gist/AssociatesCountermodel`,
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

## Lines of investigation: toward higher duploids

Enumerated 2026-07-27, from the duploid comparison. Each line names
its question and a first move. Lines 4 to 7 are ordered: each needs
the ones before it.

1. **Bound the associativity profile.** SETTLED 2026-07-27: the
   profile is exactly pre-duploid, at full deductive-system
   strength. See the settled section above and
   `Cat/Logic/Gist/AssociatesCountermodel`.

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

4. **Polarity in the wild setting.** Mangel's definitions are
   stateable verbatim: positive when every map out is linear,
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

5. **The fully balanced layer.** String computation, unverified:
   with both cancellation orders, each hand is two-sided unital
   with its own twist as unit. That is two unital magmoids on one
   graph, offset by θ². State the layer, check the four unit laws,
   and compare with `absorption`. This is where the duploid
   identity apparatus should reappear. First consumer: the `Mag`
   re-founding program in `src/Mag/TODO.md`, which reads
   `hcategory` as the θ² = id merge of the two magmoids and turns
   the comparison table there into a depolarization theorem.

   Readback is independent of the deductive-system axioms, so no
   derivation search is worth a session: `Cat.Logic.Gist.FramedCut`
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
   `Cat.Logic.Gist.FramedCut`, with naturality derived from
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
   lesson of the interchange precedent in `src/Mag/TODO.md`.

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
   gone either way. Remaining gates are mathematical
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

6. **Shifts as representability.** The positive shift's universal
   property is a unique linear factorization through a thunkable
   `ω`. State it as a fiber condition in the house style. Needs
   line 4 for `linear` to have content.

7. **The reflection theorem.** The target that makes the
   comparison a theorem: the polarized, balanced core of a
   deductive system is a duploid, and the correspondence extends
   the adjunction characterization. Its expected home is the
   notion the two source literatures imply and do not define, a
   balanced duploid, with plain duploids as the trivially framed,
   polarized, set-level case.

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
   section below. Next session starts here.

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

1. The word model of the framed point, as a spike. An inductive
   type of words in `t⁻`, `t⁺`, `c⁻`, `c⁺` under the two cuts,
   canonicalized against `assoc⁺`, `assoc⁻`, `mixed-assoc` and
   the centre absorptions `w ⨾⁺ c⁻ ≡ w`, `c⁺ ⨾⁻ w ≡ w`. Decidable
   equality, then the deductive-system axioms, all set-level on
   `--erased-cubical`. Construction: cut-free. Define the normal
   forms as the inductive type and both cuts as admissible
   functions on them. No quotient, so no confluence obligation,
   and item 3's coherence theorem becomes cut admissibility. See
   the internal-language seam, line 1. Payoff immediately: a
   derivability bound for line 3. Refutation in the word model
   kills a candidate outright. Inhabitation is evidence only,
   until item 3 upgrades it.
2. Morphisms. None exist: `Display` and `Graph` carry lenses and
   the reflexive-graph reading, not maps of systems. Design:
   path-level preservation of `reflect` and the twists. System
   maps are graph maps, since the axioms are props. Initiality is
   fiber-shaped, contractibility of the mapping type. Read
   `docs/guidelines/elaboration.md` before fixing signatures.
3. The free system as an untruncated HIT, its initiality, and the
   coherence theorem: free equivalent to the word model. This is
   where the conjecture is decided.

Open design question, Lane's call, before item 1 is written:
whether the free framing takes the centres as generators with
their laws, or the point theory is stated over a bare framed
graph first, with the centres arriving only in item 3.

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
   with that community rather than a work item here.

## Resources

- `resources/munch-maccagnoni-duploids/` — vendored 2026-07-27,
  committed at `0cf05bf`, hash verified. **PROVISIONAL, not audited**,
  so it supports no load-bearing citation yet. The duploid dictionary
  above leans on it and on `mangel-classical-notions`, which is also
  unaudited. Both need statement audits before any of this reaches the
  ledger. Nothing in the tree cites either yet, and nothing should
  until the audits are run. The 2026-07-27 statement pass (the duploid
  section above) checked the §9 anchors at statement depth. It does
  not stand in for the audits.
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
  scheduling or delay appear nowhere in the six Melliès/Mangel
  sources currently on the shelf.
- What the gloss does shadow, and can be honestly re-anchored to, is
  Mangel's order-of-evaluation semantics: CBN parks a **"frozen"**
  expression (buffer-like), CBV demands a value first (future-like),
  and that attaches to the two *compositions*, not to the twists.
- The sourced side-assignment is term = proof/program side, coterm =
  counter-proof/stack side. `framing.md`'s "a covariable is a mailbox
  you enqueue into" is on the sourced side and stands.

## Also pending

A fresh briefing block for the sibling agent, written after the
renames land, so the narrative and the identifiers change together.
