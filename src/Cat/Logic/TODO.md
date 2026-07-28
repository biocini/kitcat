# Cat.Logic — open items

State as of 2026-07-27. `src/Cat` typechecks, 62 modules. `src/Test`
typechecks apart from the two `Mag` spikes, which the `Mag.Type`
rewrite broke. Lint is clean.

Committed at `b979bb6` on branch `cat-logic-polarity`, which is the
rename and the docs together. Two commits sit on top of it: `618184e`
adds the agent suite, and `7dc65e8` applies the STE register across
the docs and adds a prose check to `bin/lint`. The working tree also
carries the `associates` correction in `Cat.Logic.Base`, the matching
`towers.md` passage, and the prose-gate scrub in `bin/lint`, the
`writing` skill, `prose-and-comments.md`, and the root `CLAUDE.md`.
Untracked: `src/Mag/`, six `Test` spikes, the one-twist brief in
`notes/`, and `resources/selinger-graphical-languages/`.

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
- Consumers fixed: `Test/FramedGroup`, `Test/TwistFidelity`,
  `Test/SpikeFramedCut`, `Test/SpikeNeutralUnit`.
- The three-register naming rule is written into `Cat.Logic.Type`,
  beside the twist fields.

Checks that landed as predicted: `mixed-assoc` is now
`(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)` — Mangel's valid word — and
`unitr⁺ : f ⨾⁺ twist⁺ y ≡ f`, `unitl⁻ : twist⁻ x ⨾⁻ g ≡ g` now agree
with `Test/FramedInterchange` on the nose.

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
`twist⁺`). `Mag` and `Test.FramedInterchange` have it the other way,
and that is the one the literature selects: aligning the provable
mixed word with Mangel's valid word forces

> ⁺ = the `twist⁻`-carrying junction (CBV, value-demanding)
> ⁻ = the `twist⁺`-carrying junction (CBN, "frozen")

So `Cat.Logic` moves and `Mag` does not; afterwards both read the
same way.

Identifiers affected: `composite±`, `inj±`, `is-composable±`,
`cell±`, the `op-*` lemmas, and whatever `Cat/Logic/Display.lagda.md`,
`Cat/Logic/Graph.lagda.md`, `Test/FramedGroup.lagda.md` and
`Test/TwistFidelity.lagda.md` inherit.

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

Open, from the same pass. No inhabitant of `thunkable` or `linear`
is derived, and the twists and the tier centres are the candidates.
Mangel's polarity definitions are stateable verbatim: positive when
every map out is linear, negative when every map in is thunkable.
A separating countermodel for `associates` would certify that the
towers carry exactly the pre-duploid associativity profile.
Correlation spaces and Blass games are the literature's witnesses.
Whether the readback-carrying record derives `associates` outright
is also open.

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
