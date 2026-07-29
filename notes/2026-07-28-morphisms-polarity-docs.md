# 2026-07-28: morphisms opened, the polarity alarm, the docs sweep

Objective at open: `src/Cat/Logic/TODO.md` line 9 item 2, morphisms
of systems, with Fable subagents on the heavy parts. The session
delivered the initiality half. It then stopped for a reported
polarity error in `Cat.Logic.Base`. That error proved to be a false
alarm with a real cause. Paying the cause down took the rest of the
session.

## What was done

1. **Briefs written, two agents dispatched.** The shared plan and
   two task briefs went to `outputs/.plans/system-morphisms*.md`.
   Each brief carries exact `file:line` anchors, the style
   divergences that `Cat.Logic` holds against the general
   guidelines, and a verification ladder. T1 (the live morphism
   record) and T2 (initiality) ran in parallel on disjoint files.

2. **T2 landed: `Test.SpikeMorphismInitial`.** It states the
   morphism record and initiality, and it inlines its own carrier
   per the spike convention. `_⇒_` carries `map`, `hmap`,
   `pres-twist⁺`, `pres-twist⁻` and `pres-reflect`. Initiality is
   `is-initial G = ∀ G' → is-contr (G ⇒ G')`, itself a proposition.
   Three results follow. Initiality truncates no hom. The empty
   graph is initial. The codiscrete graph on two points carries the
   full axioms and still has two distinct self-maps.

3. **T1 did not land.** The polarity report arrived first, and both
   agents stopped. T1 had written no file.

4. **The polarity alarm resolved as a false alarm.** Lane reported
   that `inj⁺`/`inj⁻` came from the wrong actions, and asked for a
   suite-wide revision. The composition labels turned out correct
   and the proofs sound.

5. **Four prose corrections**, in `Cat.Logic.Base` (twice),
   `Cat.Logic.Type`, and `docs/deductive-systems/actions.md`.

6. **`docs/deductive-systems/` reconciled** against the record cut.
   Eleven of twelve files were stale.

7. **`(D′)` retired** from the live tree and `docs/roadmap.md`. The
   `BalancedWord` preface now describes the construction.

## Strongest findings and decisions

**The polarity labels are correct. The order convention was the
missing fact.** Munch-Maccagnoni composes applicatively, so `g ∘ f`
runs `f` first. This library composes diagrammatically, so `f ⨾ g`
runs `f` first. Transcribe Definition 1's (•◦) clause without
reversing the order and the word reads backwards, which inverts the
two labels on sight. Done correctly over `A -f→ N -g→ P -h→ B`,
`(h • g) ◦ f = h • (g ◦ f)` becomes
`(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)`. That is `mixed-assoc` verbatim, so
the ledger's `⁻ = ◦` and `⁺ = •` both stand. The convention now sits
in `docs/deductive-systems/towers.md` and in the TODO's duploid
section. Its absence is what let the misreading run.

**Two registers, and prose that conflated them.** The twist sign
orders events. A traced crossing sends before it receives at
`twist⁺`, which is a buffer, and receives before it sends at
`twist⁻`, which is a future. The sort polarity says which half of an
argument a thing fills: a term is positive, a coterm negative. The
two cross irreducibly. `var` is a term and carries `twist⁻`. `covar`
is a coterm and carries `twist⁺`. Four prose sites justified a
`⁺`/`⁻` label by the axiom a map holds. That phrasing reads as
binding `var` to coactions, which inverts the standard. All four now
state the label's own register.

**The causality account is on record and is not sourced.**
`docs/deductive-systems/framing.md` now derives the future and
buffer gloss from traced crossings, under "Why each twist takes the
side it does". It is the theory's own reading, so it is
`CONJECTURED`. Melliès, *Asynchronous Games 3*, remains the only
place that could source-check it, and it is still not on the shelf.

**Ruling (Lane): `act` and `coact` keep their names.** `act-π` holds
`covar` and `coact-π` holds `var`, which inverts the var-with-act
standard. The types force that binding, since a family over terms
can only fix the coterm slot. So it is implementation, not
semantics. A rename would make `act` contravariant on coterms.
Decision: keep the names, fix the prose, and never justify a label
by the held axiom.

**Ruling (Lane): `(D′)` leaves live prose.** The label names a
position only against the rejected `(C)` and `(D)`. It therefore
reads as one variant among several when it is the definition. Live
prose says "deductive system". The `Bb.WeakDeductiveSystem`
namespace already marks the archived weaker notion. Where the
difference needs a word, the live carrier bears readback and the
archived stratum is readback-free. The TODO keeps the letters as the
record of the decision.

**Ruling (Lane): pay docs debt in the task that finds it.**
Flagging stale documentation for later is the deferral that created
it.

**The record cut had invalidated most of the doc set.** Eleven of
twelve files carried superseded claims, not the two flagged earlier.
`the-package.md` documented the pre-cut three-field record, and
cited `FramedCut` as the inhabitant, which readback rules out.
`composability.md` showed the stability-indexed record.
`stability.md` explained why stability "comes first". `towers.md`
claimed one unit law per hand. `invertibility.md` and `framing.md`
each claimed that nothing decides whether a centre is the other
twist, which T33 refutes. `README.md` omitted `readback` from the
carrier and drew `is-stable` as a tier. The retired `pin`, `K`,
`unital` and `absorption` names survived in five doc sites and in
the register list of `Cat.Logic.Type`.

## Verification state

- `verified`: `just check Test.SpikeMorphismInitial`, exit 0. A
  control run on a bad module name exits 42, so the silent pass is a
  real pass. Obligation inventory zero: no `postulate`, no holes, no
  unsafe pragma. Maximum line width 89.
- `verified`: `just check-tree src/Test`, 9 of 9 modules.
- `verified`: `just check-tree src/Cat`, 21 of 21 modules. It ran
  after the prose edits and again after the `(D′)` retirement.
- `verified`: `just check` on `Cat.Logic.Base`, `Cat.Logic.Type`,
  and the three `Cat.Logic.Gist.Balanced*` modules.
- `verified`: `just lint changed`, width and flags clean.
- `verified`: the `writing` linter on all twelve
  `docs/deductive-systems/` files and on `docs/roadmap.md`. Every
  file scores at or under the 2.0 gate. `displays.md` and
  `invertibility.md` sat at 1.92 and 2.00 before this session. The
  additions tipped both over, so their sentences needed tightening.
  Final scores 1.59 and 0.86.
- `unverified`: that the spike's record is the right live signature.
  The probes of `docs/guidelines/elaboration.md` have not run.
- `unverified`: `pres-⨾⁺` and `pres-⨾⁻`. Nobody attempted them.
- `inferred`: that mapping types are wild beyond this one carrier.
  The session built one countermodel.
- `blocked`: none.
- Pre-existing and untouched: five `just lint flags` failures under
  `src/Cat/Graph/Refl`, each "missing --no-guardedness".

## Open questions and risks

1. `Cat.Logic.Morphism` does not exist. The spike inlines its own
   copy of the record, so the two can drift.
2. `pres-⨾⁺` and `pres-⨾⁻` need the target's stability, hence
   `reflect-lc`, hence a deductive system on the target rather than
   a bare graph map. State that hypothesis. Do not weaken the
   theorem to avoid it.
3. Whether a mapping type is ever non-trivially higher stays open.
   Two maps equal in more than one way need a target whose homs
   carry a loop. The circle model of `Gist.ThunkableSquare` supplies
   one, and this spike does not build it.
4. Whether the free system attains contractibility against every
   wild target is the coherence conjecture, item 3 of the
   initial-model program.
5. The two duploid source audits remain overdue. Every ledger
   citation that leans on them still waits.
6. `docs/gloss.md` has no entry for the initiality results.

## Next steps

1. `Cat.Logic.Morphism`, from
   `outputs/.plans/system-morphisms-T1.md`. Run the elaboration
   probes, derive `pres-var`, `pres-covar`, `pres-act` and
   `pres-coact`, add identity and composition, then prove
   `pres-⨾⁺` and `pres-⨾⁻`.
2. Promote the spike to `Cat.Logic.Gist.MorphismInitial` under the
   spike-zero policy. Retire its inlined carrier for the live
   record.
3. Then item 3 of the initial-model program: the free system as an
   untruncated HIT, and its initiality.

## Artifacts

- Library: `src/Test/SpikeMorphismInitial.lagda.md`, new and
  staged. Prose corrected in `src/Cat/Logic/Base.lagda.md`,
  `src/Cat/Logic/Type.lagda.md`,
  `src/Cat/Logic/Gist/BalancedWord.lagda.md` (new preface),
  `src/Cat/Logic/Gist/BalancedProfile.lagda.md` and
  `src/Cat/Logic/Gist/BalancedBase.lagda.md`.
- Docs: eleven changed files under `docs/deductive-systems/`, and
  `docs/roadmap.md`.
- Records: `src/Cat/Logic/TODO.md`. Line 9 item 2 now carries what
  landed and what remains. The docs-reconciliation section is
  rewritten, the `(D′)` retirement recorded, the header state trued.
- Plans: `outputs/.plans/system-morphisms.md`,
  `outputs/.plans/system-morphisms-T1.md` and
  `outputs/.plans/system-morphisms-T2.md`.

## Source anchors

Munch-Maccagnoni, *Duploids*, Definition 1, pages 3 to 4. The
clauses (••), (◦◦) and (•◦), and the opening statement that
associativity fails when the middle map has polarity `+ → ⊖`.
Vendored at `resources/munch-maccagnoni-duploids/`, `PROVISIONAL`,
statement audit outstanding.
