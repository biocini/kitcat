# One-twist verdict, duploid pass, associates

> Relocation banner, 2026-07-28. The `Test.ExtractedTwist*` trio
> named below now lives at `Bb.OneTwist.{Base,Cancel,Models}`, and
> the brief `notes/2026-07-27-one-twist-virtual-graph.md` is
> deleted. The resources entry `mangel-classical-notions` is renamed
> `mmmm-classical-notions`, 2026-07-28. Paths in this dated record
> are left as written.

Session log, 2026-07-27. Branch `cat-logic-polarity`, four commits:
`13bd646`, `cb00916`, `fe98769`, `ec98ebe`. The brief for the day's
question is `notes/2026-07-27-one-twist-virtual-graph.md`.

## What was done

1. Settled the one-twist `virtual-graph` proposal, against, by
   countermodel. The deciding lemma `act-π (twist⁻ x) ≡ snd` is
   refutable over the one-twist carrier with the full `⁺` tier.
2. Ran the §11 checks of the brief, with the path groupoid and the
   abelian group instantiated against the one-twist carrier.
3. Reread the balanced-category anchors (Melliès Definition 9,
   Selinger after Joyal-Street). Ran a statement-level pass over the
   two duploid sources. The pass confirmed the §9 dictionary and
   found one defect in the tree.
4. Fixed the defect: `mixed-assoc` is a theorem of `tower`
   (stability and the two cuts), the failing word is the property
   `associates`, and `thunkable`/`linear` close over it. `towers.md`
   carries the same statement.
5. Scrubbed the prose gate out of `bin/lint`. The `writing` skill's
   bundled linter is the only prose gate, and the skill triggers on
   any technical-prose creation or edit.
6. Ran an accuracy pass over `docs/deductive-systems/` (eleven
   files) and the `Cat.Logic` module prose (no module edits needed
   beyond item 4).
7. Recorded the settled questions, the duploid pass and eight lines
   of investigation toward higher duploids in `src/Cat/Logic/TODO.md`.

## Strongest findings

- **The term-side cancellation is refutable.** verified,
  `src/Test/ExtractedTwistCancel.lagda.md` (`no-cancel⁺`,
  `no-agree`). The model is the Klein four-group `Bool × Bool` under
  `xor`, with `reflect m (t , k) = t ⊕ (σ m ⊕ k)` for `σ` a
  three-cycle of the non-unit elements. Extraction walks the cycle:
  `twist⁺ = ψ twist⁻`, and the `⁺` centre is `ψ² twist⁻`, a
  different element. By contractibility the cancellation is the
  centre-agreement (`cancel⁺→agree`, `agree→cancel⁺`), and the
  agreement is op-involutivity at the twist field. One refutation
  settles both. `virtual-graph` keeps five fields and position (C)
  stands.
- **Why the countermodel needed a twist.** In any model where
  `reflect` is a plain composite, the one-sided identities meet and
  manufacture a unit, so groups, monoids and path groupoids satisfy
  the cancellation automatically. That strategy for a countermodel
  fails structurally. The permutation-twisted reflection is what
  escapes it, in the same genre as `Test/ReadbackTwist`.
- **The brief's §5 reduction does not transpose.** verified, same
  module: right-cancellability of `_⨾⁻ twist⁺` holds
  (`⨾⁻twist⁺-cancellable`) while the frame law fails (`no-frame⁻`).
  The readback-record reduction loses its frame-law ingredient in
  the readback-free carrier, not cancellability.
- **The two cancellations are independent axes.** One holds by
  construction in the model while the other is refutable. The
  plain-composite models collapse the two into one equation, which
  is why `Test/SpikeFramedCut` and `Test/FramedGroup` cannot witness
  the split.
- **`thunkable` and `linear` were vacuous as coded.** The valid
  mixed word `(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)` is derivable from
  stability and the two cuts alone: both bracketings represent one
  judgment. verified, `Cat.Logic.Base` (`mixed-assoc`, module
  `mixed`). The closures therefore held for every edge. They now
  close over the failing word `associates`, which matches the
  sources' definition. Junction dictionary, source-checked: `⁻` is
  `◦` (negative middle), `⁺` is `•` (positive middle); the failing
  configuration is the `+ → ⊖` middle.
- **The towers carry the pre-duploid associativity profile.**
  `assoc⁺`, `assoc⁻` and `mixed-assoc` are exactly Definition 1's
  three axioms, as theorems; `associates` is the withheld word.
  Bounding the profile from above needs line 1 below.

## Encoding decisions

- The countermodel carrier is `Bool × Bool` with componentwise
  `xor`, reusing `Core.Data.Bool`'s `xor.assoc`, `xor.invol`,
  `xor.unitr`, `xor.comm`. Tables by full case split, every clause
  `refl`.
- Tier proofs follow `Test/FramedGroup`'s pattern:
  `injective→is-embedding` under `Π-is-hlevel 2`, then
  `prop-inhabited→is-contr`. That combinator keeps the supplied
  centre definitionally, so the extracted `twist⁺` computes and the
  later fields typecheck by unfolding.
- The model spikes state their proofs against top-level functions
  definitionally equal to the record's projections, which avoids
  self-reference in the copattern definitions.

## Verification state

- verified: `just check` runs on 2026-07-27, exit 0, for
  `Test.ExtractedTwistCancel`, `Test.ExtractedTwistModels`,
  `Cat.Logic.Base`, `just check-tree src/Cat` (62 modules), and the
  four Logic-consuming tests (`FramedGroup`, `TwistFidelity`,
  `SpikeFramedCut`, `SpikeNeutralUnit`). Zero new obligations: no
  sorries, no postulates, `--safe` throughout.
- unverified: the fully balanced layer's two-unital-magmoids
  reading (string computation, TODO line 5); the equivalence of the
  one-twist carrier with the two-twist record plus one cancellation
  (analysis only); the transposition of the Klein model to the
  two-field record (inferred, not formalized); the observation that
  the twice-opposed full record's fields land at centre-closed maps
  nothing represents (typed elaboration, no spike).
- Source anchors, opened this session: Selinger,
  `resources/selinger-graphical-languages/graphical.tex` l.1074-1089
  (twist as a natural family of isomorphisms, citing Joyal-Street);
  Melliès, `resources/mellies-braided-dialogue` pdftext l.3066
  (Definition 9) and l.3229 (Definition 11); Munch-Maccagnoni,
  `resources/munch-maccagnoni-duploids` pdftext l.180 (Definition
  1), l.233, l.286, l.418, l.440, l.899 (Theorem 28), with the
  failing word stated near l.410; Mangel,
  `resources/mangel-classical-notions` article.tex l.1526, l.1551,
  l.1694, l.1712, l.1819, l.1860, l.3112, l.3135. The
  "∗-autonomous" leg of the brief's §9 collapse chain was not found
  in either source and stays unverified. Both duploid entries remain
  PROVISIONAL; the statement pass does not stand in for the audits.

## Artifacts

- `src/Test/ExtractedTwistCancel.lagda.md`: the decisive spike.
  Untracked.
- `src/Test/ExtractedTwistModels.lagda.md`: path groupoid and
  abelian group against the one-twist carrier (`twist⁺-forced`,
  `group-cancel⁺`). Untracked.
- `src/Cat/Logic/Base.lagda.md`: `mixed-assoc`, `associates`, the
  re-attached closures. Committed, `cb00916`.
- `docs/deductive-systems/`: the accuracy pass, eleven files.
  Committed, `fe98769`.
- `src/Cat/Logic/TODO.md`: settled records, eight investigation
  lines. Committed, `ec98ebe`.
- `bin/lint`, `.claude/skills/writing/SKILL.md`,
  `docs/guidelines/prose-and-comments.md`, `CLAUDE.md`: the prose
  gate scrub. Committed, `13bd646`.
- `src/Test/MixedWord.lagda.md` existed within the session to run
  the derivability check and is deleted; its proof lives in `Base`.

## Open questions and next steps

The eight lines in `src/Cat/Logic/TODO.md` are the queue. Line 1
(the separating countermodel for `associates`) is the opener, and
line 2 (thunkability as property or data) is the deepest question.
Also pending there: the two statement audits, the gate-scope
question for module prose under `src/`, the `Mag` rebuild, and the
sibling-agent briefing block.

One risk to clear early: the committed docs cite
`Test.ExtractedTwistCancel` and `Test.ExtractedTwistModels` as
VERIFIED anchors while both spikes are untracked. Track them, or
the anchors dangle for any reader of the committed tree.
