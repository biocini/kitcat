# 2026-07-29: the associates defect promotion and the ledger split

Objective at open: ask the sharper question behind the 2026-07-27
independence result. `associates` fails at the free framed point,
but the countermodel names no relation between the two bracketings.
This session found the relation, promoted the result into
`Cat.Logic.Gist`, and started the per-namespace ledger split that
`docs/plans/documentation-restructuring.md` specifies.

## What was done

1. **Dispatched a Fable subagent** to measure the defect over
   `Cat.Logic.Gist.BalancedWord`. The brief pinned the candidate
   placements, the recorded instance, and a stopping rule: do not
   generalize past the bare framed point.
2. **First attempt killed mid-run** by Lane, before it wrote any
   artifact. A `git status` check and a `Test/` file search
   confirmed this. A `SendMessage` resume attempt returned
   `success:false`: a user-initiated stop does not resume, unlike a
   self-paused agent. This session recorded the distinction in the
   `restart-means-same-agent` memory file.
3. **Relaunched with a process note.** Iterate by writing and
   running concrete checks against the model and the checker. Do
   not reason out candidates in the abstract. The scope and the
   brief stayed the same.
4. **The second attempt survived three transient API errors**: one
   500, then two 529 Overloaded. It resumed through each one and
   returned a completed result: a script
   (`outputs/.notes/associates-defect-search.py`) and a spike
   module.
5. **Independently verified the subagent's report.** This session
   did not trust the summary alone. It read the full 628-line
   module. It ran `just check` (exit 0, zero output). It grepped
   for postulates, holes, and `TERMINATING` (none found). It ran
   the bundled prose linter (1.90 violations per 100 words). It
   scanned the prose and the diff for novelty or impossibility
   language (none found). It confirmed `is-deductive-system`'s
   field list, the handedness swap, and the independence result
   stayed untouched.
6. **Promoted the spike.** `just mv Test.SpikeAssociatesDefect
   Cat.Logic.Gist.AssociatesDefect` updated one reference
   automatically. The opener now leads with the result's
   significance, written through the `writing` skill. It keeps the
   `Spike:` prose marker every `Gist` module carries. It carries no
   frontmatter yet, since the tree-wide frontmatter sweep has not
   landed and the sibling `Gist` modules do not carry it either.
7. **Swept the stale references** the rename left behind:
   `src/Cat/Logic/TODO.md`'s settled block and `Gist` inventory,
   `CHANGELOG.md`'s verified-check line, and
   `outputs/.notes/associates-defect-results.md`'s path note. A
   repository-wide search found no surviving reference to
   `SpikeAssociatesDefect`.
8. **Started the `Cat.Logic` ledger split**, per
   `docs/plans/documentation-restructuring.md`. The bare statement
   and citation go in `src/Cat/Logic/lemmata.md`. The extended
   commentary goes in `src/Cat/Logic/gloss.md`, under the same
   numbers `docs/gloss.md` used. This session read T18 through T35
   in full and classified each entry by where its subject matter
   now lives, not by number, per the plan's own instruction.
9. **Moved T25 to T30 and T32 to T35**, and added the new result as
   T36. T31 and T21 to T24 stayed in `docs/gloss.md`: their sole
   citations resolve to archived `Bb` modules, and their true home
   is a per-tree ledger that does not exist yet. This session
   recorded that partial state directly in the plan document.
10. **Fixed mechanical prose debt** the move introduced: em dashes
    and over-length sentences in the newly authored ledger text,
    and a stale `docs/gloss.md` pointer in `src/Cat/Logic/TODO.md`.

## Strongest findings and decisions

- **The defect is a determinate twist word, one per flanking edge.**
  `defect⁺ : f ⨾⁺ (g ⨾⁻ h) ≡ w⁺ (rise f) ⨾⁺ ((f ⨾⁺ g) ⨾⁻ h)` reads
  only the leading edge, through `rise f`, its value at zero.
  `defect⁻ : (f ⨾⁺ g) ⨾⁻ h ≡ (f ⨾⁺ (g ⨾⁻ h)) ⨾⁻ w⁻ (zrunW h)` reads
  only the trailing edge, through `zrunW h`, the length of its zero
  plateau. Both hold for every triple, with no failure hypothesis.
- **Sixteen placements, two survivors.** This session enumerated
  every well-typed placement of a correcting word between the two
  bracketings: eight whole-word flanks (`A1` to `A8`) and eight seam
  positions (`S1` to `S8`). One-sided invertibility keeps all
  sixteen pairwise distinct. Fourteen fail outright at one of two
  concrete triples. The checker confirmed each failure holds for
  every candidate word at once. Only `defect⁺` and `defect⁻`
  survive.
- **No uniform word exists** (`no-uniform⁺`, `no-uniform⁻`,
  machine-checked negations). The defect is not a framing constant.
- **The corrections vanish exactly at the known closures.** `w⁺` is
  the unit exactly when `f` is thunkable
  (`thunkable→rise`, `rise→thunkable`). `w⁻` is the unit exactly
  when `h` is linear (`run→linear`, `linear→run`). This gives a
  reason for the axioms' choice: thunkability on the leading edge,
  linearity on the trailing edge, not a stipulation.
- **Balance kills the measured defect.** `shift-associates` proves
  the two bracketings always agree in winding grade. The
  pre-duploid profile now has a mechanism, not a bare countermodel.
  The claim that the ℤ-collapse itself satisfies `associates` is
  script-level only. The ℤ point carries no `is-deductive-system`
  instance, so that claim has no kernel witness.
- **Process finding, not mathematical.** A user-initiated agent
  stop and a self-paused agent are different states. Only the
  second resumes through `SendMessage`. The first needs an explicit
  relaunch. A request to continue the same work counts as one.

## Verification state

- verified: `just check src/Cat/Logic/Gist/AssociatesDefect.lagda.md`,
  2026-07-29, exit 0, zero output. No postulates, no holes, no
  `TERMINATING`, confirmed by direct grep. Every named theorem in
  this log is machine-checked in that run: `defect⁺`, `defect⁻`,
  `no-uniform⁺`, `no-uniform⁻`, `A1-refuted` through `A8-refuted`,
  `S1-refuted` through `S8-refuted`, `shift-w⁺`, `shift-w⁻`,
  `shift-associates`, `thunkable→rise`, `rise→thunkable`,
  `run→linear`, `linear→run`.
- verified: prose gate. `src/Cat/Logic/Gist/AssociatesDefect.lagda.md`
  scores 1.50 per 100 words. `src/Cat/Logic/lemmata.md` scores 1.75.
  `src/Cat/Logic/gloss.md` scores 0.16. `docs/gloss.md` scores 1.93.
  `docs/plans/documentation-restructuring.md` scores 1.57. All sit
  under the 2.0 gate.
- verified: `just lint citations` finds zero dangling citations in
  the two new ledger files. It reports 13 dangling citations
  elsewhere, all pre-existing, in the untouched T1 to T24 region of
  `docs/gloss.md`.
- verified: `just lint changed` passes clean.
- unverified: the placement census over the enumerated model, 4096
  triples against 256 candidate words
  (`outputs/.notes/associates-defect-search.py` and `-results.md`).
  Also unverified: the claim that the ℤ-collapse image satisfies
  `associates`, checked at 343 sampled triples. Both are
  script-level only, with no kernel witness.
- blocked: none.

## Open questions and risks

1. Whether the per-edge factorization generalizes past the bare
   framed point, which has no generators. The named next instrument
   is the generator-bearing word model, initial-model program item
   1's sequels.
2. The documentation restructuring's step 4 is only partly done.
   T31 and T21 to T24 need their own `Bb`-tree `lemmata.md` files.
   Each needs a `CHANGELOG.md` entry in that tree first.
3. Step 5 (triage `docs/deductive-systems/`'s twelve files into
   `src/Cat/Logic/gloss.md`) has not started.
4. The plan marks the ledger split gated on the third-pass duploid
   audit settling. Two working-tree edits were present before this
   session opened and stayed untouched:
   `resources/mmmm-classical-notions/README.md` and
   `resources/munch-maccagnoni-duploids/README.md`. Both are
   consistent with that audit still being open. This session's
   slice did not touch the entries that gate protects. A session
   that continues the split should confirm audit status first.

## Next steps

The generator-bearing word model is the next instrument for the
associates-defect question. On the documentation side: create
`src/Bb/WeakDeductiveSystem/lemmata.md` and
`src/Bb/CatsWithExplicitInterchange/lemmata.md`, each with a
`CHANGELOG.md` entry in its own tree. That moves T31 and T21 to T24
out of `docs/gloss.md`. Then run step 5's triage of
`docs/deductive-systems/`.

## Artifacts

- Library: `src/Cat/Logic/Gist/AssociatesDefect.lagda.md`, promoted
  from `src/Test/SpikeAssociatesDefect.lagda.md`.
- Ledgers: `src/Cat/Logic/lemmata.md` (new), `src/Cat/Logic/gloss.md`
  (new), `docs/gloss.md` (thinned; T25 to T30 and T32 to T35 moved
  out).
- Records: `src/Cat/Logic/TODO.md` (settled block, `Gist` inventory,
  one stale pointer fixed), `docs/plans/documentation-restructuring.md`
  (step 4 progress note), `CHANGELOG.md` (path reference fixed, plus
  this session's own entry).
- Research: `outputs/.notes/associates-defect-search.py`,
  `outputs/.notes/associates-defect-results.md` (path reference
  fixed).
- Memory: `restart-means-same-agent.md`, updated with the
  user-kill-versus-self-pause distinction.
