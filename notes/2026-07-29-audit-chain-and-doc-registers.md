# 2026-07-29: the audit chain, and where documents live

A maintenance session. It started as a chore sweep and turned into
two things: a three-pass audit chain over a vendored source entry, and
a ruling on which directory each kind of document belongs in.

The formalization half of the same day is
`notes/2026-07-28-morphisms-polarity-docs.md`.

## What was done

1. **The euler subagents configured**, then verified by dispatch.
   Models pinned, the `Skill` tool granted to all four, prose-standard
   sections added. Logged at
   `notes/2026-07-28-euler-subagent-config.md`.
2. **The All porcelain retired.** `just sync` and `just check-all`
   removed, `check-tree` restated, references struck from five files.
3. **`bin/lint citations` added.** It fails when a `gloss.md` or
   `lemmata.md` names a module that does not resolve under `src/`.
4. **A three-pass audit chain** over
   `resources/munch-maccagnoni-duploids/`. The certification was
   withdrawn, six digests corrected, four missing statements written,
   and the field refused again on two defects in those corrections.
5. **The document registers ruled**, and `docs/plans/` created.

## Strongest findings

**The reviewer configuration was verified, not assumed.** Two
dispatches settled three open questions. `model: fable` parses from
agent frontmatter, so the plugin documentation listing four values
predates Fable. Fable needs usage credits this account lacks, which
made the reviewer undispatchable and forced the fallback to `opus` at
`xhigh`. And agent definitions reload **live**, not at session start,
so the repeated "takes effect next session" caveat was wrong.

**The audit chain found a defect at every pass, including in its own
corrections.** The sequence is the finding.

- Pass 1 (Sonnet) wrote 24 digests and certified them `24/24` in the
  same run. `resources/README.md` requires the audit to be
  independent of the authoring.
- Pass 2 (`reviewer`, opus/xhigh) found six of 24 digests drifting,
  coverage at 24 of 28 statements, and a fabricated evidence claim:
  "confirmed against rendered PDF pages" for a paper with no vendored
  PDF and no LaTeX engine installed. It also found an invented
  citation, "after Führmann and Hasegawa", where the source says
  `[16,8]` and Hasegawa appears nowhere in the paper.
- The lead corrected the six and wrote the four missing digests.
- Pass 3 (`verifier`, opus) confirmed 26 of 28 and **refused the
  field on two defects the lead had just introduced.**

**The lead's Proposition 16 error is the instructive one.** The text
extraction flattens a two-column display, and the lead read it in line
order, so `force_A` landed in the wrong equation. The result typed as
`A → ⇑B` where the functor needs `⇑A → ⇑B`. A render at 500 dpi and
the type of `force_P : ⇑P → P` settled it. Reading a flattened
extraction as if it were linear is a specific, repeatable failure, and
the entry now carries a note about it.

**Lane's conflation hypothesis was right and narrow.** The Hasegawa
attribution came from the sibling entry, whose title is "Classical
notions of computation and the Hasegawa-Thielecke theorem", digested
in the same run. Exactly one contamination hit. Every other proper
name belongs.

**Documents rot by directory, not by carelessness.** `just mv` sweeps
`src/` only, and nothing typechecks a document, so a document naming a
module inherits its lifetime without its maintenance. Thirteen of
`docs/gloss.md`'s 22 cited paths dangle. Eleven of twelve
`docs/deductive-systems/` files were stale. Seven of twelve
`docs/guidelines/` files carry `src/` citations their own register
bars. `guidelines/CLAUDE.md` already states the argument as the
rationale for its own rule.

**Ruling (Lane): the four registers.** Module prose says what an
object is. `<namespace>/gloss.md` carries commentary on a
construction. `<namespace>/lemmata.md` carries the statements.
`docs/guidelines/` carries standards stated abstractly. The `gloss`
and `lemmata` pairing is the classical one: the lemma is the headword,
the gloss the commentary against it.

**Ruling (Lane): `docs/plans/` for standing plans.** The distinction
is ephemeral against standing, not tracked against untracked. Every
file in `outputs/.plans/` today is a consumed run brief, so its
gitignore is right about its own contents. What lacked a home was the
standing plan with gates, which `notes/` had been absorbing alongside
dated session records.

**`composite-rx-refactor` was never misplaced.** It is a standing
gated program, the same shape as `docs/roadmap.md`. What was wrong in
`docs/` was `deductive-systems/`, namespace commentary that belongs
beside its code. Its status line, which read as though a review
blocked it, now records the real gate: the deductive-system line
reaching the category presentation.

## Verification state

- `verified`: `just check-tree src/Cat` 21/21 and `src/Test` 9/9,
  after the recipe removals.
- `verified`: `bin/lint citations` detects the 13 known dangles and
  produces no false positives. Tested with a planted `lemmata.md`
  carrying live modules, a namespace directory, and two dead paths;
  it passed the three live forms and flagged only the dead.
- `verified`, by the lead, re-deriving each: no PDF and no LaTeX
  engine for `mmmm-classical-notions`; Hasegawa absent from
  `duploids.pdftext`; the paper carries 28 numbered statements;
  Definition 23's "is an equaliser of"; Proposition 24's "G and F";
  the Proposition 16 column interleaving at l.707-722.
- `verified`, by pass 3: 26 of 28 digests faithful, both wrapped
  anchors correct, coverage 28/28.
- `unverified`: Propositions 14 and 16 as now written. The lead wrote
  both fixes, so a fourth reader must confirm them before the field
  is issued.
- `blocked`: the certification field. Refused pending that read.

## Open questions and risks

1. The field needs a fourth reader over Propositions 14 and 16 only.
   Pass 3's 26 confirmations stand and do not need redoing.
2. `outputs/duploids-statement-audit.md` still carries its own false
   claims: a blanket anchor claim with four failures, and a Q4 answer
   denying the state its own commit created.
3. `article.tex:1691` cites a second Munch-Maccagnoni duploid
   reference under bibkey `newduploids`, three lines before the
   Polarity definition. The open cross-paper question is four-way,
   not three-way.
4. `bin/resources-verify` tests only that the certification line
   exists. It cannot detect a wrong count, date, or hash.
5. The typo claim should be scoped to the arXiv v4 e-print. Nobody
   opened the PACMPL published record.

## Next steps

1. A fourth reader over Propositions 14 and 16, then the field.
2. The documentation restructuring,
   `docs/plans/documentation-restructuring.md`. Step 4 unblocks once
   the duploid entries settle.
3. `Cat.Logic.Morphism`, the roadmap item this day opened with. The
   brief is `outputs/.plans/system-morphisms-T1.md`.
4. Move the three remaining standing plans into `docs/plans/`, each
   with its citation sweep.

## Artifacts

- Tooling: `justfile`, `bin/lint` (the `citations` check), `CLAUDE.md`,
  `README.md`, `flake.nix`.
- Registers: `docs/plans/README.md` (the standard),
  `docs/plans/documentation-restructuring.md` (the program map).
- Entries: `resources/munch-maccagnoni-duploids/README.md` (field
  withdrawn, six digests corrected, four statements added, two
  defects repaired), `resources/mmmm-classical-notions/README.md`
  (paraphrase wording, two anchors).
- Records: `CHANGELOG.md` (the correction note), `TODO.md`,
  `docs/gloss.md` (T35's warrant re-pointed).
- Reviews, on disk and gitignored:
  `outputs/.drafts/duploids-statement-audit-review-2.md`,
  `outputs/.drafts/system-morphisms-review.md`.
