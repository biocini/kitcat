# 2026-07-29: the duploid papers, reviewed and one of them audited

A resources-tree session. Lane asked for reviewer passes over both
duploid-tier entries, `munch-maccagnoni-duploids` and
`mmmm-classical-notions`. It grew into a full edit-review-audit loop
on the first entry (ten revision rounds, seven reviews, one
independent statement audit) and a coverage-depth expansion on the
second, left mid-cycle.

The prior day's audit-chain session is
`notes/2026-07-29-audit-chain-and-doc-registers.md`.

## What was done

1. **Reviewer agents dispatched for both entries.** `munch-maccagnoni-duploids`
   came back PROVISIONAL with a self-contradicting Vetting section (3
   FATAL). `mmmm-classical-notions` came back with a LIGHT
   coverage-depth verdict: 6 of 44 main-text statement environments
   digested, and the flagship Hasegawa-Thielecke digest citing terms
   ("dialogue duploid", "central") the entry never defined.
2. **A researcher pass drafted six new coverage regions** for
   `mmmm-classical-notions` (§8 dialogue duploids, §4 centrality, §5
   graph-morphism adjunctions, the rest of §3, the rest of §11, §1
   dialogue chirality). An opus writer merged them, correcting three
   wrong symbol transcriptions in the draft along the way (`\varowedge`/
   `\varovee`, `\rightharpoonup`, `\dirac`). Coverage rose from 6/44 to
   24/44 statement environments; the entry now carries 30 Content
   digests, up from 7.
3. **`munch-maccagnoni-duploids` went through ten edit rounds**, each
   followed by an independent adversarial re-review, converging on a
   tracked correction patch and a committed measuring script
   (`pdf-scan.py`, Python standard library only) that turned every
   drawn-mark count in the entry from an asserted number into a
   `--check`-verified one (90 comparisons by the last round).
4. **An independent statement audit ran** over
   `munch-maccagnoni-duploids`'s 29 Content digests, from scratch,
   accepting no prior review's fidelity verdict. It found 28 CONFIRMED
   and one drift. The Theorem 28 digest's reflection-theorem triangle
   was mirrored, `⊳` for the source's `◁`. It traced the cause into two
   wrong `ToUnicode` font maps inside the PDF itself. After the fix
   landed and a second independent pass re-read the corrected text, it
   certified **29/29 CONFIRMED (digest-level)**.
5. **The result committed.** `resources/munch-maccagnoni-duploids/README.md`,
   `pdf-scan.py`, and `outputs/duploids-entry-audit.md`, one commit,
   nothing else swept in (a concurrent session had `CHANGELOG.md`,
   `src/Cat/Logic/TODO.md`, and two new `Test.SpikePolarity*` files
   uncommitted throughout; none of it is this session's).

## Strongest findings

**Across ten revision rounds, the mathematics never moved and the
self-description of scope kept moving.** Every round's digest-fidelity
content was independently reconfirmed clean. Every round's claim about
*how completely* something had been checked turned out to overreach by
a small, checkable margin: a wrong count, a table row short by one, an
exception list that named three items where ten existed. The pattern
survived committing a measuring script (round 5). The tool's own
*counts* stopped drifting immediately and permanently, but the *prose
describing what the tool covers* kept drifting for three more rounds,
because a computed number and a claim about a computed number are
different things, and only the number was being tested.

**A second, sharper pattern: duplicate claims in two locations, one
fixed and one not.** "Is `pdf-scan.py` a tracked file" got asserted
correctly in the Files section and incorrectly in Vetting, 72 lines
apart, twice in a row across two different rounds. The eventual fix
was structural, not another sync: convert the second location into a
pointer at the first rather than a restatement, so there is only one
place to be wrong.

**The audit found something no adversarial review had, because it read
differently.** Seven review rounds scrutinized the correction-patch
machinery in detail and never opened PDF page 15 at 600dpi for the
Theorem 28 digest specifically. The audit's from-scratch, digest-by-
digest pass did, and traced a real defect to its root cause (the PDF's
own font encoding, not Poppler) rather than just flagging the symptom.

**The `bin/resources-verify` tooling gap is now confirmed twice, on two
different entries, two days apart.** `notes/2026-07-29-audit-chain-and-doc-registers.md`
flagged it first: the script only checks whether a `Statements
verified:` line exists, never parses `N/M`, so a 3/30 entry reads as
fully "audited — load-bearing capable" exactly like a 29/29 one. Both
`mmmm-classical-notions` (this session) and `munch-maccagnoni-duploids`
(round 6's review) hit it independently. Nobody has fixed it yet.

## Verification state

- `verified`: `munch-maccagnoni-duploids`, 29/29 CONFIRMED
  (digest-level), independent audit, 2026-07-29, bound to
  `@ a39faa7c / eb36ae85` (PDF hash / corrected-extraction hash, both
  named because this is the first entry in the tree where the two can
  change independently).
- `verified`: the correction patch reproduces byte-identically from
  `duploids.pdf` plus the `sed` fence in the README, under GNU sed 4.10
  and macOS BSD sed, confirmed independently in every review round.
- `verified`: `pdf-scan.py --check` reports 90 comparisons, 0 failures,
  and was adversarially mutation-tested (82 deliberate mutations in the
  final round, 53 caught by the extension that round added).
- `verified`: `just resources-verify` reports 16 entries, 18 hashes, 0
  FATAL, and lists `munch-maccagnoni-duploids` as `audited — load-bearing
  capable` (previously `NOT audited`).
- `unverified`, `blocked` pending a dedicated audit: `mmmm-classical-notions`
  has 30 digests on disk, but the `Statements verified:` field still
  reads `3/30` (only the original 2026-07-28 audit's seven digests,
  minus four since revised, plus none of the 23 new ones). Coverage
  rose. Audit coverage did not.
- `unverified`: `mmmm-classical-notions`'s review-2 findings, one MAJOR
  (the `bin/resources-verify` gap above) and seven MINOR
  disclosure/notation items, are recorded but not applied.

## Open questions and risks

1. `mmmm-classical-notions` needs the same cycle
   `munch-maccagnoni-duploids` just finished: apply review-2's
   findings, then commission an independent statement audit over all
   30 digests. See the next-session brief below.
2. `bin/resources-verify` still cannot detect a wrong `N/M`, a stale
   date, or a wrong hash prefix. It only checks the field exists.
   Flagged twice now, on two entries, two days apart. A fix belongs
   either in the script or as a `resources/README.md` amendment, or
   both; no session has picked it up.
3. Neither duploid entry carries a `Vetted:` line. That is explicitly
   Lane's discretion to write, not an editor's or an auditor's. Both
   entries are audited but not yet vetted.
4. `resources/README.md` still has no provision for a per-entry
   measuring script like `pdf-scan.py` (raised as an open question in
   at least three of the seven reviews). It exists, works, and is
   untracked; the format authority doesn't yet say where scripts like
   it belong.
5. A concurrent session had uncommitted `Cat.Logic` polarity-spike work
   (`Test.SpikePolarityTwist`, `Test.SpikePolarityHLevel`,
   `CHANGELOG.md`, `src/Cat/Logic/TODO.md`) in the working tree
   throughout this session. Untouched here; worth checking it landed
   cleanly before assuming a clean tree.

## Next steps

1. Apply `outputs/.drafts/classical-notions-entry-review-2.md`'s
   findings to `resources/mmmm-classical-notions/README.md`, then
   commission an independent statement audit over all 30 digests. Full
   brief below, for a fresh session.
2. Fix the `bin/resources-verify` `N/M`-parsing gap.
3. Decide, at Lane's discretion, whether either duploid entry is ready
   for a `Vetted:` line.

## Artifacts

- Entries: `resources/munch-maccagnoni-duploids/README.md` (audited,
  29/29, committed), `resources/munch-maccagnoni-duploids/pdf-scan.py`
  (new tracked tool, committed), `resources/mmmm-classical-notions/README.md`
  (30 digests, uncommitted, review-2 findings outstanding).
- Audit: `outputs/duploids-entry-audit.md` (committed).
- Reviews and research, on disk and gitignored under `outputs/.drafts/`:
  `duploids-entry-review.md` through `duploids-entry-review-7.md`,
  `classical-notions-entry-review.md`, `classical-notions-entry-review-2.md`,
  `classical-notions-depth-research-sections.md`.
- Plans: `outputs/.plans/classical-notions-depth.md`,
  `outputs/.plans/classical-notions-depth-T1.md`.
- Commit: one, this session (`resources: the duploid entry audited,
  29/29 confirmed`).
