# 2026-07-29: mmmm-classical-notions closes the audit cycle

A direct continuation of `notes/2026-07-29-duploid-papers-audit.md`,
which left `mmmm-classical-notions` mid-cycle: review-2's findings
recorded but not applied, and no audit run over the 23 new digests.
This session applied the revision plan, fixed the two tooling gaps
that review had flagged twice, commissioned an independent audit over
all 30 digests, and wrote `Vetted:` lines on both duploid-tier
entries at Lane's direction.

## What was done

1. **Review-2's Revision Plan applied to
   `resources/mmmm-classical-notions/README.md`.** All six in-entry
   items: the Vetting section discloses a second
   source-level typo (`⊢` for `⊣` at `article.tex:2661`), the digest
   preamble names the `⟑`/`⟇` connective substitution
   (`\tensorialand`/`\tensorialor`, stmaryrd, no circled Unicode
   equivalent), the Non-associative category and Shifts digests fix
   `M`/`M^op` to `ℳ`/`ℳ^op`, the Section map's tail row gains the
   `l.3725` `\ifbool{arxiv}{}{\end{document}}` line, the appendix and
   §13 rows use the source's own "Joyal's obstruction theorem" title,
   and the Dialogue duploid digest's `≃` and the dropped clause in the
   Thunkable-implies-central digest are restored.
2. **The downstream drift in `notes/2026-07-25-two-lineages.md:383`
   fixed**, per review-2's [W8]: the anchor moved from `l.3036` to
   `l.3044`, and the claim gained its `⊗` qualifier.
3. **`bin/resources-verify` taught to parse the `Statements verified:
   N/M` fraction.** It now reports a `PARTIAL audit (N/M CONFIRMED)`
   standing whenever `N < M` with no `CORRECTED` clause, and treats
   the tree's other field shape — "`N` CONFIRMED on first pass, `K`
   CORRECTED" where `N + K = M` — as full coverage, so it does not
   misclassify the seven already-vetted entries using that phrasing.
   Confirmed live: `mmmm-classical-notions` read `PARTIAL audit
   (3/30 CONFIRMED)` before the audit landed, full standing after.
4. **`resources/README.md`'s Vetting contract amended** to name a
   digest addition or revision, beside a re-fetch or a re-extraction,
   as an event that voids the `Statements verified:` field — the
   change review-2 asked for outside the entry.
5. **An independent statement audit dispatched** (`verifier`
   subagent, Claude Opus 5, background), modeled on
   `outputs/duploids-entry-audit.md`. It re-derived all 30 digests
   from `article.tex` from scratch, accepting no prior pass's verdict,
   with explicit extra scrutiny on the six passages hand-edited in
   step 1. Verdict: **30/30 CONFIRMED (digest-level)**, 23
   near-verbatim, 7 paraphrase, 0 not confirmed. Written to
   `outputs/classical-notions-entry-audit.md`.
6. **The Vetting section's field text replaced**: `Statements
   verified: 30/30 CONFIRMED (digest-level), 2026-07-29, by Claude
   (Opus 5), @ 8d9edc19055a`, retiring the three-bucket
   audited/revised/new breakdown the partial state had required.
7. **Both duploid-tier entries vetted, at Lane's explicit direction**
   (given mid-session, conditioned on both entries clearing their
   audits): `munch-maccagnoni-duploids` (29/29, from the prior
   session) and `mmmm-classical-notions` (30/30, this session) each
   gained a `Vetted: 2026-07-29, Lane (ratified at Lane's explicit
   direction, conveyed in-session).` line, retiring the PROVISIONAL
   marker on both.

## Strongest findings

**The six passages edited in this session all held against the
source on independent re-audit.** None of the revision-plan edits
introduced drift: the audit re-derived each one from `article.tex`
directly rather than trusting the edit, which is the same discipline
that caught the sibling entry's mirrored-triangle defect. Here it
found nothing to fix.

**The two tooling gaps flagged twice, on two entries, two days
apart, are closed.** `bin/resources-verify` previously reported a
3/30 entry and a 29/29 entry as identically "audited, standing capable
of citation". It now distinguishes them, without misreading the
already-vetted entries that use "N confirmed on first pass, K
corrected" phrasing for full coverage. The format authority now names
a digest edit as a voiding event, closing the gap the sibling
review's [W1] identified.

**The independent audit surfaced eight non-blocking accuracy notes,
left unapplied.** Per standing feedback against unprompted cleanup,
these were reported rather than silently fixed:

- `ℳ` covers two distinct source symbols (`\mathcal M` and
  `\mathscr M`) in different digests.
- The Dirac-form digest drops the source's `1` coefficient. This is
  an open question, not a typo: review-2's [Q2] already raised it,
  and it remains open.
- A second citation (`Mellies2017micrological`) is missing beside
  Cockett-Seely in the Linearly distributive duploid digest.
- A diagram the Functoriality digest calls "the square" is drawn as
  a triangle. This is defensible under the source's own vocabulary,
  but a clearer label exists.
- The Duploid digest does not name `•` and `◦` explicitly.
- The Contextual isomorphism digest omits that `ω̄_X` is itself
  thunkable and linear.

None of these change any verdict.

## Verification state

- `verified`: `mmmm-classical-notions`, 30/30 CONFIRMED
  (digest-level), independent audit, 2026-07-29, by Claude (Opus 5),
  bound to `@ 8d9edc19055a` (the tarball's frontmatter `sha256`, a
  single-hash binding since this entry's canonical format is
  `latex-source` with no correction patch and no `secondary-sha256`).
- `verified`: `just resources-verify` reports 16 entries, 18 hashes,
  0 FATAL, and lists both `mmmm-classical-notions` and
  `munch-maccagnoni-duploids` as `vetted (Lane discretion exercised)`.
- `verified`: the width and prose-lint gates pass on every touched
  file (`resources/mmmm-classical-notions/README.md`,
  `resources/munch-maccagnoni-duploids/README.md`, `resources/README.md`,
  `notes/2026-07-25-two-lineages.md`). `bin/resources-verify` passes
  `bash -n` and runs clean end to end.
- `unverified`: the eight accuracy notes above and the [Q1]-[Q4]
  questions for authors from review-2 remain open, by design — none
  block the field, and none were resolved unprompted.
- `blocked`: nothing. The cycle this session's brief asked for is
  complete.

## Open questions and risks

1. The eight accuracy notes and review-2's four questions for authors
   are Lane's call, not a queued fix.
   `outputs/classical-notions-entry-audit.md` Section 6 and
   `outputs/.drafts/classical-notions-entry-review-2.md`'s Questions
   for Authors section hold the detail.
2. `resources/README.md` still has no provision for a per-entry
   measuring script like `munch-maccagnoni-duploids/pdf-scan.py` —
   raised again in the prior session's open questions, still
   unpicked-up, and out of scope here (`mmmm-classical-notions` is
   native LaTeX and needs no such script).
3. Nothing in this session's diff has been committed. `git status`
   shows a concurrent session's uncommitted `Cat.Logic` polarity work
   (`Test.SpikePolarityHLevel`, `Test.SpikePolaritySplit`,
   `Test.SpikePolarityTwist`, `CHANGELOG.md`, `src/Cat/Logic/TODO.md`)
   interleaved in the working tree throughout. This session touched
   none of those files, and its own CHANGELOG insertion sits
   immediately after the entry it completes, ahead of that session's
   already-appended entries.

## Next steps

1. Lane's call: commit this session's changes (six files plus the
   new audit report), and decide whether to act on any of the eight
   accuracy notes or the four questions for authors first.
2. Pick up `bin/resources-verify`'s remaining gap (the per-entry
   measuring-script provision) whenever an entry that needs one
   arrives.

## Artifacts

- Entries: `resources/mmmm-classical-notions/README.md` (30/30,
  vetted), `resources/munch-maccagnoni-duploids/README.md` (vetted,
  no digest change this session).
- Audit: `outputs/classical-notions-entry-audit.md` (new, untracked).
- Tooling: `bin/resources-verify` (N/M parsing), `resources/README.md`
  (Vetting contract amendment).
- Downstream fix: `notes/2026-07-25-two-lineages.md`.
- Prior session's brief: `notes/2026-07-29-duploid-papers-audit.md`.
- Commits: none this session: everything staged for Lane's review.
