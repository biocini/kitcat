# Duploid source audit: statement-level, both vendored papers

Session log, 2026-07-28. Run via `/deepresearch`, plan approved by
Lane before evidence gathering. Slug `duploids-statement-audit`
throughout. Objective: `TODO.md`'s "The two duploid source audits,
statement-level. They gate every ledger citation that leans on those
sources" — audit `resources/mmmm-classical-notions` and
`resources/munch-maccagnoni-duploids` against their own vendored text,
and clear the `resources/README.md` `Statements verified:` gate for
both.

## What was done

1. Wrote the plan (`outputs/.plans/duploids-statement-audit.md`),
   scale decision: 2 `researcher` subagents in parallel, one per
   paper (a direct 2-item comparison/audit). Confirmed with Lane
   before dispatch.
2. T1 audited `mmmm-classical-notions`'s seven existing Content-digest
   claims against `article.tex` at their cited anchors.
3. T2 audited `munch-maccagnoni-duploids`'s 24 numbered statements
   (Definitions, Propositions, Remark, Theorem) against
   `duploids.pdftext`; this entry had no Content digests before this
   pass.
4. Drafted a synthesis report, ran the mandatory `verifier` pass, then
   the mandatory `reviewer` pass (strictly sequenced, never in the
   same dispatch).
5. Applied the reviewer's fixes as a full revised document
   (`outputs/.drafts/duploids-statement-audit-revised.md`), verified
   each fix landed on disk with `rg`/`grep` before delivery.
6. Delivered `outputs/duploids-statement-audit.md` +
   `outputs/duploids-statement-audit.provenance.md`.
7. Wrote `Statements verified:` fields into both
   `resources/mmmm-classical-notions/README.md` and
   `resources/munch-maccagnoni-duploids/README.md`, and added the
   missing Content digests section to the latter. Checked off
   `TODO.md`'s line 39.

## Strongest findings

- **Both entries CONFIRMED at digest level.** `mmmm-classical-notions`:
  7/7. `munch-maccagnoni-duploids`: 24/24, newly digested (no digests
  existed before this pass). All anchors in both entries' section
  maps/digests check out against the primary text; two minor
  anchor-precision drifts in `mmmm-classical-notions`'s pre-existing
  digest (a cited range that overshot by ~8 lines, a theorem anchor 3
  lines into its own body) were corrected in the entry.
- **Two source-level errors in the published papers themselves,
  confirmed against rendered PDF pages, not extraction artifacts:**
  `mmmm-classical-notions`'s composition-law diagram
  (`article.tex:1531`) literally renders codomain `M(X,Y)` where the
  surrounding prose requires `M(X,Z)` — the entry's own digest already
  gave the corrected form silently. Munch-Maccagnoni's Proposition 8
  (`duploids.pdftext:434`) states `wrap_N` is thunkable (correct, and
  matching the entry's section-map label), but its own proof concludes
  "Hence `wrap_N` is linear" — the derived equation is exactly
  Definition 2's thunkable shape, not the linear one. Confirmed a
  genuine published-text error by rendering `duploids.pdf` page 8
  directly and regenerating the extraction (`pdftotext 26.06.0`,
  byte-identical to the vendored `duploids.pdftext`).
- **The `verifier` pass caught a real overreach**: an early draft
  claimed both entries "clear the bar for load-bearing citation"
  before the `Statements verified:` field was actually written to
  either `README.md`. Downgraded before the reviewer ever saw it.
- **The `reviewer` pass found four MAJOR issues, all fixed and
  re-verified on disk:** the draft's citation inventory for
  Munch-Maccagnoni in `mmmm-classical-notions/article.tex` was wrong
  (miscounted, one citation mis-anchored by two lines) and missed the
  single most relevant sentence to the open cross-paper question
  (`article.tex:1817`, "a slight variant of"); the comparison space
  omitted Munch-Maccagnoni's Definition 7 (the equational form
  Definition 9 is stated as equivalent to); the Verification Record's
  blanket "no dead or stale anchors" claim was itself false against
  six of the draft's own citations; and the supporting research
  file's Proposition 8 digest independently mischaracterized the same
  equation as "linearity," which the review caught by direct render
  before this document did. Three MINOR issues (hash-scoping
  imprecision, an overstated cross-check-coverage claim, one drifted
  headline anchor) were fixed in the same revision pass.
- **Encoding/formatting trap, fixed**: `bin/resources-verify`
  line-anchors its `Statements verified:` match — a backtick-wrapped
  field (`` `Statements verified: ...` ``) does not match, and both
  entries reported "NOT audited" even after the field was written.
  House convention (`resources/rijke-hott/README.md` and others) is
  plain text starting the line, no backticks, no leading dash. Fixed
  in both entries; `just resources-verify` now reports both
  "audited — load-bearing capable; Lane discretion open."

## Failed or corrected approaches

- The first draft treated the cross-paper correspondence question
  (does `mmmm-classical-notions`'s duploid definition match
  Munch-Maccagnoni's?) as a two-way comparison against Definition 9
  alone, and asserted the citation supporting it was narrowly for "the
  adjunction theorem." Both were wrong: the paper cites
  Munch-Maccagnoni's *definition* directly (`article.tex:1682`,
  `l.1817`), not only the theorem, and Munch-Maccagnoni's paper itself
  presents two equivalent duploid definitions (Definition 7, Definition
  9), not one. The honest framing, reached only after the review pass,
  is a three-way comparison: mmmm's universal-property shift definition
  against Munch-Maccagnoni's own equational/invertible-maps pair.
- The provenance sidecar was initially written to the repository root
  rather than beside the final output; `.claude/rules/euler.md` states
  `<slug>.provenance.md` next to the final output, so it was moved to
  `outputs/duploids-statement-audit.provenance.md` before delivery.

## Open questions / next steps

- **`inferred`, not resolved**: whether `mmmm-classical-notions`'s
  duploid definition (a universal-property shift) is equivalent to
  either of Munch-Maccagnoni's two forms (Definition 7's equational
  form, Definition 9's invertible-maps form). `mmmm-classical-notions`
  itself concedes only "a slight variant of" (`article.tex:1817`), not
  identity. A future pass should target Definition 7 as the more
  likely bridge (its equational style is closer to a universal
  property than Definition 9's bare invertibility) and should first
  pin down which of the two definitions the "slight variant" phrase
  actually refers to.
- Whether Munch-Maccagnoni's Proposition 8 slip is a known published
  erratum was not investigated — only that it is genuinely in the
  paper's own text, not a vendoring or extraction problem.
- `src/Cat/Logic/TODO.md`'s "Settled: the duploid dictionary,
  statement-checked" section still frames the full statement audits as
  pending; it agrees with this audit on the four claims checked, but
  should be cross-referenced against `outputs/duploids-statement-audit.md`
  by whoever next touches that file. Out of this run's `resources/`-
  scoped work.

## Verification state

- `verified` (source-layer, this session's own re-checks, not kernel):
  all 7 `mmmm-classical-notions` digest claims and all 24
  `munch-maccagnoni-duploids` numbered-statement anchors, independently
  re-read against the vendored primary text by at least two of
  {researcher, verifier, reviewer} across the pipeline. The
  Proposition 8 and composition-diagram anomalies, confirmed against
  rendered PDF pages plus a regenerated `pdftotext` run, not just the
  extraction.
- `unverified`: the Q3 cross-paper definitional correspondence
  (explicitly flagged as open, not asserted, throughout).
- No kernel-layer check applies — this is a source-fidelity audit of
  prose/PDF research artifacts, not a formal-proof deliverable.
  `.euler/TOOLCHAIN.md` governs Agda kernel checks, not exercised this
  session.
- `just resources-verify`: 16 entries, 17 hashes verified, 0 missing,
  0 FATAL, both duploid entries now "audited — load-bearing capable."

## Artifacts

- Plan: `outputs/.plans/duploids-statement-audit.md`
- Research briefs: `outputs/.plans/duploids-statement-audit-T1.md`,
  `outputs/.plans/duploids-statement-audit-T2.md`
- Research notes: `outputs/.drafts/duploids-statement-audit-research-mmmm.md`,
  `outputs/.drafts/duploids-statement-audit-research-duploids.md`
- Draft, verified, review, revised:
  `outputs/.drafts/duploids-statement-audit-report-draft.md`,
  `-verified.md`, `-review.md`, `-revised.md`
- Final: `outputs/duploids-statement-audit.md`
- Provenance: `outputs/duploids-statement-audit.provenance.md`
- Entries touched: `resources/mmmm-classical-notions/README.md`,
  `resources/munch-maccagnoni-duploids/README.md`
- `TODO.md` line 39 checked off.
