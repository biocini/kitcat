# Session log — pipeline reliability, the port certification, and the audited shelf

**Date:** 2026-07-13, second session (branch `dev`; the morning
session closed at `bb03e1c` and its coda was amended into
`6665b31`).

**Scope:** Lane opened three escalating questions — should the
resources/ entries carry deeper summaries and had the ingestion
pipeline actually been designed; does the suite reproduce and
*verify* paper statements the way deep-research verifies its briefs,
and is the subagent system correctly implemented; and finally the
foundational one: is the pipeline reliable *independent of Lane's
review*? The session answered each in turn: the content-digest layer
and custody mechanics were built and the doctrine encoded; an
8-reviewer certification (4 against the original feynman suite at
`~/feynman-skills`, 4 internal coherence) certified the port and
produced the findings; and Lane's reliability reframe was made law —
the load-bearing gate for ingested knowledge is the human-free
statement audit, ratification is self-initiated discretion, and
mathematical truth terminates at the typechecker. The new audit mode
then ran for real over all six entries. No Agda changed.

**Status:** built + committed + verified (authoring lint with the
new drift canary, resources-verify with hashes/standing/consumers,
unidirectional sweep, sync, shellcheck — all green). Two commits:
`af73f50` (digest layer + custody + doctrine), `e1d9f62`
(reliability redesign + audited shelf + suite review applied). All
six entries stand `audited — load-bearing capable; Lane discretion
open`.

## 1. Work completed

1. **The pipeline critique (Lane's question 1).** Assessment: the
   entries navigated well (the maps) but digested thinly; acquisition
   was designed but custody was not (no mechanical hash verify, no
   re-fetch records, `.pdftext` anchors hostage to poppler versions,
   irreplaceable PDF-only sources on one machine). Lane ruled: Rijke
   digests focus the univalent-foundations core; custody mechanics
   approved; Lane owns backups; fetch URLs recorded (binding for
   PDFs); the directory's purpose = reference shelf + citation
   store; **information flows one way, resources out — a repository
   reference inside an entry is a defect**.
2. **The digest + custody build.** The format authority rewritten
   (purpose, unidirectional doctrine, Source-URL/re-fetch,
   `.pdftext` provenance, Content-digests layer, depth ∝ load);
   `bin/resources-verify` created; Rijke digested by a 22-lecture
   fan-out (Part II statement-level, I/III light); the entries
   brought to the bar by delegated ingest runs (URLs with honest
   vintage caveats, provenance, dep-arrows digests); the
   chiralities extraction normalized onto the flake-pinned
   pdftotext 26.06.0 (anchors held, spot-checked); unidirectional
   defects cleaned from rijke and dep-arrows. Commit `af73f50`.
3. **The certification review (Lane's question 2 + the sanity
   check).** Four internal coherence reviewers (investigation,
   production, ingestion, subagent-implementation) plus — after Lane
   supplied the original suite at `~/feynman-skills` — four
   port-fidelity certifiers reading both sides of all 13 prompt
   pairs and the architecture. Verdicts: **the translation is
   faithful** (13/13 FAITHFUL/FAITHFUL-WITH-NOTES/
   DIVERGENT-JUSTIFIED, zero DEFECT; every apparent drop resolved
   into bind-once factoring; the domain translations substantive;
   the port even fixed source bugs). **The subagent system is
   correctly implemented** (8/8 masters, both surfaces, no
   phantoms, no nested-dispatch assumptions). The one
   architecture-level loss: the source's **Feature scope**
   fight-for-its-life discipline had no port counterpart — the
   mechanism behind the overcomplication Lane kept having to police
   manually. Internal findings: one cross-cutting FATAL (the
   `[unvetted]` shedding rule drifted in ~8 prompt restatements),
   ~26 MAJOR clustering into bind-once drift, unpinned delegated
   outputs, missing skill handoffs, a resources-freshness seam, and
   mechanize as the least-audited `src/`-writing workflow.
4. **Lane's five rulings, applied.** The Layer scope section
   (fight-for-its-life, with retroactive passing records for
   `/prove` and `/hott`); the statement-verification design
   (ADOPT-WITH-CHANGES per the ingestion reviewer's sharpening);
   the subtractive coherence pass (the verify protocol promoted
   into the contract once, 15 prompts deduplicated to
   name-and-defer, the FATAL drift deleted everywhere, handoffs
   wired, mechanize's bracket closed, a lint canary added so
   shedding-rule drift now fails mechanically); the ratification
   spec; the flagged-drop dispositions.
5. **The reliability reframe (Lane's question 3, the session's
   pivot).** Lane: the pipeline's utility hinges on reliability
   whether or not Lane reviews; claims ought to be *formalizable*
   when they line up with the research interest (which they do by
   construction — ingest-on-firsthand-need); the real criterion is
   **useful, actionable, reliable for the concrete research
   interests**. GO on four changes: (1) the PROVISIONAL blocking
   rule retired — the load-bearing gate is the human-free statement
   audit (identity hash + adversarial fidelity), Lane's
   ratify/spot-audit/veto self-initiated, a veto retiring the entry
   and voiding dependents; (2) audit-as-hard-gate absolute; (3) the
   terminal criterion in the contract — verification of mathematics
   completes at the theorem ledger, whoever approved what; human
   gates are authorization and direction, never truth; (4)
   `resources-verify` reports each entry's standing and its
   consumers (an entry nothing consumes is flagged against the
   usefulness criterion).
6. **The audit mode, exercised end to end.** `verifier` gained the
   entry-statement-audit mode (per-statement CONFIRMED / CORRECTED
   / UNSUPPORTED; every verdict quotes fresh source text; records
   hash-bound). Five parallel audits covered all six entries:
   rijke 152/155 CONFIRMED (full Part II depth), dep-arrows 8/10,
   the conceptual four spot-checked 15/18. Zero FATAL, zero wrong
   anchors. Eight corrections applied verbatim (two dropped
   "locally small" hypotheses on the mechanization target; an
   invented `†` notation; a strengthened equivalence; coercion
   fixes; source errata now recorded rather than silently
   normalized) and the confirming re-pass ran 15/16 clean — its one
   miss an off-by-one anchor, fixed. Commit `e1d9f62`.

Movement against the morning log's preview: step 1 (ratify the
resources) was **superseded by the reliability redesign** — there is
no ratification queue to clear; the shelf is audited and Lane's
discretion is open. Steps 2 (mathematics) and 3 (workflow shakedown)
were not advanced as such — though this session was itself the
deepest shakedown yet (the audit mode, the verify protocol, and
sixteen delegated runs all exercised for real).

## 2. Strongest findings and decisions

- **The reliability doctrine (Lane, the session's ruling):** the
  load-bearing gate for ingested knowledge is the statement audit,
  never a signature; discretion is self-initiated; mathematical
  claims are CONJECTURED until machine-checked whoever signed what.
  VERIFIED encoded: `.agents/CLAUDE.md` (Epistemic labels,
  Ingestion), `resources/README.md` (Vetting spec),
  `docs/provenance.md`, `.agents/verifier.md`, and every prompt.
- **The port is certified faithful** (SOURCE-CHECKED against
  `~/feynman-skills`, both sides read in full): 13/13 pairs, 4/4
  architecture axes, zero DEFECT. The one loss — Feature scope —
  is restored as the contract's Layer scope section.
- **The audit mode catches exactly its target class** (VERIFIED by
  first exercise): dropped hypotheses on a mechanization target
  (dep-arrows Defs 2.8/4.8, "locally small"), notation leaking from
  our own memos into a source entry (the chiralities `†` —
  unidirectional contamination), strengthened claims
  (finite-types `:272`), and source typos, now recorded as errata.
- **T16 corrected and upgraded** (VERIFIED in `docs/gloss.md`):
  attribution fixed to the source's `(−)op`, and 📐⚠️ → 📐 — the
  identification's source claims are audit-verified at their
  anchors, the first ⚠️ lift under the new audit-keyed rule.
- **The consumed-by criterion is live** (VERIFIED,
  `resources-verify`): braided-dialogue and micrological-negation
  are consumed by nothing — honest usefulness flags awaiting the
  braid/ribbon thread, not defects.

## 3. Modules touched

No Agda. Context layer: `.agents/CLAUDE.md` (verify protocol,
Layer scope, reliability doctrine, hardened Delivery),
`.agents/{verifier,ingest,suite-maintainer}.md`, all 14 research
prompt bodies (the subtractive sweep + wiring), `resources/README.md`
+ all six entry READMEs (digests, URLs, provenance, audits, errata),
`docs/{provenance,gloss}.md`, `bin/{lint,resources-verify}`,
`justfile`, root `CLAUDE.md` (roster wording, tooling rows),
`.gitignore`/.DS_Store untracking.

## 4. Spikes

None (no Agda). The mathematics-arc `src/Test/` files are unchanged.

## 5. Theorem ledger

T16: `📐⚠️ → 📐`, attribution corrected to `(−)op` (see §2). The
maintenance rule now keys ⚠️ lifts on the backing entry's statement
audit covering the cited identification (audit-keyed, human-free),
with a Lane veto re-imposing ⚠️. T15 unchanged (awaits the Kelly
vendor + audit). Bijection 5↔5 unchanged.

## 6. Failures preserved

- **The `†` contamination** (caught by the audit): our chirality
  memo's notation had been written into the source entry as if the
  source's own. Salvage: the audit mode's fresh-quote requirement is
  what caught it; the unidirectional doctrine now has a live
  precedent naming the failure mode (memo → entry leakage).
- **The `[unvetted]` drift** (the review's one FATAL): a convention
  fixed at its home had survived in ~8 prompt restatements — the
  bind-once failure mode realized. Salvage: the restatements are
  deleted, and the `bin/lint` canary now fails the tree on any
  recurrence; the lesson is that a convention fix must be paired
  with a grep for its restatements, and where possible a canary.
- **The off-by-one anchor** (`funext.tex:110`→`:109`, caught by the
  confirming re-pass): even the corrections pass needs its
  confirming pass — the two-pass protocol is not ceremony.

## 7. Proposals

- **Lane's discretion sweep of the shelf** (self-initiated, no
  queue): six audited entries, spot-checkable in seconds each via
  anchor + quote + jump command; a `Vetted:` line or a veto per
  entry whenever Lane chooses.
- **The Kelly vendor** (paywalled; Lane's access) to lift T15 under
  the audit-keyed rule.
- **Residual MINORs** from the review, deliberately unapplied:
  uniformity of suffixed finals (draft/audit/critique vs the
  contract's unsuffixed scheme); eli5's dropped Tier-3 fan-out and
  durable summary artifact (keep-dropped per Lane's disposition,
  revisit if large-document needs bite); the bin/lint SC2016
  file-level disable (cosmetic).

## 8. Meta-process notes worth carrying

- **Ask "who secures this layer" before "who approves it."** The
  session's pivot came from Lane pressing on moral hazard until the
  design confessed its true gate. The durable form: for each
  pipeline stage, name the mechanism (machine, adversarial agent,
  human) that makes it reliable, and never let a human gate stand
  in for a mechanism the system can run itself.
- **Bind-once pays compound interest under redesign:** the
  reliability reframe landed mid-apply, and because the prompt sweep
  had just converted 15 prompts to name-and-defer, changing the
  contract's semantics changed all of theirs with zero additional
  edits.
- **Certify against the source with both sides read in full.** The
  port certification's value came from tracing each source mechanism
  through prompt → contract → HARNESS before grading; without that,
  most of the port would have misread as under-specified (three
  would-be false positives caught by one certifier).
- **A verifier's laziness is defeated by evidence requirements, not
  exhortation:** the fresh-source-quote rule made rubber-stamping
  physically impossible, and the audits' one systematic catch (the
  `†`) came directly from it.

## 9. Open questions and risks

- **The redesign is one session old**: audit-as-gate has run once
  (successfully); the discretion-not-queue semantics and the veto
  path are unexercised. First veto will test the
  voiding-of-dependents mechanics.
- **The audit depth knob is declared but uncalibrated**: spot-check
  breadth for background entries (3–4 statements) is a judgment
  call; a bad background entry could hide behind a lucky sample.
- **The mathematics remains the deferred priority** — three
  infrastructure sessions in a row.

## 10. Next steps

1. **Resume the mathematics** — roadmap targets 1–2 (faithful-
   stratum spike A1–A3, bimodule B1–B3) via `/prove`; memo A's kill
   criteria stand ready; the suite is now certified, coherent, and
   audit-hardened under it.
2. Lane's discretion sweep of the six audited entries, whenever
   chosen (no queue).
3. The Kelly vendor for T15, on Lane's access.
4. As they arise: the residual MINORs (§7).

## 11. Artifacts

- Committed: `af73f50`, `e1d9f62` (+ `6665b31` bridged by the
  morning log's coda).
- Tracked bridge: this log + `CHANGELOG.md`.
- Local working memory (gitignored): the four coherence reports
  (`notes/research/suite-review-*.md`), the four certification
  reports (`port-cert-*.md`), the six statement-audit reports
  (`stmt-audit-*.md`), and the Rijke digest staging. Sixteen
  delegated runs this session (5 digest writers, 3 ingest
  conformance runs, 8 reviewers/certifiers, 6 auditors, 1 sweep, 1
  corrections applier — some overlapping categories), all completed
  clean; no blocked capabilities; the one spend-limit interruption
  was in the prior session, not this one.
