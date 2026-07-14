# Session log — the evening cascade: T21 independence, the Kelly lift, and the shelf's machine surface

**Date:** 2026-07-13, fourth session (branch `dev`; the third
session — the /prove shakedown — closed at `79f63f2`, and this
session is the post-close cascade Lane kept extending; Lane
directed a full /log close for it).

**Scope:** three braided arcs. (1) The mathematics: Lane directed
a subtler-bridge search on `extract-agree` with a spike; the
analyzer found a countermodel instead of a wall, the three-arm
spike landed green, and the result froze same-session as **T21 /
`Gloss.ExtractAgreeIndependence`** — the first tracked-Test
provenance freeze, the first live exercise of the promotion
decision block, the code-citation review (which caught real
under-scoped credits on its first run), and the full
accuracy → citation → mechanical gate chain. Function-valued
res-inv was adopted with the `codep-invariance` overlay landed as
optional API. (2) The Kelly arc end-to-end: Lane supplied the
paywalled 1964 PDF; ingest (vintage fight recorded honestly),
full-depth audit (46 statements + 21 countermodel tables at
300 dpi), the OCR-mandate's first exercise (evaluate-and-reject,
the honest branch), the tracked 21-hunk render-verified
correction patch, the confirming pass, and **T15's ⚠️ lift** —
closing the methodology's standing cautionary example. (3) The
workflow cascade: Lane's rulings landed as they were made —
promotion prominence + P3's held-promotion clause, the /log
roadmap-reconciliation stage (exercised live at this close:
roadmap target 1 LANDED), name-keyed log Contents, the eli5
fan-out tier restored from the certification record, the
verifier's write-boundary scoping (Lane spotted the contradiction
live), the OCR/correction-patch custody mandates, the styleguide
rulings (five of six splits ruled; sweeps scheduled), uniform
author/date headers, full-shelf ratification, and the custody
frontmatter migration (all eight entries on the machine surface;
the fetch-skill/ingester-split direction recorded in the
roadmap).

**Status:** built + verified + committed. Six commits — five in
`63abb93`..`13a3df8` plus this close. All gates green at every
stage: check-all, lint (authoring + changed), resources-verify
(8 entries, 9 hashes, 0 FATAL), shellcheck. Ledger bijection
6↔6. Two ⚠️ lifts to date, both audit-keyed; none remain.

## Work completed

1. **The extract-agree independence arc** (ledger:
   `notes/plans/2026-07-13-extract-agree-bridge.md`). Analyzer
   search design → Lane GO → three-arm spike
   (`Test/CodepExtractAgree-20260713-171000`, green): Arm 1 the
   equivalence class {extract-agree, emb-hom, extract-agree-emb}
   over compose-contr; Arm 2 the Bool/xor collapsed countermodel
   satisfying every stratum field + emb-equivalence +
   identity-representability + orbit surjectivity + pointed-fam
   while refuting extract-agree at (false, true); Arm 3 both
   derivation routes STUCK at the naked bridge, fenced raw
   errors, ⊥-detector silent. Accuracy PASS (restatements
   byte-identical); citation review CORRECTED both Petrakis
   credits (Def 2.1 lacks the cofam half — §6 has it; Def 4.1
   lacks the codependent duals — the WG6 slides have them),
   applied + mirrored upstream + a dep-arrows map addendum;
   mechanical gate PASS 0-Blocking. Lane ruled the freeze:
   **T21** 🧪 `Gloss.ExtractAgreeIndependence` @ `09f7155`
   (frozen from the spike @ `dde1f57`), the honest boundary as
   three separate clauses, consequence: three abstract
   propositional strata BY THEOREM.
2. **Function-valued res-inv adopted** (Lane), with the
   invertibility upgrade landed as optional API:
   `Test/CodepFaithfulInvariance-20260713-163756` —
   `codep-invariance` overlay (prop-valued is-equiv fields,
   derived ≃-bundles, backward coercions, roundtrip laws; filling
   by `id-equiv`, killchecks pinning the backward coercions
   collapse to `λ s → s` at the filling; no `@0` on the fields —
   erasure would break the center extractions).
3. **The Kelly arc** (T15's gap, open since the reboot): Lane
   supplied the PDF (later located publicly — the commit-pinned
   GitHub raw URL re-fetched byte-identical, recorded as the
   fetch surface); ingest at mechanization depth (11 conditions,
   15 theorems, 5 proof digests with exact hypothesis lists, 21
   countermodel tables, from the PDF + 300 dpi renders); audit
   40/46 first pass, 6 CORRECTED (2 MAJOR both entry commentary —
   including the correction that Kelly uses THREE proof moves,
   not one cancellation principle: load-bearing for the bimodule
   spike's planning); Lane directed the OCR/correction pass:
   `ocrmypdf --redo-ocr` evaluated and REJECTED on evidence
   (dual-layer duplication poisons anchors), the embedded layer
   kept, the tracked 21-hunk patch (every hunk render-verified;
   twelve destroyed diagrams — the audit's "ten" undercounted —
   title block, de-interleaved theorems, Thm 10's dropped "(2)")
   with byte-identical regeneration proven; map re-anchored to
   the 242-line corrected extraction; confirming pass all-PASS
   (one MINOR, the printed "Rice." period — applied, keeping the
   transcription layer's zero-error record); **Statements
   verified: 46/46 @ a7f8d308**; **T15 📐⚠️ → 📐** under the
   audit-keyed rule, its derivation description refined to the
   source's three moves. Commit `13a3df8`.
4. **Full-shelf ratification** (Lane, "ratifying 4a"): `Vetted:`
   lines on all seven audited entries; PROVISIONAL markers
   retired as dated history (never deleted). Kelly's discretion
   open, honestly marked.
5. **The custody frontmatter migration** (Lane's ruling): flat
   YAML frontmatter (artifact, sha256, format, fetch-url +
   optional doi/version/fetched/inner and secondary hashes) as
   the machine-parseable surface on all eight entries;
   `resources-verify` reads it (fetch commands leave the bodies;
   the hash's home is frontmatter, bind-once); the
   fetch-skill/ingester-split direction recorded in roadmap
   target 5. The transition's named legacy fallback was added and
   then deleted the same evening once Kelly migrated.
6. **The OCR + correction-patch custody mandates** (Lane): the
   pinned `qpdf`/`ocrmypdf`/`pdftotext` chain mandatory for
   scans, evaluate-not-assume; the tracked correction patch
   (render-verified hunks, applied mechanically, regenerable
   byte-identically, corrections never write what a render does
   not show; patch changes void the audit field). Format
   authority + ingest contract.
7. **The workflow cascade** (each ruled by Lane in-session,
   commit `63abb93`): the promotion decision block in the
   contract (candidates lead every close; P3's held-promotion
   clause; log.md's held list); the /log roadmap-reconciliation
   stage (trigger definitions in the roadmap header; check
   per-session, edit trigger-gated; adversarial-sweep guard
   against cadence creep) — exercised live at this close: target
   1 LANDED, removed and folded into target 1's (new) preamble;
   the name-keyed order-canonical log Contents (F9); the eli5
   large-document fan-out tier reconstructed from the
   port-certification record with four designed-not-translated
   parameters flagged; the verifier write-boundary scoping (the
   report is the one write; never what it audits) after Lane
   spotted the live self-harmonization; styleguide rulings
   (author/date headers uniform across tracked src/ — applied to
   the five Gloss certificates, the killchecks, and the spikes,
   check-all green; no redundant per-module flags; u v w levels
   with ℓ reserved for I → Level; ternary-first sweep GO;
   WIP-probe cleanup GO; fixity split still open); addition-time
   worked records + the minimal-living-surfaces principle in the
   contract; `resources-verify`'s forgeable audit detection
   line-anchored (found live by the bentzen ingest).

## Strongest findings and decisions

- **T21 — extract-agree is irreducible** (VERIFIED,
  `Gloss.ExtractAgreeIndependence`, docs/gloss.md T21): no
  admissible weaker structure derives the extraction-composition
  bridge; one countermodel kills the entire candidate space; the
  weakening class is equivalent over compose-contr. Boundary
  honest in three clauses (decoding structures outside the space
  BY DESIGN — they are the bridge; the bimodule-faithfulness
  class excluded by argument only, upgrade registered). The
  structural ground: the ⨾ᵇ/emb interface in the stratum is
  EMPTY.
- **Kelly's derivations use three distinct proof moves**
  (SOURCE-CHECKED, the audited entry): K-stripping (Thm 7 only),
  direct iso-cancellation (Thm 6), naturality of c (Thms 8–10) —
  the entry's own "one engine" summary was the audit's sharpest
  commentary catch; plan the bimodule spike around three moves.
- **T15 lifted** (docs/gloss.md): the Kelly source-identification
  is SOURCE-CHECKED at its anchors; both ⚠️ lifts to date ran
  under the audit-keyed rule; none remain.
- **The citation review catches what four upstream layers
  missed** (VERIFIED by its first run): the under-scoped credits
  had survived the design memo, the green spike, the accuracy
  review, and the dispatching lead's own framing — only the
  fresh source read beyond the entry map's anchors caught them.
  Its lessons are now practice: audit against the source, never
  the dispatch's paraphrase; a credit resolving through
  unanchored content proposes the map addendum.
- **OCR is evaluated, never assumed** (the mandate's first
  exercise): `--redo-ocr` on the 1964 scan produced dual-layer
  duplication (1243 vs 497 lines) that would poison every anchor
  — the pinned chain's evaluate-and-reject branch is
  load-bearing, not ceremony.
- **Lane's rulings this session**: the subtler-bridge search
  directive; function-valued res-inv + optional is-equiv API;
  uniform bylines; name-keyed Contents; the freeze (names as-is;
  tracked-Test provenance pattern); full-shelf ratification;
  frontmatter custody; the OCR/patch mandates; eli5 tier
  restoration; addition-time records; the roadmap-reconciliation
  stage; the full-/log directive for this close.

## Modules touched

Agda: `src/Gloss/ExtractAgreeIndependence.lagda.md` (NEW
certificate, green, in All);
`src/Test/CodepExtractAgree-20260713-171000.lagda.md` (NEW spike,
green); `src/Test/CodepFaithfulInvariance-20260713-163756.lagda.md`
(NEW overlay, green); `src/Test/CodepFaithful-20260713-140913.lagda.md`
(credit-scope mirrors + byline); `src/All.lagda.md` (certificate
import via sync); bylines on the five prior Gloss certificates +
`Test/CodepCoherentKillchecks`. Whole library green (check-all,
multiple independent runs). Context layer: the commit-63abb93 set
(contract, methodology, prove/log/eli5 prompts + eli5 shim,
verifier/ingest definitions, styleguide, roadmap), plus
`bin/resources-verify` (frontmatter reader; forgery fix; legacy
case added and removed), `resources/README.md` (frontmatter
schema; OCR/patch mandates), all eight entry READMEs,
`docs/gloss.md` (T21, T15, maintenance note), `docs/roadmap.md`
(reconciliation: target 1 landed; targets renumbered; shelf
standing).

## Spikes

- `Test/CodepExtractAgree-20260713-171000` — three arms
  DERIVED/DERIVED/STUCK×2 as designed; ENSHRINED as T21 (forward
  pointer in-file); kept.
- `Test/CodepFaithfulInvariance-20260713-163756` — DERIVED; the
  optional-API overlay; kept (promotion candidate only if the
  certified stratum lands a real module).
- `Test/CodepFaithful-20260713-140913` — unchanged
  mathematically; credits corrected; its A1–A3 results' ledger
  promotions remain HELD (see Theorem ledger).

## Theorem ledger

- **T21 added** (🧪 `Gloss.ExtractAgreeIndependence`) — see Work
  completed 1. Bijection 6↔6 (reviewer-verified both directions).
- **T15**: 📐⚠️ → 📐 (audit-keyed; the second and last ⚠️ lift —
  none remain).
- **Held list** (carried until ruled, per the P3 clause): the
  three stratum entry candidates — (i) A1, the Π-integral
  licence/shape recovery; (ii) A2, agreement ⟺ interchange-2 +
  the constructive wall; (iii) A3, the engine at +0 over abstract
  res-inv — now unblocked by T21 (extract-agree's status is a
  theorem, so the entry wordings are stable); recommended for
  next session's opening decision block.

## Failures preserved

- Arm 3's two walls (in the spike and frozen in the certificate,
  fenced raw errors): both routes reduce to the naked bridge —
  the salvage is T21 itself (the wall is now a theorem, the
  strongest possible form of "do not re-derive").
- The `--redo-ocr` rejection record (the Kelly entry's chain
  record): dual-layer duplication as a standing reason the chain
  evaluates rather than assumes; salvage = the patch mechanism
  carried the correction load instead.

## Proposals

- The three stratum ledger entries (Held list above) — next
  session's opening decision block.
- Kelly's `Vetted:` line — Lane's open discretion on the eighth
  entry.
- The suite-maintainer audit-checklist bullet (absolute
  no-write constraints vs deliverable contracts) — proposed by
  the scoping run, awaiting Lane's word.
- The eli5 seven-section summary format — restore or keep the
  port's relocation (flagged by the tier restoration).
- `sync --fix` All placement (tail-append vs alphabetical
  cluster) — one-line ruling or a sync enhancement.
- The fence-extraction diff as a standing re-audit step in the
  Gloss promotion ritual (from the freeze run).
- `resources-verify --schema` mode (required-key completeness,
  currently unpoliced beyond artifact/sha256).

## Meta-process notes worth carrying

- **The pipeline's layers catch disjoint defect classes** — the
  evening's clearest lesson: accuracy verified the mathematics,
  the citation review alone caught provenance under-scoping, the
  mechanical gate alone caught the stale header pointer, and the
  confirming pass alone caught the printed-period digest
  mismatch. No layer was redundant; every one earned its place
  on its first real exercise.
- **Countermodels beat walls when the space is closable**: the
  directive asked for a spike expecting STUCK; the analyzer
  found the Bool/xor model and upgraded independence from
  "argued" to "machine-refuted" at ~60 lines. Ask whether the
  candidate space is small enough to kill wholesale before
  settling for a wall.
- **Custody is cheapest at ingest time**: the frontmatter
  migration of seven entries took one dispatch because every
  entry had recorded its data somewhere; the machine surface was
  a reshape, not a re-derivation.
- **Honest-outcome branches must be first-class**: the OCR
  mandate's evaluate-and-reject branch and the patch-over-OCR
  outcome were both the "failure" path, and both produced better
  custody than the intended path would have.

## Process review

Report:
`notes/research/2026-07-13-independence-kelly-shelf-process-review.md`
(the `process-reviewer`'s second run; its brief additionally
assessed the shakedown session's ratified fixes on their first
live exercises — all six ran as designed: the promotion decision
block in both shapes, the citation review catching what four
upstream layers missed, the refl-probe fenced-error standard, the
name-keyed Contents, the F8 brief fix exercised by this very
dispatch, and the roadmap-reconciliation stage with its
lead-interpreted first-run caveat). Awaiting Lane's ratification:

Ratify-now (8):
- **F1 — per-file ownership under dispatch** (the SECOND data
  point — a pattern begins): the lead's byline sweep mutated the
  spike mid-read by the bridge analyzer; anchor re-verification
  was paid twice downstream. One Delegation bullet in
  `.agents/CLAUDE.md`, covering lead edits, not just concurrent
  briefs.
- **F2 — coder divergence lists land in the run ledger**: the
  accuracy reviewer re-derived twelve deltas; the lead adopted
  ledger-pinning ad hoc at the freeze. `coder.md` + `prove.md`
  stage 2.
- **F3 — the code-citation confirming pass**: the mode letter
  mandates it unconditionally, the contract's verify protocol is
  FATAL-only, and the first live run followed the weaker reading
  — two MAJOR-corrected credits were never re-audited (the Kelly
  corrections got theirs the same session). Harmonize; Lane picks
  the direction.
- **F4 — the map-addendum practice onto a surface** (one line,
  `verifier.md`'s code-citation mode).
- **F5 — `sync --fix` placement** (tail-append vs alphabetical
  cluster; ruling or `bin/sync` enhancement).
- **F6 — the fence-extraction diff in the Gloss ritual**
  (`src/Gloss/CLAUDE.md`; one-freeze sample, honestly noted).
- **F7 — `resources-verify` polices required frontmatter keys in
  the default pass** (`fetch-url` is contract-load-bearing; a
  separate `--schema` mode rejected within the proposal).
- **F8 — removal records carry dropped parameter values
  verbatim** (`suite-maintainer.md`; from the eli5 restoration's
  four designed-not-translated knobs).

Next-session (1): **W1** — whether the bracket's accuracy half
binds Lane-directed Test-tier dispatches outside `/prove` (the
invariance overlay ran coder-only; no defect; a promotion-time
backstop exists).

Rejected at the layer-scope gate (4): concurrency tooling; a
mandatory coder process-notes appendix; a separate `--schema`
mode; a repo-wide retroactive credit re-audit.

Validation without proposal: the OCR evaluate-and-reject branch —
first exercise, the honest branch, better custody than the
intended path.

## Open questions and risks

- **The bimodule-faithfulness exclusion is argument-grade** (T21
  boundary clause iii): the registered second countermodel is
  unbuilt; if the bimodule spike makes that class load-bearing,
  build it.
- **The tracked-Test provenance pattern is one freeze old**: the
  certificate's `@ dde1f57` pins survive history rewrites only as
  well as the branch does; the pattern assumes append-only dev.
- **The frontmatter schema is unpoliced beyond hashes** (the
  --schema proposal).
- **Roadmap reconciliation ran lead-interpreted this first time**
  (the stage's prose was followed, but by the same lead who wrote
  it hours earlier; an independent session is the real test).

## Next steps

1. **The opening decision block**: the three stratum ledger
   entries (A1/A2/A3), Kelly's Vetted line, and the small
   proposals above.
2. **Roadmap target 1 — the bimodule spike (B1–B3)** via /prove,
   from the prove-shakedown log's pre-registered design block;
   plan around Kelly's three proof moves; the A2 wall
   (pointwise-itc2) is the convergence question; α/β and
   lopsidedness are the GO-gate calls.
3. As capacity allows: the styleguide conformance sweeps; the
   fetch skill + ingester split (roadmap target 5).
4. Carried: the next-session process items from the shakedown
   review (the design-memo home question is roadmap-recorded;
   F9/F10 landed this evening).

## Artifacts

- Run ledgers: `notes/plans/2026-07-13-extract-agree-bridge.md`,
  `notes/plans/2026-07-13-faithful-stratum-spike.md` (post-close
  sections).
- Research: the bridge design, accuracy, citations reports
  (`notes/research/2026-07-13-extract-agree-*.md`); the Kelly
  audit (`notes/research/2026-07-13-kelly-audit.md`; confirming
  pass reported inline, all-PASS); the process review (above).
- Commits: `63abb93`, `5a98473`, `dde1f57`, `09f7155`, `13a3df8`,
  plus this close.
- Blocked capabilities: none. Degraded delegations: none — 17
  delegated runs this session, all completed clean: analyzer ×2
  (bridge design, accuracy), coder ×3 (independence spike,
  invariance overlay, freeze), verifier ×3 (citation review,
  Kelly audit, Kelly confirming pass), reviewer ×1 (mechanical
  gate), ingest ×2 (Kelly ingest, Kelly re-extraction),
  suite-maintainer ×5 (promotion-block/P3 + name-keyed Contents
  rounds, verifier scoping, eli5 tier, roadmap-reconciliation
  stage, frontmatter migration), process-reviewer ×1. The lead
  applied all corrections per protocol.
