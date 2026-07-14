# Session log — the /prove shakedown: faithful-stratum spike A1–A3, and the workflow-rulings cascade

**Date:** 2026-07-13, third session (branch `dev`; the second
session closed at `cf6d697`).

**Scope:** the first real end-to-end run of the `/prove` pipeline,
on roadmap target 1 — the faithful-stratum substrate spike, memo
A's pre-registered design. All three checks passed with no kill and
no escalation; the pipeline's four stages (analyzer prep → coder →
accuracy review → mechanical gate) each ran as designed and were
themselves under observation, per Lane's opening directive to
collect pipeline feedback. Interleaved with the run, a cascade of
Lane rulings hardened the layer: THE REFACTOR's end state made
explicit; Public Module Style codified; Test/ un-gitignored with
two-tier semantics (timestamped scratch / untimestamped regression
witnesses) and the killchecks relocated out of public modules onto
a tracked All-wired tripwire; plan and research artifacts
date-prefixed with a self-updating lint canary gating the path
patterns; a `/log` process-review stage with a new
`process-reviewer` roster agent; and the code-citation pipeline
(provenance spec, analyzer→coder credit handoff, verifier
code-citation mode, conditional review stage in `/prove`). The
close itself absorbed three more rulings: `docs/styleguide.md`
distilled from an analyzer norms survey of Core.*; the ingestion
of Bentzen's *Naive cubical type theory* (arXiv 1911.05844) at the
rijke-hott bar as the cubical-idiom companion, audited 57/57 and
wired into `/hott`; and Lane's ratification of the process
review's entire ratify-now set, applied same-session.

**Status:** built + verified + committed at close (Lane's word,
this `/log` invocation). Spike green at zero warnings; `just
check-all` green with the new killcheck tripwire wired; reviewer
mechanical gate PASS (0 Blocking / 2 Suggestions / 3 Nitpicks —
suggestions applied); authoring lint green including the new
path-pattern canary, bite-tested both directions;
`just resources-verify` 7 entries, 8 hashes, 0 FATAL, the bentzen
entry audited — load-bearing capable. Theorem-ledger promotion of
the spike results is HELD for Lane's rulings.

## 1. Work completed

1. **The `/prove` run** (`notes/plans/2026-07-13-faithful-stratum-spike.md`,
   the run ledger). Stage 1: analyzer prep memo with the three
   record skeletons, per-check plans, and two load-bearing
   refinements to memo A — res-inv must be FUNCTION-valued
   (`transport refl` is not definitionally the identity, so the
   path-valued form fails shape recovery at the operation level)
   and Layer C needs a new axiom `extract-agree : f ⨾ g ≡ f ⨾ᵇ g`
   (no `ctr` exists at Petrakis generality). Stage 2: the spike
   `src/Test/CodepFaithful-20260713-140913.lagda.md` (614 lines,
   green, zero warnings) — every memo statement closed first-try.
   Stage 3: accuracy review CONFIRMED all checks (records genuinely
   abstract; A3's +0 verified by line-for-line transplant diff);
   mechanical gate PASS. Stage 4: closed with promotion HELD.
   Verdicts: **A1 DERIVED** (the tautological filling recovers
   hcategory definitionally at every operation — res-inv := λ s → s,
   all codep laws refl, killcheck-dot pins stratum `_·_` ≡ Base
   `_·_` by refl); **A2 the healthy wall** (extraction-agreement ⟺
   interchange-2 pinned both ways; derivation from the stratum +
   ccL alone STUCK at the pointwise-itc2 bridge on both
   pre-registered routes; `cc-τ-blind` pins the representability
   field propositional; `itc2-taut` pins that at the filling itc2
   IS the base interchange — the honest-failure clause positively);
   **A3 DERIVED at +0** (·-comp absorbs all res-inv cost in two
   links; reindex-face, face₂₃, and bonus face₁₂ transplant from
   `Cat.Codep.Coherence` unmodified).
2. **Killcheck relocation** (Lane's no-probative-artifacts ruling):
   `killcheck-apPost`/`killcheck-apPre` moved from
   `Cat.Codep.Coherent` to the new durable regression witness
   `src/Test/CodepCoherentKillchecks.lagda.md`, wired into
   `src/All.lagda.md` by the sanctioned manual import (sync
   preserves it — verified live). The tripwire now fires with
   every `just check-all`.
3. **Test/ policy** (Lane): gitignore lifted — Test/ is tracked
   scratch, gate-exempt by name in `bin/lint` (not by ignore-file
   side effect); two-tier naming codified (timestamped
   `<Name>-<YYYYMMDD-HHMMSS>` scratch / untimestamped durable
   witnesses); root CLAUDE.md's Test rules, namespace row,
   Mechanization Discipline, and All conventions rewritten;
   `.agents/CLAUDE.md` and methodology exemplars aligned.
4. **THE REFACTOR made explicit** (Lane): `docs/roadmap.md` target
   3 now states the end state — conditional promotion of
   `Cat.Codep`: `hcategory` becomes the canonical category record,
   the four pre-refactor records rebased or retired, the downstream
   `Cat.*` tree re-founded with per-module dispositions decided
   when the refactor opens; root CLAUDE.md's pre-refactor bullet
   defers to it.
5. **Public Module Style** (Lane): new root CLAUDE.md section —
   API-first crafting modeled on Core.*; literate prose is sound
   documentation of the adjacent code block, never process
   narration; no testing/probing artifacts in public modules.
6. **Dated artifacts + the path canary** (Lane): plan and research
   artifacts are `<YYYY-MM-DD>-`-prefixed; the bind-once home and
   all ~21 prompt-body restatements swept; `bin/lint authoring`
   gained a self-updating canary (extracts the canonical patterns
   live from the contract's slug block, fail-loud anchors,
   bite-tested with planted drift both rows, restoration
   cmp-verified). This session's artifacts renamed to the dated
   forms.
7. **The `/log` process-review stage** (Lane): new
   `process-reviewer` roster agent (proposes, never applies;
   independence rationale recorded), `log.md` stage dispatching it
   with the session evidence, proposals surfaced to Lane tagged
   ratify-now / next-session; registered in both harnesses and
   picked up live by this session.
8. **The code-citation pipeline** (Lane): `docs/provenance.md`
   gains the owning "Code citations" section (house forms,
   anti-laundering rule, fidelity standard, review trigger);
   analyzer memos carry transcribable credit lines as coder
   obligations; coder Provenance made active; verifier gains the
   code-citation-review mode; `/prove` stage 3 is now accuracy →
   conditional citation review → mechanical gate; reviewer credit
   check narrowed to completeness + form. Motivating specimen: this
   run's finding S2 (Petrakis anchors laundered through the memo).

9. **`docs/styleguide.md`** (Lane): distilled from an analyzer
   norms survey of Core.* (31/134 files in full + tree-wide
   sweeps; 32 NORMs, graded) — ~24 conventions across module
   anatomy, naming (including the previously-uncodified
   qualified-API pattern), definitions/proofs, records,
   prose/comments, API surface; two honesty caveats (Core holds
   137/197 of the width baseline; ternary-first postdates most of
   Core's text — legacy chains are baseline, not precedent); six
   Core splits flagged as Open rulings, not legislated. Wired into
   the context-layer enumeration, the style law, Public Module
   Style, and the coder/reviewer definitions.
10. **The Bentzen ingestion** (Lane: rijke-hott treatment):
   `resources/bentzen-naive-cubical/` — arXiv 1911.05844 v2,
   canonical LaTeX source, hash-stable across two fetches,
   statement-level digests over the whole technical content.
   Statement audit at full depth: 57/57 digests + 4/4 source notes
   CONFIRMED, 0 FATAL / 0 MAJOR / 6 MINOR; corrections applied
   verbatim, confirming re-pass clean (its two accept-or-touch
   notes also applied); `Statements verified:` recorded
   @ 95621e6e. Wired: the contract's Foundational references, the
   `/hott` prompt + shim (cubical half; honest no-univalence
   scope), root CLAUDE.md References. Bonus: the ingest run found
   `bin/resources-verify`'s audit detector could be forged by a
   prose mention of the field name — fixed (line-anchored match),
   verified against all seven entries.
11. **The ratified process set, applied** (Lane ratified the
   process review's whole ratify-now set mid-close): prove.md
   GO-gate readings + spike mode + intro + reviewer-memo input;
   analyzer sketch-hygiene pass; coder refl-probe technique with
   the "verbatim"-definition home in the contract and five sites
   harmonized (+ two mechanize.md stragglers, lead-applied);
   log.md process-review input fix; methodology pipeline exemplar;
   and the `/hott`↔analyzer grounding standardization (new
   contract section "Foundational references"; seven surfaces
   name-and-defer — the sweep justifiedly extended to four more
   agent definitions carrying the same restatement).

Movement against the previous log's preview: step 1 (**resume the
mathematics**) — done as specified, roadmap target 1 spiked
end-to-end via `/prove`; step 2 (Lane's discretion sweep) and step
3 (the Kelly vendor) — untouched, both Lane-initiated; step 4
(residual MINORs) — untouched. Roadmap target 6's
memory-externalization concern was materially advanced from the
other side: this session's rulings all landed directly in tracked
homes.

## 2. Strongest findings and decisions

- **A1 — the Π-integral licence is machine-checked** (VERIFIED,
  `Test.CodepFaithful-20260713-140913`, `module taut`): the
  fixed-endpoint composite signature is exactly what a filling
  earns when its `res` reads only action-invariant data; the
  definitional accident is the signature of Π-integration, not an
  accident. Shape recovery holds at the operation level
  (`killcheck-dot = refl`).
- **A2 — the circularity is exact and constructive** (VERIFIED,
  same module, `module A2`): agreement of the two extractions and
  interchange-2 are inter-derivable over the two-sided stratum, and
  neither is reachable from the substrate + two-sided
  representability alone — both routes wall at the same
  pointwise-itc2 bridge, transcribed in-file. Had the wall closed
  it would contradict T13; it did not. The three coherence cells
  are intrinsic to wild two-sidedness (`itc2-taut`: at the filling,
  itc2 IS the base `interchange`).
- **A3 — the engine is independent of the definitional accident**
  (VERIFIED, same module, `module A3`; transplant identity checked
  line-for-line in the accuracy review): genuine fillings inherit
  the pentagon machinery unchanged.
- **`extract-agree` is load-bearing at the stratum** (the refl at
  the filling is VERIFIED; the *necessity* claim — no route to the
  extraction/composition bridge without `ctr` — is the analyzer's
  argument, CONJECTURED): abstract propositional-strata count
  becomes 3; the shadow theorem's "exactly two" survives at the
  filling only. Awaits Lane's ruling.
- **face₃₅'s Coherence lift is ctr-dependent** (VERIFIED as a
  reading of `Cat.Codep.Coherence` :187-188; the stratum
  consequence — that a stratum face₃₅ gates on the itc2 bridge —
  is CONJECTURED): rides A3's unchecked residue.
- **Lane's rulings this session** (all encoded in tracked homes,
  see §1): REFACTOR end state; Public Module Style; Test/ two-tier
  tracking; killchecks-never-in-public-modules; dated plan/research
  artifacts; Test naming; the process-review stage; the
  code-citation pipeline; the styleguide; the Bentzen
  companion-reference treatment; the `/hott`↔analyzer grounding
  standardization; the ratified process set.
- **The Bentzen entry is audit-clean at the rijke bar**
  (the audit protocol's record: 57/57 digests + 4/4 source notes
  CONFIRMED at full depth, fresh-quote evidence throughout;
  0 FATAL / 0 MAJOR across both passes; `Statements verified:`
  @ 95621e6e in the entry's Vetting). Scope honesty: the paper
  develops no univalence — recorded in the entry and every wiring
  surface.
- **`bin/resources-verify`'s audit detection was forgeable**
  (VERIFIED live by the ingest run: a prose mention of the field
  name conferred "audited — load-bearing capable" standing) —
  fixed by line-anchoring the match, re-verified against all
  seven entries.
- **Core.* norms, measured** (the survey,
  `notes/research/2026-07-13-core-styleguide-survey.md`): 32
  NORMs / 4 top-level TENDENCIES / 4 INCONSISTENCIES; the record
  discipline near-perfect (43/47 `no-eta-equality`, all four
  exceptions principled); Core holds 137/197 of the width
  baseline; ternary-first is practiced in coherence-facing work
  but predated by ~112 legacy binary chains.

## 3. Modules touched

Agda: `src/Test/CodepFaithful-20260713-140913.lagda.md` (new,
green, zero warnings); `src/Test/CodepCoherentKillchecks.lagda.md`
(new durable witness, green); `src/Cat/Codep/Coherent.lagda.md`
(killcheck section removed, green); `src/All.lagda.md` (manual
regression import). Whole library: `just check-all` exit 0.
Context layer (no Agda): root `CLAUDE.md`, `.agents/CLAUDE.md`
(incl. the new Foundational references section),
`.agents/{analyzer,coder,reviewer,verifier,researcher,writer,methodology}.md`,
`.agents/process-reviewer.md` (new, + harness symlinks),
`.agents/prompts/` (the dating sweep across ~12 bodies; log.md
stage + input fix; prove.md citation stage + GO-gate/spike-mode;
hott.md grounding + bentzen; mechanize.md wording),
`.agents/skills/kitcat/HARNESS.md` + `log/SKILL.md` +
`hott/SKILL.md`, `bin/lint` (Test exemption + path canary),
`bin/resources-verify` (line-anchored audit detection),
`.gitignore`, `docs/{roadmap,provenance}.md`, `docs/styleguide.md`
(new), `resources/bentzen-naive-cubical/` (new entry, audited).
The 25 legacy Test/ files enter tracking unchanged (triage
deferred, roadmap target 6).

## 4. Spikes

- `Test/CodepFaithful-20260713-140913` — the run's spike; verdicts
  A1 DERIVED / A2 healthy-wall / A3 +0; KEPT (now tracked);
  promotion to gloss.md/Gloss HELD for Lane (§7).
- `Test/CodepCoherentKillchecks` — not a spike: the first
  untimestamped durable regression witness, in All.
- No other spikes created; the legacy zoo's fates are unchanged.

## 5. Theorem ledger

No entries added or upgraded this session; bijection 5↔5
undisturbed (reviewer-verified). Three entry proposals are HELD
(§7). The enshrinement rule was weighed against the `/prove` hold:
with Test/ now tracked and committed, the spike evidence is
in-repo and durable; certificate-grade enshrinement awaits Lane's
extract-agree ruling, which shapes how the entries are worded.

## 6. Failures preserved

- **A2(4), the expected wall** (in-spike STUCK blocks + the run
  ledger): agreement from stratum + ccL alone. Both routes reduce
  to the same missing bridge — pointwise itc2, both directions
  transcribed content-exact from the typechecker's obstruction.
  Salvage (do not re-derive; build on): the stratum's ONE missing
  datum for two-sidedness is the pointwise-itc2 bridge; any future
  overlay (dHom⁽²⁾, compose-contr²) knows exactly what it must
  supply, and A2(1)/(2) are the reusable conversion lemmas between
  agreement form and interchange form.

## 7. Proposals

Held for Lane's discretion (none executed by this run):

- **gloss.md entries ×3** — (i) A1: the Π-integral licence /
  shape recovery; (ii) A2: agreement ⟺ interchange-2 + the
  constructive wall; (iii) A3: engine at +0 over abstract res-inv;
  each with the spike as evidence, Gloss freeze if ruled
  certificate-worthy.
- **`extract-agree` adoption** as Layer C's third axiom (and the
  shadow-theorem restatement: 3 abstract / 2 at filling).
- **Function-valued res-inv** as the stratum design.
- **The shadow theorem's cells half** — the natural next spike:
  recovery of the 3-cell overlay at exact types.
- **Byline ruling** for Test regression files (the killcheck file
  is the tier's exemplar; currently Gloss-style no-byline).
- **The styleguide's six Open rulings** (docs/styleguide.md):
  author headers; per-module `--no-sized-types`; universe-level
  names; fixity placement; the ternary-first conformance sweep;
  the WIP-probe cleanup path.
- The `/prove` prompt tweaks and other process items: §9 (the
  ratify-now set was ratified and applied mid-close).

## 8. Meta-process notes worth carrying

- **The annotated-sketch discipline paid in full**: every ★-line,
  killcheck, and derivation closed first-try at four checkpoints —
  the memo's definitional trace and link annotations were directly
  implementable. Conversely, the two defects it caught in memo-A
  prose (transport-refl, extract-agree) would have burned coder
  cycles if dispatched from prose alone.
- **Line-for-line transplant diffing** was the accuracy review's
  highest-value check per minute — the +0 claim reduced to textual
  identity.
- **Wall transcription needs a technique**: CLI agda prints no
  hole goals; force the missing bridge with `refl` and transcribe
  the UnequalTerms error, then revert (and mark the transcription
  content-exact, not verbatim, unless the raw error is pasted
  fenced).
- **Bind-once + a canary beats a swept convention**: the dating
  ruling was applied by one home edit + a mechanical sweep, and the
  new canary makes the next drift fail the tree instead of relying
  on a remembered grep.

## 9. Process review

Report:
`notes/research/2026-07-13-prove-shakedown-faithful-stratum-process-review.md`
(the `process-reviewer`'s first real run — dispatched natively; the
agent registered live mid-session). Ten friction points + one
validation + three layer-scope rejections. **Lane ratified the
entire ratify-now set mid-close and it was applied same-session**
(work-completed item 11); tags below record the reviewer's
dispositions with their post-ratification status.

Ratify-now (all APPLIED 2026-07-13):
- **F1** stage-1 GO gate satisfied by interpretation, twice
  (pre-registered design; autonomous deviations) → prove.md
  codifies both readings.
- **F2** spike-mode /prove implicit in a full-module prompt →
  prove.md Spike mode clause.
- **F4** two sketch-hygiene defect classes survived the analyzer
  (binder/level collision; beta-eta helper) → analyzer.md
  pre-delivery hygiene pass.
- **F5** wall transcription had no documented technique and
  "goal-verbatim" was unachievable as worded → coder.md refl-probe
  technique; "verbatim" defined once at the contract's
  oracle-contract bullet; five sites (+2 mechanize stragglers)
  harmonized.
- **F6** prove.md stage-3 intro counted "two passes" over three
  bullets → growth-proof rewording.
- **F7** reviewer's credit-completeness check presumed the
  analyzer memo without naming it → named required input.
- **F8** log.md's process-review brief named a CHANGELOG delta the
  workflow only produces later (the reviewer hit this itself) →
  stage hands what exists at that point.
- **V1** the analyzer-first rule earned its worked exemplar →
  methodology.md cites this run.
- **F3 (ratify-now half)** pre-registered designs in harness
  memory cost a transcription toll per run → memo B externalized
  into this log (§11's pre-registered design block), so roadmap
  target 2 opens on a tracked file.

Next-session (standing, Lane's discretion):
- **F3 (general)** the tracked-home question for design memos at
  large — roadmap target 6 owns it.
- **F9** log.md's numbered Contents charges a renumbering toll per
  insertion — named weakness, no fix determined.
- **F10** P3's same-session enshrinement met a Lane-held promotion
  and was resolved by interpretation — deserves a codified rule.

Rejected at the layer-scope gate (recorded): a design registry; a
mid-run policy-change clause; hole-goal tooling.

Late friction (post-report, feeds the next review): convention-set
enumerations drift when a convention is added (three places
enumerate, one got the new entry); no lint canary yet for
grounding-restatement drift; concurrent-edit coordination on root
CLAUDE.md worked by disjointness, not design — per-file ownership
notes in concurrent briefs should be the norm.

## 10. Open questions and risks

- **Is `extract-agree` genuinely irreducible at the stratum?** The
  necessity argument is analyzer-grade, not a countermodel. A
  subtler bridge (a pointed-fam substructure short of the rejected
  spine shape) has not been ruled out.
- **face₃₅ at the stratum** — plausibly gated on the itc2 bridge
  (ctr-dependence of its lift); untested, rides A3's residue with
  face₄₅/face₁₄.
- **The shadow theorem's cells half remains unspiked** — A1 +
  itc2-taut are its structure-and-interchange half only.
- **First-run sample size**: every pipeline conclusion in §8/§9
  rests on one `/prove` run; treat the generalizations accordingly.
- **The Test/ legacy zoo** enters tracking untriaged (deliberate;
  roadmap target 6 owns the sweep).

## 11. Next steps

1. **Lane's rulings** on the held items (§7): extract-agree, the
   three gloss entries, function-valued res-inv, the byline — plus
   the styleguide's six Open rulings (docs/styleguide.md, final
   section).
2. **Roadmap target 2** — the bimodule record spike (B1–B3) via
   `/prove`, opening on the pre-registered design below.
3. The next-session process items (§9): the design-memo
   tracked-home question, the Contents renumbering toll, the
   P3-vs-held-promotion rule.
4. Carried: Lane's discretion sweep of the audited shelf (now
   seven entries); the Kelly vendor for T15; the residual MINORs
   from the suite review.

### Pre-registered design: the bimodule spike B1–B3 (memo B,
### 2026-07-11 — externalized here from harness memory per F3)

The three cells are ONE FAMILY — Kelly's unit coherences for a
bimodule (absorb-lcoh = the left action-unit triangle, absorb-rcoh
= the right, its op-conjugate; couple-D₀ = the centre Kelly cell
λ_I = ρ_I on the trace `F x = hom x x`, op-fixed — why it is
self-dual). Kelly's derivation is a faithfulness/cancellation
argument foreclosed by wildness; the cells are its wild residue.

- **B1 — the bimodule record**: carrier `F` with two actions
  `⊳`/`⊲` + laws `⊳-idn`, `⊲-idn`, `⊳-assoc`, `⊲-assoc`, `middle`
  (the middle-interchange law). Lopsidedness flag for Lane at
  build time: one native action + interchange recovering the
  other (symmetrization as the layer's value-add) vs pre-native
  asymmetry.
- **B2 — the regular filling**: `emb` as the bimodule hom from
  the regular filling into the internal-hom bimodule,
  `emb f ((w,a),(v,b)) = (a ⊳ f) ⊲ b`; compose-contr read as "the
  regular representation is full onto composites".
- **B3 — emb-parity**: the parity/op story of that hom against
  the record's two actions.
- **B4 STRUCK — do not run**: memo B's "conjectured escape" (a
  canonical swap-derived T with `is-contr (fiber emb T)` freeing
  the cells) is REFUTED by the prop-pinning round's Argument 1
  (extract-to-empty; docs/gloss.md T13, `Gloss.PropPinning`).
- Standing memo-B claims for the run's analyzer to re-verify:
  middle pentagons (interchange-vs-assoc) free by same-fiber —
  conjectured-high-confidence, unspiked; the exact h-level split
  (free = coherences internal to `emb⁻¹(composite)`, h ≤ 1; paid
  = bridges to the unit-equivalence cancellation, h = 2); R2=R3 =
  the ⊳/⊲-assoc folding of `a;f` and `g;b` into single arrows;
  memo B leans β (independent intermediate tier, not stratum
  specialization) — α/β is Lane's call at the run's GO gate.
- Convergence note: the faithful stratum's two-sidedness IS a
  bimodule (this session's A2 wall names the exact missing
  coupling datum); the two spikes inform each other.

## 12. Artifacts

- Run ledger: `notes/plans/2026-07-13-faithful-stratum-spike.md`
  (the shakedown notes §§1–9 are its "Pipeline shakedown" section).
- Analyzer memo: `notes/research/2026-07-13-faithful-stratum-spike-prep.md`.
- Accuracy report: `notes/research/2026-07-13-faithful-stratum-spike-accuracy.md`.
- Process review: `notes/research/2026-07-13-prove-shakedown-faithful-stratum-process-review.md`.
- Styleguide survey: `notes/research/2026-07-13-core-styleguide-survey.md`
  (distilled into the tracked docs/styleguide.md).
- Bentzen audit: `notes/research/2026-07-13-bentzen-audit.md`
  (confirming re-pass reported inline — clean, no file per the
  dispatch); the durable record is the entry's Vetting section.
- Blocked capabilities: none. Degraded delegations: none — all
  roster agents present (the S1/S2 fixes and two mechanize
  wording stragglers were applied lead-owned under the
  trivial-work exception, recorded; the process-reviewer
  registered live mid-session and ran natively).
- Delegated runs this session: 15 (analyzer ×3 — prep, accuracy,
  styleguide survey; coder ×2 — spike, killcheck relocation;
  reviewer ×1; suite-maintainer ×5 — path canary, process-review
  stage, citation wiring, ratified set, /hott wiring; ingest ×1;
  verifier ×2 — full audit, confirming re-pass; process-reviewer
  ×1), all completed clean.
