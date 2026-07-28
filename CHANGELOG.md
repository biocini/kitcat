# Changelog — kitcat lab notebook

The chronological record of what changed in this repository: what
landed, what was verified, what failed, and what it superseded.
**Newest entry first.**

- **To resume work**, read the latest session log in
  [`notes/`](notes/) (`notes/<date>-<slug>.md`) — that is where
  current state, open questions, and next steps live.
- **To understand what happened**, read down this file.
- Standing targets and their gates: [`docs/roadmap.md`](docs/roadmap.md).

This is a lab notebook, not release notes: entries are dated,
concise, and honest about verification status (`verified` /
`unverified` / `blocked` / `inferred`).

---

## 2026-07-28 — the free balanced word model: the (D′) profile closes, refuted

**The oracle ran, `verified`** (`Test.SpikeBalancedWord`, 948
lines, recorded `just check`, zero obligations): the word model
of the bare framed point at (D′) strength — normal forms as
eventual-translation descriptors, cuts admissible, no quotient,
decidable equality, the full two-field instance. `associates
t⁻ t⁺ t⁺` is refuted, so generic `associates` is underivable at
(D′): the profile is exactly pre-duploid plus `mixed-assoc`, the
four unit laws, and the twist-flanked family. Bound for the
inhabitants line: `t⁻` not thunkable, `t⁺` not linear. The
winding conjecture holds: endo-homs ℤ-graded by the shift, the
double twist the `+1` generator, the obstruction exhibited as
one-sided invertibility (`refl` one way, refuted the other).
`inferred`, not proved: the model is the free object (empirical
certification 64/64 through six leaves,
`outputs/.notes/balanced-word-model-*`); initiality is line 9
items 2–3.

**Test distributed under spike zero, the archive got its
process, `verified`**: twelve chosen-edge spikes →
`Bb.NaiveVirtualGraph`; `Cat.Depreciated` (49) →
`Bb.CatsWithExplicitInterchange`, its twelve Test witnesses →
its `Gist` (gloss T21 now cites checked code); the Magmoid suite
→ `Bb.UnitalMagmoids`; `src/Bb/CLAUDE.md` process, READMEs,
CHANGELOGs, `Bb.index` — `src/Bb` 98 of 98, `src/Test` 9 of 9,
four removals with grounds, `CatData` resolved as a planning
name never adopted. Rulings executed: width 100 everywhere,
`check-tree` sweeps `.lagda*` (which surfaced the four
`Data.Thin` holes, pre-existing, still deferred). Whole tree:
319 of 323. Lint clean. No commits.

Next: line 9 item 2 (morphisms), the gloss entries for the cut
and the profile, the spike's promotion. Log:
[notes/2026-07-28-balanced-word-model.md](notes/2026-07-28-balanced-word-model.md).

## 2026-07-28 — Cat.Logic: line 2 settled, the Gist namespace, the balance dossier, custody

**Thunkability is data, `verified`** (`Cat.Logic.Gist.ThunkableSquare`,
checked): the length-4 square `compat` stated, and the circle model
refutes propositionality of `thunkable` and of the square-refined
closure in a full weak system. The freedom is a loop-space action and
uniform shifts are natural, so no coherence tower truncates it. The
same mechanism forecast the balance torsor, `verified` in
`Gist.ReadbackTorsor`: the contractible form of balance dies on the
phase fragment, so balance enters as structure. `Gist` created, nine
spikes vendored from `Test` with prefixes dropped.

**The programs written for cold starts**: the initial-model program
(line 9, the coherence conjecture, the word model), the
internal-language seam (CatColab RFC 0004, five lines), the balance
dossier under line 5 with positions (C), (D), (D′). Rulings: mode
separation is not a foundation, balance goes into `virtual-graph` as
structure, strict involution not required and kept anyway. The three
staged spike prompts ran in sibling sessions and ratified the (D′)
cut (entry below).

**Close-out, `verified`**: the handedness swap adjudicated stale
(executed in the rename pass, evidence at `Type:96`, `Base:504`),
gloss T32-T34 added and T31 corrected, the future/buffer register
compression fixed at its single live site. Custody: the entry renamed
`mmmm-classical-notions` (three authors, slug as four name words),
`kiselyov-having-effect` vendored PROVISIONAL, schema admits `html`,
`resources-verify` clean at 16 entries. `inferred`, not theorems: the
(D′)-hcategory convergence and the NbE reading of readback. Open: the
(D′) profile, oracle the free balanced word model.

Commits: `7f1cf05`, `5ca957e`, `920a21f`, `1003899`, `b43fd3c`.
Session log:
[notes/2026-07-28-thunkability-balance-turn.md](notes/2026-07-28-thunkability-balance-turn.md).

## 2026-07-28 — Cat.Logic: the balance spikes, the (D′) record cut, the Bb archive

**The record cut, `verified`** (`just check-tree`: `src/Cat` 69 of
69, `src/Test` 33 of 33, `src/Bb` 16 of 16; lint clean). Position
(D′) adopted. `virtual-graph` carries `readback`, the NbE
correctness equation stated unit-free. `is-deductive-system` is
contractible cuts plus invertibility, propositional fieldwise, and
`stable` demoted from tier to theorem (`axioms→stable`). At tier
strength the four unit laws and both cancellations are theorems
(`tower.balanced`): each tier centre reads back as the other
twist, two unital magmoids on one graph, offset by the double
twist. The strict op-involution survives the field (`opⱽ-invol`
stays `refl`). The weak stratum is frozen green as
`Bb.WeakDeductiveSystem` (16 modules, new `Bb.*` namespace). Five
free-framing Gist spikes retired to it under Lane's no-red ruling,
with every `docs/` citation re-pointed. Groundwork the same day,
`verified`: the readback torsor (`Gist.ReadbackTorsor`, balance
moduli is content), the (D) rehearsal (`Gist.BalancedBase`), and
the (D′) profile gate (`Gist.BalancedProfile`, two carrier kills).

**Failed forms, recorded:** an implicit carrier over unfolding
predicates breaks on any new record field (eta recovery is
complete only while every field occurs in the hypotheses) — ruled
explicit per `docs/guidelines/elaboration.md`, which gained the
eta paragraph. Where-scoped opens of parameterized modules and
inline prop-combinator chains in copattern clauses both leave
unsolved metas; the named, module-parameter forms check.

**Open:** the (D′) associates profile, both directions. The free
balanced word model is the oracle, merged with line 9 of the
`Cat.Logic` TODO. Next step: the word-model session at (D′)
strength. Commits `0065395`, `36ef6d7`. Session log:
[`notes/2026-07-28-balanced-record-cut.md`](notes/2026-07-28-balanced-record-cut.md).

## 2026-07-14 (tenth session) — THE REFACTOR downstream committed (5 stages); a context-layer process failure surfaced, hardening opened and handed to Lane

**THE REFACTOR core downstream — five stages, all `verified` (each
reviewer-PASS + analyzer-FAITHFUL, `just check-all` exit 0):**
Stage 1 `95cc0ef` (record moved `Cat.Codep.Base`→`Cat.Type`, renamed
`hcategory`→`category`; `Cat.Coherence` retired; Gloss excluded,
byte-identical); Stage 2 `d1202b8` (`Cat.Base` redesigned — named
`emb f · g` composite relation, `cast-path⁻¹`, η-idn one-liner, the old
`emb-ext`/`emb-noy` plumbing gone); P6 `30222d6` (Iso/Covariant/Yoneda
re-pointed); Monoidal `ff481d0` (tensor alignment — a named tensor
`_·_`, full `noy/yon`→`pre/post` sweep; Spike 1 DERIVED); Groupoid
`cda12a8` (`∞-groupoid` re-assembled over the structure+axioms bundle).

**A context-layer process failure surfaced — the session's pivotal
outcome.** The `Cat.Codep` NAMESPACE RETIREMENT — Lane's standing
intention across several prior sessions — was never in the plan of
record; the planning charter (`analyzer.md:151` "the `Cat.*` canon is
`Cat.Codep`") drove the new tree to RETAIN and thread through
`Cat.Codep`. Diagnosis: the Agda-pipeline agents (analyzer/coder/
reviewer) are overfit with repo content that belongs in the knowledge
base, read as settled so it forecloses inquiry. Drafted (uncommitted): a
**single-source-of-truth law** (`.agents/CLAUDE.md`) + **methodology
P7** — content-agnostic workflow layer, agents coordinate with the
knowledge base, redundancy is a gap-probe. A methodology review found
methodology itself violates P7. **Superseded:** the plan-of-record
assumption that `Cat.Codep` is retained; `docs/roadmap.md` re-gated
(uncommitted) — `Cat.Codep` retires (a core deliverable),
Braid/Twist/Hexagon are refactor-gated not Chir.

**Handed to Lane** (session closed to Lane's direction to take control):
the methodology revision + the `.agents/` corpus audit against it.
Uncommitted, awaiting Lane: `.agents/CLAUDE.md`, `.agents/methodology.md`,
`docs/roadmap.md`. No commit after `cda12a8`; `master` is the clean
fallback. Session log:
[`notes/session-logs/2026-07-14-1729-refactor-downstream-workflow-gap.md`](notes/session-logs/2026-07-14-1729-refactor-downstream-workflow-gap.md).

## 2026-07-14 (eighth session) — process-revision backlog (F2–F5) cleared; the session-log HHMM filename convention

Object: a process/context-layer session, no mathematics. Ratified and
applied the open process-revision backlog carried from the prior
session's review, and — at Lane's direction — added and retrofitted a
timestamp grain to the session-log filename convention. Session log:
[`notes/session-logs/2026-07-14-1048-process-revisions-log-timestamps.md`](notes/session-logs/2026-07-14-1048-process-revisions-log-timestamps.md).
Uncommitted at this writing — the whole changeset (7 modified files +
12 renames + memory-file reference fixes) awaits Lane's word.

**Applied — the F2–F5 process revisions** (Lane ratified all four).
`verified` (landed to tracked homes, `just lint authoring`/`changed`
clean, each diff checked against the run ledger): F3+F6 memo-fidelity
clause (`.agents/analyzer.md:68`); F2+F5b counted-inventory
live-command convention (`.agents/CLAUDE.md:217`); F4 repo-tooling
dispatch template (`.agents/CLAUDE.md:177`, no new agent — R1
preserved); F1-siblings dual-channel sweep (`.agents/ingest.md`,
`.agents/writer.md`). F5b's *structural* self-tracking prong remains
open and deprioritized (not subsumed — flagged by the close review).

**Landed — the session-log HHMM convention** (Lane's initiative).
Filenames gain a 4-digit 24-hour time between date and slug
(`<YYYY-MM-DD>-<HHMM>-<slug>`) so same-day logs order at a glance and
sort correctly for the session-open read. `verified`: the
authoritative rule + rationale in `.agents/CLAUDE.md` "Slugs and file
naming", format strings at three mirror sites (root `CLAUDE.md`,
`.agents/CLAUDE.md:85`, `.agents/prompts/log.md` ×2), and `/log` now
derives the stamp from the close-time wall clock. 12 existing logs
renamed with `git mv` and every reference repointed — `CHANGELOG.md`,
3 intra-log cross-refs, 9 memory files — all resolve; order verified
against the logs' own content cross-reference chain.

**Process review** (`/log` close): a low-friction validation session —
encode-at-ruling-time (the primary mode), the disjoint-file-ownership
concurrency split, and deviation-surfacing all ran as designed. Two
proposals for Lane's discretion: FP2 (ratify-now, a one-clause `/log`
template fix — license omitting an empty Proposals section), FP1/FP3
(next-session questions). Report:
[`notes/research/2026-07-14-process-revisions-log-timestamps-process-review.md`](notes/research/2026-07-14-process-revisions-log-timestamps-process-review.md).

**Roadmap:** no triggers — nothing landed, was added, or was re-gated;
`docs/roadmap.md` untouched.

## 2026-07-14 (seventh session) — the bimodule spike lands (→ Cat.Bimodule); the frontmatter convention; the output-handoff fix

Object: continued the roadmap (target 1, the bimodule record spike via
`/prove`) and, at Lane's direction, adopted a library-wide frontmatter
convention and fixed a context-layer output-handoff seam. Session log:
[`notes/session-logs/2026-07-14-0949-bimodule-frontmatter-harness.md`](notes/session-logs/2026-07-14-0949-bimodule-frontmatter-harness.md).
Committed at close (this `/log`).

**Landed — the bimodule spike (roadmap target 1).** The regular
representation embeds as a bimodule hom into the internal-hom
bimodule; left-equivariance `emb (a ⨾ f) ≡ a ⟩ emb f` derives over a
full hcategory residue-free (the load-bearing ingredient is base
`interchange` via `op-comp-path` + the definitional concreteness of
the actions — NOT op's `compose-contr`), the same bridge that walls
over the abstract stratum (T23); symmetrization is thereby free over a
full hcategory. `verified`: `Test.CodepBimodule-20260713-234309`, all
checks DERIVED over β, review bracket clean (accuracy PASS-WITH-FIXES /
citations both CONFIRMED / mechanical PASS, 0 Blocking; fresh
interface-deleted re-check exit 0 zero warnings). **Lane ruled: it
promotes to a `Cat.*` library home (`Cat.Bimodule`, post-refactor),
NOT to gloss** — no ledger entry, no `Gloss.*` cert (bijection
unchanged 8↔8); the spike is the recipe until THE REFACTOR opens the
foundation (roadmap target 2 updated to carry `Cat.Bimodule`).

**Landed — the frontmatter convention** (Lane's initiative). YAML
frontmatter on tracked `.lagda.md` sources: three registers
(frontmatter metadata / a `contents:` tagline / optional synopsis
prose), required core `author`/`date`(`YYYY-MM`)/`contents`, extensible
via tolerated unknown keys. Phase-1 tooling `verified`: `site/build.py`
frontmatter rendering (byline + `contents` lede + module title; strips
before the `---`→`<hr>` rule, no leak), the `bin/lint` tolerant
frontmatter canary, and a width **soft cap at 100** (bite-tested both
directions); a limited two-file pilot (`Core.Path.Base`, `Core.Type`,
both `just check` exit 0). The styleguide Opener + Rulings rewritten.
The tree-wide bulk sweep (29 old-header files + the header-less set) is
`deferred` to roadmap target 6.

**Landed — the output-handoff reconciliation** (`HARNESS.md` +
companions). A dispatched `verifier` read the file-based-handoff
contract and the harness's "final message = result" framing as
contradictory and dropped its file-write. Fixed: HARNESS.md now states
the dual-channel rule (write the file AND return a short completion
report; the message never substitutes for the artifact), with
name-and-defer companions in `.agents/CLAUDE.md` and
`.agents/verifier.md`. `verified`: `just lint authoring`/`changed`
green. (The process review found one sibling, `researcher.md:32-33`,
carrying the mirror phrasing; Lane ratified at close and it was
reworded to the dual-channel form.)

**Process.** All bimodule checks DERIVED — no walls preserved. The
accuracy review caught loose WHY-prose (S1, corrected at four sites);
the citation review confirmed both credits (Kelly SOURCE-CHECKED,
Petrakis reworded to a see-also register). Process review: 4 friction
points, 1 ratify-now (the `researcher.md` reword), the dominant
finding a validation — eight prior-review fixes ran clean.

## 2026-07-13 (sixth session) — the ratified promotions executed; the Gloss canonization standard

Object: the queued A-batch promotions landed, and Lane's in-session
rulings hardened Gloss into a canonization tier — formal
mathematical presentation, no operational vocabulary, custody-
disciplined re-freezes — applied to all eight certificates the same
session. Everything below is UNCOMMITTED at close (one working set,
19 modified + 2 new files), awaiting Lane's commit word.

**Landed.** **T22 — the tautological filling recovers the
representable core definitionally** (verified:
`Gloss.TautologicalFilling`, frozen from the substrate spike +
`Cat.Codep.Base` @ `dde1f57`; four killchecks now run with every
check-all). **T23 — agreement ⟺ interchange-2, both routes
walled** (verified: `Gloss.InterchangeCircularity`; walls re-pinned
live, raw residues frozen). **T24 — the pentagon engine at +0**
(inferred-from-machine-check: the tracked spike @ `dde1f57`, module
A3, not frozen; the Test/ citation is Lane's granted exception,
recorded in the entry). Bijection 8↔8. **The Gloss presentation
standard** (Lane, four rulings; `src/Gloss/CLAUDE.md`): no
operational vocabulary (ledger numbers, buzzwords, contentless
labels), no templated prose, outcomes-as-mathematics with
ledger-locators-follow-the-certificate, the Test/Gloss division of
labor ("if it needs operational phrasing to be comprehensible, it
isn't ready for Gloss"), and the comment-only re-freeze custody
spec. **The retrofit of all eight certificates** under it
(verified: code tokens byte-identical to their pins under
independent comment-stripped extraction; every comment delta
enumerated; `move-r` landed in `Core.Path.Base`; `sym-∙` uses
swapped to the existing `sym-distr`; `sym-sym` verified
refl-redundant and dropped; PropPinning dead code deleted; six
operational identifiers renamed to mathematical names, rename map
awaiting Lane's veto). **The `hcategory-structure` universe
refactor** (Lane's ruling: non-inferable `h` explicit; verified:
three modules edited, downstream proven zero-edit, T10 untouched;
the earned-by-inference principle in `docs/styleguide.md` +
root-contract cross-reference; the uniformity sweep found the
library otherwise already conformant, 1 violator in 92 records).
**The hotpath CLAUDE.md audit** (Lane-invoked; scores 89/95/84/92):
nine approved edits applied — sharpest catch: the ratified
re-freeze custody spec lived only in a gitignored ledger and is now
contract-encoded; `Trait.*`/`Meta.*` rows dropped by Lane's ruling.
**`Cat.Codep.Coherent`** swapped to the Core lemmas (Lane's GO).

**Verified.** `just check-all` exit 0 at zero warnings (the
mechanical gate's independent run pre-ruling-items; the final
delta's coder run + lead spot-check per Lane's directive);
mechanical gate PASS 0-Blocking over the 17+2 tree; citation review
both Petrakis credits CONFIRMED at source; two accuracy reviews
PASS-with-fixes, all fixes applied; freeze fidelity proven by
per-block byte-match with a coverage map (now the contract's
multi-certificate reading).

**Superseded.** The pre-standard certificate presentation (run
vocabulary, T-references, templated custody boilerplate); the
one-spike-one-certificate fidelity reading; `hcategory-structure`'s
implicit hom universe; the empty `Trait.*`/`Meta.*` namespace rows.

Session log:
[`notes/session-logs/2026-07-13-2309-promotions-gloss-standard.md`](notes/session-logs/2026-07-13-2309-promotions-gloss-standard.md)
(process review inside: 7 friction points — the
ruling-vs-in-flight-lag re-proposal leads — 4 validations).

## 2026-07-13 (fourth session) — T21 independence, the Kelly lift, the shelf's machine surface

Object: the evening cascade after the shakedown close — the
extract-agree question settled by theorem, the Kelly gap closed
end-to-end, and the workflow rulings Lane made in-session landed
as they were made.

**Landed.** **T21 — extract-agree is irreducible** (verified:
`Gloss.ExtractAgreeIndependence` @ `09f7155`, frozen from the
three-arm spike @ `dde1f57`, the first tracked-Test provenance):
the equivalence class over compose-contr, the Bool/xor
countermodel killing the whole admissible candidate space, both
honest walls fenced verbatim; boundary in three clauses; three
abstract propositional strata BY THEOREM; bijection 6↔6. The full
chain ran at certificate grade — accuracy PASS, the
code-citation review's first live run (verified: caught
under-scoped Petrakis credits four upstream layers missed;
corrections applied + mirrored + a dep-arrows map addendum),
mechanical gate PASS 0-Blocking. Function-valued res-inv adopted;
the `codep-invariance` optional overlay landed (verified: green).
**The Kelly arc** (verified end-to-end): the paywalled 1964
source vendored (public re-fetch URL found by Lane, verified
byte-identical), audited 46/46 at full depth with all 21
countermodel tables at 300 dpi, the OCR mandate's first exercise
(evaluate-and-reject — the honest branch), the tracked 21-hunk
render-verified correction patch with byte-identical
regeneration, confirming pass all-PASS — **T15's ⚠️ lifts**
(audit-keyed; no ⚠️ source-identifications remain), with Kelly's
three-distinct-proof-moves correction feeding the bimodule
spike's planning. **The shelf**: full ratification (seven Vetted
lines), custody frontmatter on all eight entries with
`resources-verify` reading it mechanically, the
OCR/correction-patch custody mandates, and the
fetch-skill/ingester-split direction recorded. **The workflow
cascade** (all Lane-ruled in-session): the promotion decision
block + P3's held-promotion clause; the /log
roadmap-reconciliation stage (exercised live at this close:
target 1 LANDED, the bimodule spike now leads the roadmap);
name-keyed log Contents; the eli5 fan-out tier restored; the
verifier write-boundary scoping; uniform author/date headers;
five of six styleguide splits ruled with sweeps scheduled.

**Failed / preserved.** Arm 3's two walls — now superseded by
their own theorem (the strongest "do not re-derive"); the
`--redo-ocr` rejection record (dual-layer duplication) as the
standing reason the OCR chain evaluates rather than assumes.

**Superseded.** T15's ⚠️ and the "engine of every derivation"
reading of Kelly; the entries' body-prose hash/fetch records (the
frontmatter is the machine surface); memo A's "exactly two
strata" (three, by theorem); roadmap target 1 (landed — the
bimodule spike leads).

Session log:
[`notes/session-logs/2026-07-13-1831-independence-kelly-shelf.md`](notes/session-logs/2026-07-13-1831-independence-kelly-shelf.md)
(the held list — the three stratum ledger entries — and the
process review's eight ratify-now proposals await Lane).

## 2026-07-13 (third session) — the /prove shakedown: faithful-stratum spike + the rulings cascade

Object: the first real end-to-end `/prove` run (roadmap target 1,
the faithful-stratum substrate spike) and a cascade of workflow
rulings applied same-session. First Agda since the coherence arc.

**Landed.** The spike
`src/Test/CodepFaithful-20260713-140913.lagda.md` (verified: green,
zero warnings; independently re-checked by the accuracy review and
the mechanical gate): **A1 DERIVED** — the tautological filling
recovers `hcategory` definitionally at every operation
(function-valued res-inv; `killcheck-dot = refl`), machine-checking
the Π-integral licence; **A2 the healthy wall** —
extraction-agreement ⟺ interchange-2 pinned both ways, the
derivation from the stratum alone STUCK at the pointwise-itc2
bridge (both routes transcribed; closing would have contradicted
T13), and at the filling itc2 IS the base interchange — the 3-cell
overlay is intrinsic; **A3 DERIVED at +0** — the pentagon engine
transplants unmodified over abstract res-inv. Two memo-A
refinements pinned: function-valued res-inv (the transport-refl
trap) and the new Layer C axiom `extract-agree` (refl at the
filling; abstract strata count 3). Ledger promotion HELD for Lane.
Also landed, per Lane's rulings: Test/ tracked with two-tier
semantics and the killchecks relocated to
`src/Test/CodepCoherentKillchecks.lagda.md` (All-wired tripwire;
verified by check-all); THE REFACTOR's end state explicit in the
roadmap; Public Module Style; dated plan/research artifacts with a
self-updating path-pattern lint canary (verified: bite-tested both
directions); the `/log` process-review stage + `process-reviewer`
agent (first run delivered 10 findings; the ratify-now set ratified
and applied same-session); the code-citation pipeline
(docs/provenance.md "Code citations" owns the spec; verifier gains
the code-citation-review mode; `/prove` stage 3 gains the
conditional review); `docs/styleguide.md` distilled from a Core.*
norms survey; and `resources/bentzen-naive-cubical/` ingested at
the rijke bar and audited 57/57 CONFIRMED (verified; 0 FATAL/MAJOR
across audit + confirming re-pass), wired into `/hott` and the
contract's new Foundational references. Tooling soundness fix:
`bin/resources-verify`'s audit detection line-anchored (a prose
mention could forge load-bearing standing — found live, verified
fixed).

**Failed / preserved.** A2(4) is the expected wall, preserved
in-spike with both obstructions; salvage: the pointwise-itc2
bridge is the stratum's one missing coupling datum.

**Superseded.** The killcheck-beside-the-proof placement
(Mechanization Discipline now points at the Test/ regression
tier); the undated plan/research artifact names; memo A's
path-valued res-inv; the "verbatim"-residue wording at six
surfaces (now defined once at the contract's oracle-contract
bullet).

Session log:
[`notes/session-logs/2026-07-13-1559-prove-shakedown-faithful-stratum.md`](notes/session-logs/2026-07-13-1559-prove-shakedown-faithful-stratum.md)
(carries the pre-registered bimodule-spike design for roadmap
target 2 and the held-for-Lane rulings list).

## 2026-07-13 (second session) — pipeline reliability and the audited shelf

Object: the resources/ pipeline and the research suite, taken from
"designed" to "certified and reliability-hardened". No Agda changed.

**Landed.** The content-digest layer (statement-level digests in the
source's own terms; Rijke digested at full Part II depth by a
22-lecture fan-out) and custody mechanics (`just resources-verify`:
hashes, entry standing, consumed-by; fetch URLs and `.pdftext`
provenance recorded per entry; the chiralities extraction normalized
onto the flake-pinned poppler). The directory's doctrine encoded:
reference shelf + citation store, **information flows from resources
out, never the reverse**. Then an 8-reviewer certification — four
against the original feynman suite at `~/feynman-skills`, four
internal — certified the port **faithful** (13/13 prompt pairs, 4/4
architecture axes, zero DEFECT) and the subagent system **correctly
implemented**, and its findings were applied: the contract's new
**Layer scope** section (the source's fight-for-its-life discipline
the port had dropped, with retroactive records for `/prove` and
`/hott`), the verify protocol promoted into the contract with 15
prompts deduplicated to name-and-defer, the drifted `[unvetted]`
restatement (the review's one FATAL) deleted everywhere with a lint
canary against recurrence, skill handoffs wired, and mechanize's
audit legs closed.

**The ruling that reframed the layer (Lane):** the pipeline must be
reliable whether or not Lane reviews it. The load-bearing gate for
ingested knowledge is now the **human-free statement audit**
(identity hash-verified + digests adversarially verified against the
source, fresh-quote evidence required, records hash-bound);
ratification/veto is Lane's self-initiated discretion, never a
pipeline queue; and mathematical claims stay CONJECTURED until
machine-checked, whoever approved what. First exercise: all six
entries audited (rijke 152/155 CONFIRMED, shelf-wide 175/183), eight
corrections applied — including two dropped "locally small"
hypotheses on the mechanization target and our own memo's `†`
notation contaminating a source entry — confirming re-pass clean,
source errata recorded. `docs/gloss.md` T16 re-attributed to the
source's `(−)op` and upgraded 📐⚠️ → 📐 under the new audit-keyed
rule.

`verified`: authoring lint (with canary), resources-verify (7 hashes,
0 FATAL; all six entries audited — load-bearing capable),
unidirectional sweep, sync, shellcheck. `superseded`: the
PROVISIONAL blocking rule ("no load-bearing citation on a
PROVISIONAL entry") and the ratification queue — replaced by
audit-as-gate with discretion open. Commits `af73f50`, `e1d9f62`.
Session log:
[`notes/session-logs/2026-07-13-1323-reliability-audited-shelf.md`](notes/session-logs/2026-07-13-1323-reliability-audited-shelf.md).

## 2026-07-13 — the fresh review and the shim/prompt surface split

Object: the hardened context layer, reviewed fresh and then
restructured. No Agda changed.

**Landed.** A fresh-eyes adversarial review (an 8-reviewer workflow
with per-finding adversarial verification against rulings R1–R13)
produced 58 verified findings; all 5 FATAL, 18 MAJOR, and the
relevant MINORs were fixed — R7 Rijke propagation, R2 ingest wiring,
R6 writer dispatch, the writer↔verifier citation contradiction, the
marker-shedding-on-ratification policy, a `bin/lint` soundness fix,
and a new `just lint changed` non-regression width gate for the
in-flight tree. The flake was fixed (`poppler_utils` → `poppler-utils`
would have broken it at HEAD) and pinned with `flake.lock` (agda
2.8.0 + curl/git/gnutar/perl). Six `resources/` entries were brought
to the R11 bar by delegated `ingest` runs (`petrakis-dep-arrows`
re-ingested as LaTeX-source canonical; a `mellies-dialogue-
chiralities` duplicate removed; line-anchored maps added).

Then the **workflow surface was re-expressed as the shim/prompt
split**: full workflow bodies are masters at `.agents/prompts/`, small
auto-trigger shims at `.agents/skills/kitcat/`, Claude Code reaches
them via two directory symlinks, pi reads `.agents/` directly, and
`.pi/prompts` + `.feynman/` were removed. `.agents/CLAUDE.md` was
established as the context-layer source of truth (the repo-user /
agent-facing division of labor made explicit) and now carries the
durable R1–R13 design decisions (R10 externalization).

**Verified.** authoring lint, `just sync`, the flake devshell build
(agda 2.8.0 + all layer tools), symlink integrity, tree independence
(reworded free of the external codename, re-checked), and the 18↔18
shim/prompt pairing — all green. `verified`: those checks.
`unverified`: `just check-all` under the flake was run once during the
shakedown (green) but no Agda changed since. `blocked`: the review's
verify phase hit the monthly spend limit once (Fable 5) and was
resumed on Opus 4.8 via `resumeFromRunId` with no findings lost.

**Superseded.** The 2026-07-11 R4 ruling that "dissolved the
shim/prompt indirection" (merged skill = command) is reversed by the
split above. The old per-skill three-symlink topology (54 symlinks)
is replaced by two directory symlinks.

Three commits: `1b50416` (the amended 2026-07-12 `/log` close, with
the external codename scrubbed from history — `dev` is local-only),
`38dcb3c` (apply-pass + surface redesign), `4c7d34b` (resolved
deferrals). Session log:
[`notes/session-logs/2026-07-13-0959-fresh-review-surface-split.md`](notes/session-logs/2026-07-13-0959-fresh-review-surface-split.md).
Six `resources/` entries remain PROVISIONAL pending ratification.

**Coda (same session, post-`/log`, commit `118cd4b`).** The Rijke
foundational entry (`resources/rijke-hott/`) was given a comprehensive
part-organized section map — 3 parts, 22 lectures, 247 line anchors at
`<lecture>.tex:LINE` (extracted per-lecture by a 22-agent workflow,
spot-checked against the source). A new `/hott` skill (the 19th) does
reference lookups grounded in that map: the standard formulation
SOURCE-CHECKED at the line, plus the kitcat cross-reference. Adding it
needed only the two masters — the directory symlinks surfaced it in
both harnesses — the first exercise of the new surface design.

## 2026-07-12 — the context-layer hardening arc

The feynman-derived context layer was audited against a studied
reference implementation of the same workflow discipline (like-with-
like, benched on this repo's own mathematics work) and hardened into
the library's own. Landed: `.agents/methodology.md` (the five working
principles stated as kitcat's own, with kitcat exemplars); the
bind-once cross-agent contract `.agents/CLAUDE.md` with the 18 skills
slimmed to defer to it; the roster restructured (`analyzer` = merged
theoretician + structural analyst; `coder`/`reviewer` renamed; new
`ingest`/`writer`/`suite-maintainer`); every working protocol
(spike/killcheck-refl/STUCK-wall/graduation) encoded from root
CLAUDE.md through the agents; a repo-owned `flake.nix` pinning the
latest stable Agda + ingestion tools; `just sync` gating on drift and
a new `just lint authoring` gate; the `/prove` pipeline command;
`resources/` given a canonical-source-format + `.pdftext` cache
convention; and the Rijke foundational entry (arXiv 2212.11082) as
the first live ingestion. The layer was corrected to full public
independence (no external-repo references; the methodology stands on
kitcat's own exemplars). notes/plans + notes/research became local
working memory. `verified`: authoring lint, spike-echo, symlink
integrity, tree independence, flake syntax. `unverified`: `just
check-all` under the flake (no Agda changed; last green `593f44a`).
`blocked`: five `resources/` entries + Rijke are PROVISIONAL pending
ratification. Superseded: the reboot's harness-mechanics claims
(re-audited against live builds) and the ad-hoc convention set.
Commits `f70cf94`, `6103b7f`, `202dfe7`, `9e4dfaf`. Session log:
[`notes/session-logs/2026-07-12-0313-context-layer-hardening.md`](notes/session-logs/2026-07-12-0313-context-layer-hardening.md).

## 2026-07-11 — the context-layer reboot (feynman port)

The repository's context management layer was rebooted: the
feynman.is research workflows were ported into a kitcat-owned,
harness-generic suite (`.agents/skills/kitcat/` — sixteen workflows
+ the HARNESS.md capability rosetta + the `spike-echo` diagnostic),
morally translated from ML research to mathematics research, and
**verified live on both harnesses** (Claude Code via `.claude/skills/`
symlinks; Pi natively plus typed `/name` adapters in `.pi/prompts/`
and `.feynman/prompts/`) — all from one canonical file per workflow.
Landed alongside: `docs/provenance.md` (binding honesty standards:
strict VERIFIED/SOURCE-CHECKED/CONJECTURED/`[unvetted]` labels, nine
practices, AI-contribution statement, date-stamped policy context);
the `resources/` vetted-sources convention (hash-verified vendored
documents, gitignored, records tracked); `docs/roadmap.md`;
CLAUDE.md rewritten as the cross-harness contract (root AGENTS.md
deleted — Pi prefers it over CLAUDE.md, verified in source); README
adapted (identity, provenance section, build; dead credits fixed).
The agent roster shipped with it: six definitions in `.agents/`
(`researcher` and `verifier` ported from the feynman originals;
four Agda specialists written fresh from the contract), registered
across all three harnesses by symlink — discovery verified live.
A six-lens whole-suite review (Opus) ran before staging; its 2
FATAL and 6 MAJOR findings are fixed (verified: the fixes are in
the staged tree). A nine-unit adversarial porcelain sweep then cut
the tooling that had no established place — `log-failure`/`Log/`,
the `deps` cluster, `benchmark`, `html-deploy`, `check-dirty`,
lint's imports check — fixed `mmv`'s unsafe rename sweep, and kept
the verified core (`check`/`check-all`, `sync`, `lint`
width+flags, `new`, `html`/`html-serve`, `stats`/`wip`);
`src/Test/` and `Stash/` are now gitignored scratch (Gloss the
upgrade path), and `All.lagda.md` no longer imports untracked
scratch (clean clones typecheck again — verified). Branch renamed
to `dev`.
**Superseded and retired to `.attic/`**: the pre-reboot context
layer — design.md, architecture.md, lexicon.md, styleguide.md,
coh.md, handoff.md (replaced by this file + the session-log chain +
the roadmap), six pre-reboot research memos, the four agent
definitions, and the docs-drift porcelain (recipe removed).
No Agda changed; `just check-all` not run (last green `593f44a`);
everything staged, commit pending Lane's go-ahead. Session log:
[`notes/session-logs/2026-07-11-1809-context-layer-reboot.md`](notes/session-logs/2026-07-11-1809-context-layer-reboot.md).

---

## 2026-07-11 — Cat.Codep: the coherence tower, closed by theorem

*Retroactively reconstructed 2026-07-12 (the mathematics work of the
day; the reboot above is the same day's later infrastructure
session).* The coherence overlay landed: `Cat.Codep.Coherent`
(θ-core derived, the gauge cluster collapsing to no fourth cell —
T6/T7/T19) and the Mac Lane `Triangle` (weak/full/mirror — T8), with
the parity theorem's Route-B upgrade on `Op` (T9). The theorem
ledger `docs/gloss.md` (T1–T20) and five frozen `Gloss.*`
certificates (EightFieldWall, PathGroupoid, PcomConservation,
PropPinning, TriangleFace23 — all `@ 9133396`) were committed
together in exact ledger↔certificate bijection. TEL-independence
(T11, S² countermodel + EightFieldWall), the op-involution regress
(T12), and the prop-pinning trichotomy (T13) established; the
interchange / Kelly / Melliès / binary-ancestor identifications
(T14–T17) recorded 📐. `verified` (`check-all` exit 0). This
session's commits `cfccb0b`, `9133396`, `2327309`, `593f44a`.
Session log:
[`notes/session-logs/2026-07-11-1200-codep-coherence-tower.md`](notes/session-logs/2026-07-11-1200-codep-coherence-tower.md).

## 2026-07-10 — Cat.Codep: hcategory reshape + the opposite category

*Retroactively reconstructed 2026-07-12.* The representable core was
reshaped to the flat-carrier `hcategory` record (collapsed tower),
and the opposite category `Cat.Codep.Op` landed with the parity
theorem — pre/post definitionally swapped, every mirror axiom
derivable (T9), giving strict self-duality of the category core
(T10); the eval axiom is self-mirror, so bias is chirality (T3). The
`Gloss.PcomConservation` (T20) and `PathGroupoid` (T18) spikes were
produced here (certificates frozen the next day, `2327309`).
`verified` (per-commit machine-checked). Commits `40e6743`,
`ed94308`, `97e3157`. Session log:
[`notes/session-logs/2026-07-10-1200-hcategory-reshape-opposite-category.md`](notes/session-logs/2026-07-10-1200-hcategory-reshape-opposite-category.md).

## 2026-07-09 — Cat.Codep: the representable trilayer

*Retroactively reconstructed 2026-07-12 (the overnight session; git-
local dates place it on the 9th).* The `Cat.Type`-style category was
rebuilt as `Cat.Codep`: a category presented through a representable
embedding `emb : hom ↪ composite`, the 4-field
representability-canonical carrier, and the `structure` / `axioms` /
`category` trilayer split (defeating a walking-arrow termination
class). Ancestors of ledger T1 (`Cat.Codep.Base`) and T4
(`Cat.Codep.Coherence`); the conservativity battery's path-groupoid
witness is the T18 ancestor. `verified` (five commits
machine-checked). Commits `dc52571`, `2376d5b`, `bd75cd1`,
`b5756c1`, `9bddaf8`. Session log:
[`notes/session-logs/2026-07-09-1200-codep-representable-trilayer.md`](notes/session-logs/2026-07-09-1200-codep-representable-trilayer.md).
