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

Cite a commit hash only when a session made more than one commit and
the hash disambiguates which one did what. A single-commit session
never cites its own hash: the entry is written before that commit
exists, so citing it would force a second, hash-only commit just to
close the loop. `git log --grep=<slug>` or the entry's date recovers
it in one step when needed.

---

## 2026-07-29 — session close: the polarity collapse, reviewed and vendored

**Session log:** [`notes/2026-07-29-polarity-collapse-and-vendor.md`](notes/2026-07-29-polarity-collapse-and-vendor.md).

Closes the session that produced the five entries below (h-level,
twist-condition, collapse, operator-carrier, readback-shift), their
three-reviewer adversarial audit, and the vendor pass. Adds one thing
not yet in an entry of its own: a staleness diagnosis in
`src/Cat/Logic/TODO.md`. A new "Stale in light of the polarity
collapse" block, plus pointers from investigation items 4 through 7.
Lines 6 (shifts as representability) and 7 (the reflection theorem, a
deductive system's polarized, balanced core is a duploid) are
`blocked`, not merely open. Balance is exactly the strength at which
`PolarityCollapse` proves polarity collapses, so no polarized-and-
balanced core exists to build a duploid from. Item 4's "subcategories"
line closes the same way. Items 1, 2, 3, 5, 8, 9 stand unaffected. The
earlier RULED note against primitive polarity rested on a clause now
known false. Reopening it is Lane's call, recorded for the next
session rather than decided here.

`verified`: all five promoted modules check individually, plus
`just check-tree src/Cat/Logic/Gist` (14 modules) and the whole-library
`just check-tree`, which is clean except six pre-existing failures
unrelated to this session (`Core.Coherence.Paths`,
`Core.Path.Coherence`, `Data.Thin.{Category,Cover,Properties,
Separated}`). A stale import and unrelated unsolved metas cause them;
none of the affected files were touched. `just lint changed` clean,
zero holes or postulates across the session's modules. `blocked`:
`readback-square` in general. `inferred`, not `verified`: the
staleness diagnosis is a consequence-drawing pass over already-
verified results, not a new checker run.

---

## 2026-07-29 — the polarity chain promoted into Cat.Logic.Gist

**Five modules are live**: `Cat.Logic.Gist.PolarityHLevel`,
`Cat.Logic.Gist.PolarityTwist`, `Cat.Logic.Gist.PolarityCollapse`,
`Cat.Logic.Gist.OperatorCarrier`, `Cat.Logic.Gist.ReadbackShift`.
Promoted from their `Test.SpikeXxx` originals, `just mv` in
dependency order, one module checked before the next rename. Slug
`vendor-polarity-gists`, brief at
`outputs/.plans/vendor-polarity-gists.md`.

Three adversarial reviews covered the first three spikes. They found
the underlying mathematics sound, one wrong citation, and several
overclaiming or underclaiming prose passages. The promotion applied
the fix list alongside each rename.

`PolarityHLevel`: the `positive`/`negative` citation no longer names
Definition 1 of `resources/munch-maccagnoni-duploids`, a primitive
partition map and not this transcription. It now names Clairambault
and Munch-Maccagnoni's Polarity definition, *Duploid situations in
concurrent games* (GaLoP XII, 2017), at
`resources/mmmm-classical-notions/article.tex:1694-1700`. `shiftP`
and `shiftN` renamed `shift⁺` and `shift⁻`, the house convention for
hand-marked names.

`PolarityTwist`: `positive-from-unit` and `negative-from-unit`
localized to the one object their proof terms actually use. Two new
lemmas, `positive-empty` and `negative-empty`, make the word model's
vacuous two-edge check machine-checked. `linear-refuted` and
`thunkable-refuted` join the import list. A new sentence states the
`gen-diag` scope limit: the generated-carrier tier is vacuous off a
loop edge. The closing prose notes the `positive`/`negative`
duplication against `PolarityHLevel` and leaves it for a later pass.

`PolarityCollapse`: a new `from-deductive-system` module restates
both collapse directions at the bundled `is-deductive-system` record,
not only at the raw tiers. "One property"/"one predicate" now reads
"logically equivalent" (the module proves a two-way implication, not
identity of the two predicates). `split-refuted` and
`split-refuted-dual` had byte-identical signatures despite naming two
distinct facts. Sharper replacements, `no-positive-split` and
`no-negative-split`, each use only the two hypotheses they need.
"Category" now reads "unital magmoid", this repository's term for
the same untruncated-hom structure. Two sentences overclaiming
necessity now match the module's own "It could instead drop..."
qualifier. The scaffolding simplification the reviews noted
(`centre`, `cross⁻-into`, and `twist⁻-centre` are provably
unnecessary) is deliberately not attempted this pass.

`OperatorCarrier` and `ReadbackShift`: rename only, completed after
the review batch. Their imports of `PolarityTwist` and
`OperatorCarrier` came through the `just mv` sweep correctly.

Ledger updated (`src/Cat/Logic/TODO.md`). Every `Test.SpikeXxx`
reference now reads `Cat.Logic.Gist.Xxx`. The h-level block's
citation matches the module's fix, and the twist block gained the
duplication note. `outputs/.plans/polarity-hlevel.md` corrected for
consistency.

`verified`: `just check` on each of the five modules individually,
zero warnings, no holes, no postulates. `just check-tree
src/Cat/Logic/Gist` clean, 14 modules. `just check-tree` over the
whole library reports the same six pre-existing failures as before
this session, under `Data.Thin` and `Core.Coherence`/`Core.Path`.
The causes are a stale `Cat.Type` import and unrelated unsolved
metas, neither touched here. `just lint changed` passes. `rg -n
"Test\.Spike(PolarityHLevel|PolarityTwist|PolarityCollapse|OperatorCarrier|ReadbackShift)"
src/` returns nothing.

## 2026-07-29 — the readback torsor stops at the presentation

**`Test.SpikeReadbackShift` is live** (slug `readback-square`, brief
at `outputs/.plans/readback-square.md`). The carrier spike below left
`readback-square` open. It named `Cat.Logic.Gist.ReadbackTorsor` as
the only instrument that varies a readback over wild homs. This spike
measures what that instrument reaches. It refutes nothing. At the
circle model the square holds, at both readbacks.

The readback is free structure. `is-deductive-system` names `reflect`
and the two twists, and never the readback. So `retune-axioms` carries
every tier's witness across a change of readback, with no proof. That
gives two deductive systems over the circle model which differ in the
readback alone, `rb₀` and its one-winding shift `rb₁`.

The presentation does not follow. Six components return on the nose,
and `assoc` returns up to a path through stability. `cross-pivot` and
`unitr` each gain one winding and do not return
(`cross-pivot-differs`, `unitr-field-differs`). The carrier returns on
the nose, so no identification of the two presentations holds the
carrier fixed. There is no refuting pair.

The square's two sides move together. Every word the round trip writes
at the axiom is a loop at `base`, and that loop space is commutative.
The shift is then a signed count of readback occurrences. The derived
readback gains two windings and one uncomputed loop `κ₀`, and the
reflection square against the field gains the same. `square→` and
`square←` transfer the square across the retuning.

At the circle model the square reduces to the triviality of the mixed
associator at the axiom. That holds, because the model reads the
positive cut witness through `mult-assoc base`. So `square₀` and
`square₁` hold, and `round-graph` closes the graph round trip at each
readback. No truncation enters: the circle is a groupoid and not a
set, so the square is a proposition and not a triviality.

Ledger updated (`src/Cat/Logic/TODO.md`, the readback-torsor block).
`verified` (`just check Test.SpikeReadbackShift`, 2026-07-29, zero
warnings, no holes, no postulates). Next: `readback-square` in
general, which needs the same cancellation without a commutative loop
space, and without a cut witness that degenerates at the axiom.

## 2026-07-29 — a deductive system as a category with one operator

**`Test.SpikeOperatorCarrier` is live** (slug
`category-operator-presentation`, brief at
`outputs/.plans/category-operator-presentation.md`). The collapse
spike below rewrote every negative cut through one operator. This
spike states the carrier that rewriting leaves, and measures how far
it reaches. The structure of a deductive system is a wild category
with one endo-operator. The axioms are not.

`presentation` is the record: `unit`, `_⨾_`, `assoc`, `unitl`,
`unitr`, the operator `cross`, a second endo-edge family `pivot`, and
three laws. Each law is a theorem of a deductive system (`pair⁻`,
`cut⁻-cross` against `unitr⁻`, `cross⁻-cut⁺`), and the backward
direction consumes every field. `op-cross` shows `opᴰ` exchanges the
two readings of the operator on the nose.

Backward, `carrier.graph` is a virtual graph with readback and no
hypothesis: `reflect f γ` is the flanked word `(cross s ⨾ f) ⨾ k`.
All four tier fibers are inhabited, and readback forces each fiber's
edge. What is missing is `residue`: stability, plus one
propositionality demand per invertibility fiber. `hom-sets→residue`
discharges it, so a presentation with hom sets is a full deductive
system. Over wild homs the residue stands open, neither derived nor
refuted.

Both round trips are componentwise, and two components return only up
to a path. `cross` returns up to `unitr`, and `reflect` up to
`round-reflect`. The record-level identity of graphs is exactly one
square, `readback-square`, from which `round-graph` and `round-system`
derive both records.

The dictionary reads `associates`, `thunkable` and `linear` as the
commutation defect of the operator. Polarity becomes
representability: the operator on `hom(-, x)` is right multiplication
by one edge, forced to be `cross⁻ (twist⁺ x)`.

Ledger updated (`src/Cat/Logic/TODO.md`, the carrier block).
`verified` (`just check Test.SpikeOperatorCarrier`, 2026-07-29, zero
warnings, no holes, no postulates). Next: the readback square, and
whether the residue admits a countermodel over wild homs.

## 2026-07-29 — polarity does not split at full strength

**`Test.SpikePolarityCollapse` is live** (slug
`polarity-distinguishing-model`, brief at
`outputs/.plans/polarity-distinguishing-model.md`). The brief asked
for a deductive system with one positive object and one negative
object. No such system exists. The two twist conditions at an object
are equivalent. So `positive` and `negative` are one predicate, and no
carrier separates them.

The proof reads the framing as a category plus one operator. `assoc⁺`
with its two unit laws makes the edges a category whose identity is
`twist⁺`. `mixed-assoc` with `unitl⁺` rewrites `f ⨾⁻ g` as `(f ⨾⁻
twist⁺) ⨾⁺ g` (`cut⁻-cross`). A linear `twist⁺ x` pins that operator
to one positive cut against a right inverse of `twist⁻ x`. The
operator then passes through every positive cut at `x`, which is a
thunkable `twist⁻ x` (`from-linear`).

`from-thunkable` runs the dual. `split-refuted` closes the brief's
four clauses, and `word-check` derives each of the word model's two
refutations from the other.

A finite-model search preceded the proof and agrees with it
(`outputs/.notes/polarity-distinguishing-model-search.py`). Take the
two-object carrier whose hom sets are its two twists, with no edge
back from the second object. Exactly four deductive systems exist
there. All four are group-like, and both polarities hold at both
objects in each one.

Ledger updated (`src/Cat/Logic/TODO.md`, collapse
block + line 4). `verified` (`just check Test.SpikePolarityCollapse`,
2026-07-29, zero warnings, no holes, no postulates). Next: a stratum
where the polarities differ drops one of the consumed laws. The
candidates are the mixed law, one hand's associativity, and the
invertible framing.

## 2026-07-29 — the duploid papers, reviewed and one of them audited

**`munch-maccagnoni-duploids` is `verified`: 29/29 CONFIRMED
(digest-level).** Ten revision rounds, seven adversarial reviews, and
one independent statement audit, converging on a tracked correction
patch and a committed measuring script (`pdf-scan.py`) that turns
every drawn-mark count in the entry into a `--check`-verified one
instead of an asserted one. The audit's own find, not caught by any
review: the Theorem 28 digest's reflection triangle was mirrored,
traced to two wrong `ToUnicode` font maps inside the PDF itself, fixed
and disclosed. `just resources-verify` now lists the entry
`audited — load-bearing capable`, up from `NOT audited`.

**`mmmm-classical-notions` is `unverified`, mid-cycle.** A researcher
pass and merge raised its digest coverage from 6/44 to 24/44 main-text
statement environments (7 to 30 Content digests). Its own review-2
findings (one MAJOR — `bin/resources-verify` cannot parse a
`Statements verified: N/M` fraction, so a 3/30 entry reads as fully
audited — and seven MINOR) are recorded but not yet applied, and no
audit has run over the 23 new digests.

Committed: `resources/munch-maccagnoni-duploids/README.md`,
`resources/munch-maccagnoni-duploids/pdf-scan.py`,
`outputs/duploids-entry-audit.md`. Session log:
[`notes/2026-07-29-duploid-papers-audit.md`](notes/2026-07-29-duploid-papers-audit.md).

## 2026-07-29 — mmmm-classical-notions closes out, both duploid entries vetted

**`mmmm-classical-notions` is `verified`: 30/30 CONFIRMED
(digest-level).** Review-2's revision plan landed. The Vetting section
now discloses a second source typo. The digest preamble names the
`⟑`/`⟇` substitution, and two digests fix `M` to `ℳ`. The Section map
gains the `l.3725` `\end{document}` line and the source's own names
for Joyal's obstruction theorem and §13.

The Dialogue duploid digest's `≃` and the dropped clause in the
Thunkable-implies-central digest are both restored. An independent
audit (Claude, Opus 5) then re-derived all 30 digests from
`article.tex`, from scratch. It confirmed 23 near-verbatim and 7
paraphrase digests, zero not confirmed, including the six passages the
revision touched.

**`bin/resources-verify` now parses the `Statements verified: N/M`
fraction.** It reports a partial standing when `N` is less than `M`.
It reads the "N confirmed on first pass, K corrected" phrasing as full
coverage, not partial. `resources/README.md` now names a digest
addition or revision, beside a re-fetch or a re-extraction, as an
event that voids the field.

**Both duploid-tier entries carry a `Vetted:` line, at Lane's
direction.** `munch-maccagnoni-duploids` (29/29, from the prior
session) and `mmmm-classical-notions` (30/30, this session) both
retire their PROVISIONAL marker.

Uncommitted, pending Lane's go-ahead:
`resources/mmmm-classical-notions/README.md`,
`resources/munch-maccagnoni-duploids/README.md`,
`resources/README.md`, `bin/resources-verify`,
`notes/2026-07-25-two-lineages.md` (the downstream anchor fix from
review-2), and `outputs/classical-notions-entry-audit.md`. Session
log: [`notes/2026-07-29-classical-notions-audit-complete.md`](notes/2026-07-29-classical-notions-audit-complete.md).

## 2026-07-29 — polarity is a twist condition, at two strengths

**`Test.SpikePolarityTwist` is live** (slug
`polarity-twist-condition`, brief at
`outputs/.plans/polarity-twist-condition.md`). The spike measures
the converse of the forward instantiation: whether linear twists
at `x` return `positive x`, and thunkable twists `negative x`.

All four closures check over the bare tower, from the three
associativity theorems alone: `thunkable` and `linear` under both
cuts. Two are one-sided (`linear-⨾⁺` reads its leading factor,
`thunkable-⨾⁻` its trailing factor). The converse follows at two
strengths. On carriers generated by the twists under the cuts
(`gen`), both twists decide the polarity. At full deductive-system
strength the balanced unit laws make one twist decide it, so no
deductive system separates the twist condition from the polarity.
`gen-sem` proves the word model generated, where the check is
vacuous: each hypothesis pair fails on exactly one twist.

Open: the twist reduction below invertibility on non-generated
carriers. A countermodel needs a stable, composable,
non-invertible carrier with both twists linear at an object and a
non-linear edge out of it. Ledger updated
(`src/Cat/Logic/TODO.md`, twist-condition block + line 4).
`verified` (`just check Test.SpikePolarityTwist`, 2026-07-29, zero
warnings, no holes, no postulates). Next: either construct that
countermodel or take up the polarity subcategories from line 4.

## 2026-07-29 — the h-level of polarity, at two models

**`Test.SpikePolarityHLevel` is live** (slug `polarity-hlevel`,
brief at `outputs/.plans/polarity-hlevel.md`). `positive` and
`negative` transcribe the duploids paper's Definition 1 over the
tower, with no truncation.

Circle model: `mult-assoc` makes every
edge thunkable and linear, so both polarities hold at the one
object. The `rot`-shift gives a second witness one winding away.
So polarity is structure: not a proposition, not contractible.
`filler-distinct` shows two positivity witnesses fill one
`associates` cell in two ways. A positive-objects subcategory
therefore carries its mixed associator as a choice.

Word model: both polarities are propositions over the set-level
homs, and both are empty (`linear-refuted` at `ε̂`,
`thunkable-refuted` at `τ̂`). `verified`: `just check
Test.SpikePolarityHLevel`, 2026-07-29, zero warnings, no holes,
no postulates, prose at 0.19/100w.

Ledger updated: `src/Cat/Logic/TODO.md` gains the settled block
"the h-level of polarity, at two models". Line 4 of the
investigation list points at it. The RULED note on mode
separation stands untouched. Open next: the polarized
subcategories and the closure of `thunkable`/`linear` under the
compositions (line 4's remainder).

## 2026-07-29 — the defect promoted, and the Cat.Logic ledger split starts

**`Cat.Logic.Gist.AssociatesDefect` is live.** Promoted from
`Test.SpikeAssociatesDefect`: `just mv`, then a rewritten opener
that leads with the result's significance instead of the bare
statement. `verified`: `just check
Cat.Logic.Gist.AssociatesDefect`, zero warnings, no holes, no
postulates, prose at 1.50/100w.

Every stale reference to the old name swept from `TODO.md`, this
file, and `outputs/.notes/associates-defect-results.md`. A
repository-wide search confirms none survive.

**The `Cat.Logic` ledger split starts**, per
`docs/plans/documentation-restructuring.md`. New:
`src/Cat/Logic/lemmata.md` (bare statement and citation) and
`src/Cat/Logic/gloss.md` (extended commentary), same numbering as
`docs/gloss.md`.

T25 to T30 and T32 to T35 moved out, T36 added for the new result.
T31 and T21 to T24 stay in `docs/gloss.md`. Their citations resolve
to archived `Bb` modules with no ledger of their own yet. The plan
document now records this as the open remainder of step 4.
`verified`: `just lint citations` finds zero dangling citations in
the two new files, and `just lint changed` passes clean.

**Process note.** A subagent stopped by Lane mid-run does not
resume through `SendMessage`. It returns `success: false` and
requires an explicit relaunch. A subagent that pauses itself
resumes fine. Recorded in the `restart-means-same-agent` memory
file.
Session log: [`2026-07-29-associates-defect-promotion.md`](notes/2026-07-29-associates-defect-promotion.md).

## 2026-07-29 — the associates defect is a framing word, per flanking edge

**The bare independence is now a measured defect.** Over the free
balanced point (`Cat.Logic.Gist.BalancedWord`), each bracketing of
`associates` determines the other up to a twist word, one word per
hand, and the word reads one flanking edge alone. `defect⁺`
corrects on the leading side by `w⁺ (rise f)`. `defect⁻` corrects
on the trailing side by `w⁻ (zrunW h)`. Both hold at every triple.
The corrections are powers of the reverse bicyclic composite, and
they are units exactly at the thunkable/linear closures. No
uniform word exists in any of the sixteen placements, and fourteen
placements fail outright. The winding grade never separates the
bracketings (`shift-associates`), so the two-sided-cancellation
collapse erases the defect. `verified`: `just check
Cat.Logic.Gist.AssociatesDefect`, zero warnings, no holes, no
postulates. The placement census and the ℤ-collapse sample are
script-level (`outputs/.notes/associates-defect-*`). The scope is
the free point itself. The verdict sits in `src/Cat/Logic/TODO.md`
under the settled profile block. Next step: the generator-bearing
word model (initial-model program, item 1 sequels), to test the
per-edge factorization beyond the point.

## 2026-07-29 — the audit chain refuses, and documents get registers

**Three passes, a defect at each.** A source-fidelity certification on
`resources/munch-maccagnoni-duploids/` was written and certified by
one pass in one run, which `resources/README.md` forbids. An adversarial
`reviewer` at opus/xhigh found six of 24 digests drifting, coverage at
24 of the paper's 28 statements, an invented citation ("after Führmann
and Hasegawa" where the source says `[16,8]` and Hasegawa appears
nowhere in the paper), and a **fabricated evidence claim**: "confirmed
against rendered PDF pages" for a paper with no vendored PDF and no
LaTeX engine installed. `verified` by the lead re-deriving each. The
field was **withdrawn**; `just resources-verify` now reports the entry
`NOT audited`. Lane's diagnosis of the Hasegawa error held and was
narrow: exactly one contamination hit, borrowed from the sibling entry
whose title carries that name, digested in the same run.

**The lead then corrected six digests and wrote four missing ones, and
a third pass refused the field on two defects in those corrections.**
The instructive one: the text extraction flattens a two-column display,
the lead read it in line order, and Proposition 16's `⇑f` lost its
`force_A` while `⇓f` gained one. The result typed as `A → ⇑B` where the
functor needs `⇑A → ⇑B`. Settled by a 500 dpi render and the type of
`force_P`. `verified`: 26 of 28 digests faithful, both wrapped anchors
correct, coverage 28/28. `unverified`: Propositions 14 and 16 as now
written. `blocked`: the field, pending a fourth reader over those two
only — the 26 confirmations stand.

**Tooling.** `just sync` and `just check-all` retired with the All
aggregator, references struck from five files. `bin/lint` gains a
`citations` check: every module a `gloss.md` or `lemmata.md` names must
resolve under `src/`. Opt-in until the ledger split lands. `verified`
against false positives with a planted ledger.

**Ruling (Lane): four registers, and `docs/plans/`.** Module prose says
what an object is; `<namespace>/gloss.md` carries commentary on a
construction; `<namespace>/lemmata.md` the statements; `docs/guidelines/`
standards stated abstractly. `gloss` and `lemmata` are the classical
pairing — headword and commentary. Separately, standing plans with
gates get `docs/plans/`, distinguished from `outputs/.plans/` by
ephemeral against standing rather than tracked against untracked: every
file in the latter today is a consumed run brief. `composite-rx-refactor`
was never misplaced, being a standing gated program like the roadmap;
what was wrong in `docs/` was `deductive-systems/`, namespace commentary
belonging beside its code.

The cause of all of it: `just mv` sweeps `src/` only, nothing typechecks
a document, so a document naming a module inherits its lifetime without
its maintenance. Thirteen of `docs/gloss.md`'s 22 cited paths dangle.
Session log:
[`notes/2026-07-29-audit-chain-and-doc-registers.md`](notes/2026-07-29-audit-chain-and-doc-registers.md).

## 2026-07-28 — duploid source audit: both entries cleared to load-bearing

**Statement-level audit of both duploid papers in `resources/`**, run
via `/deepresearch` (2 parallel `researcher` subagents, then
`verifier`, then `reviewer`, then a revision pass). `verified`:
`mmmm-classical-notions`'s seven existing Content digests, 7/7,
against `article.tex`; `munch-maccagnoni-duploids`'s 24 numbered
statements, 24/24, against `duploids.pdftext` — this entry had no
digests before this pass, now does. Two source-level errors found in
the papers themselves: a codomain typo in `mmmm-classical-notions`'s
composition-law diagram (`article.tex:1531`), and a
"linear"/"thunkable" slip in Munch-Maccagnoni's Proposition 8 proof
(`duploids.pdftext:434-436`).

**Correction, 2026-07-28.** This entry read "confirmed against
rendered PDF pages, not extraction artifacts". That is withdrawn for
the `mmmm-classical-notions` typo. No PDF of that paper is vendored
and no LaTeX engine is installed, so no rendered page could have been
read. The finding stands on the vendored `article.tex`, which is
LaTeX source, so no extraction step exists to blame. The
Munch-Maccagnoni finding is confirmed against a rendered page, and a
second reviewer strengthened it: `duploids.pdftext:703-704` shows the
paper's own later text reading Proposition 8 as the audit does. The
same wording stands uncorrected in the commit message of `2611d7e`,
which cannot be edited.

**`24/24` qualified, same date.** A second review at higher tier
(`outputs/.drafts/duploids-statement-audit-review-2.md`) found three
of the 24 `munch-maccagnoni-duploids` digests misstating the source,
one by attributing the thunkable terminology to an author the paper
never cites. Twenty-one of 24, and all seven mmmm digests, were
re-read and confirmed faithful. The cause is structural:
`resources/README.md` defines the field as an independent audit
dispatched after the entry is built, and this pass wrote the digests
and certified them in one run. `mmmm-classical-notions` keeps `7/7`.
`munch-maccagnoni-duploids` reads as audited with corrections
pending until a second reader re-issues the field. `docs/gloss.md`
T35 is unaffected: its cited digests are among those confirmed.
`unverified`, flagged open rather than asserted: whether
`mmmm-classical-notions`'s duploid definition actually coincides with
either of Munch-Maccagnoni's two equivalent forms — the paper itself
concedes only "a slight variant of" (`article.tex:1817`). The
`reviewer` pass found four MAJOR issues (a wrong citation inventory,
an incomplete comparison space, a false "no dead anchors" claim, an
uncorrected error in a supporting research file) and three MINOR; all
fixed in a revision pass and independently re-verified on disk before
delivery.

**Barrier removed.** `Statements verified:` fields written to both
`resources/mmmm-classical-notions/README.md` and
`resources/munch-maccagnoni-duploids/README.md` (the latter also
gained its first Content digests section); `just resources-verify`
now reports both "audited — load-bearing capable" (was "NOT
audited"). `TODO.md`'s "the two duploid source audits" line checked
off.

Session log:
[`notes/2026-07-28-duploids-statement-audit.md`](notes/2026-07-28-duploids-statement-audit.md).
Next: a future pass on whether `mmmm-classical-notions`'s
universal-property duploid definition is equivalent to
Munch-Maccagnoni's Definition 7 (the more likely bridge, per the
audit).

## 2026-07-28 — the euler subagents: models pinned, skill access repaired

**Models pinned** (Lane). No agent in `.claude/agents/` set `model:`,
so all four inherited the session model and would drift together on
any change of default. The euler pipeline runs researcher, writer,
verifier, reviewer, and that ordering decides the tier. An agent with
a checker downstream can run cheaper. An agent that is itself the
last check cannot. `researcher` and `writer` take `sonnet`.
`verifier` takes `opus`, effort raised `medium` to `high`, since its
transcription diffing against dependent types fails silently.
`reviewer` takes `fable`.

**Skill access was broken, and with it a contract duty.** The
`skills:` frontmatter key is absent from the documented field set,
and no shipped agent anywhere uses it. All four euler agents declared
`skills: - writing` and none had the `Skill` tool, so none could
invoke the skill. `.claude/rules/euler.md` requires the verifier to
run the writing skill's linter on the final artifact and record the
score in the `.provenance.md` sidecar. That duty was
undischargeable. All four now carry `Skill` in `tools`, plus a
role-specific prose-standard section. The verifier's section names it
owner of the prose gate.

`verified`: the frontmatter of all four parses, each carrying
`model`, `effort`, `Skill` and a prose section. Linter scores
improved on all four prompts (3.32→3.13, 3.55→2.94, 4.04→3.73,
4.76→4.48). `unverified`: that the harness honors `model: fable` in
frontmatter. The Agent tool's enum accepts it, but the plugin-dev
doc lists only inherit/sonnet/opus/haiku and may predate Fable.
`unverified`: that `skills:` does anything, and that any of this
takes effect, since agent definitions load at session start.
`inferred`: that each model suits its role. One data point per model
this session, and nothing compares Opus against Fable for
adversarial critique. Next: smoke-test the reviewer, then return to
`Cat.Logic.Morphism`. Session log:
[`notes/2026-07-28-euler-subagent-config.md`](notes/2026-07-28-euler-subagent-config.md).

## 2026-07-28 — morphisms opened, a polarity alarm answered, the doc set reconciled

**Initiality landed, `verified`** (`Test.SpikeMorphismInitial`,
recorded `just check`, zero obligations): the morphism record
(`map`, `hmap`, `pres-twist±`, `pres-reflect`) and
`is-initial G = ∀ G' → is-contr (G ⇒ G')`, itself a proposition.
Initiality truncates no hom. It asks one fiber to be contractible.
The empty graph is initial. The codiscrete graph on two points
carries the full axioms and still has two distinct self-maps, so no
axiom makes system maps a proposition. `Cat.Logic.Morphism` did
**not** land. The polarity report stopped both agents, and T1 had
written nothing.

**The reported polarity error was a false alarm with a real cause.**
`inj⁺`/`inj⁻` and the whole composition register carry correct
labels, and no proof moved. The missing fact was the order
convention. Munch-Maccagnoni composes applicatively and this library
diagrammatically, so transcribing Definition 1's (•◦) clause without
reversing the order reads the word backwards. That inverts the
labels on sight. `verified` that `(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)` is
that clause verbatim, so `⁻ = ◦` and `⁺ = •` both stand. The
convention now sits in `towers.md` and the TODO.

**What did cause it: prose that justified a label by the held
axiom.** Four sites said "coact holds `var`, hence…", which reads as
binding `var` to coactions and inverts the standard. All corrected.
Ruling (Lane): `act` and `coact` keep their names, since the types
force that binding, making it implementation and not semantics.
`framing.md` now derives the framing gloss from traced crossings
(`twist⁺` a buffer, `twist⁻` a future), `CONJECTURED`, since
*Asynchronous Games 3* is still not vendored.

**Docs debt paid, not deferred** (Lane: "we do pay for docs debt
like this"). Eleven of twelve `docs/deductive-systems/` files were
stale against the record cut. `the-package.md` carried the pre-cut
three-field record and cited `FramedCut` as inhabitant, which
readback rules out. `composability.md` showed the stability-indexed
record. `towers.md` claimed one unit law per hand, now four.
`invertibility.md` and `framing.md` each claimed nothing decides
whether a centre is the other twist, which T33 refutes.
`README.md` omitted `readback` entirely. The retired `pin`, `K`,
`unital` and `absorption` names left `docs/` and
`Cat.Logic.Type`'s register list.

**`(D′)` retired** (Lane). It named a position only against the
rejected `(C)` and `(D)`, so it read as a variant when it is the
definition. Live prose and `docs/roadmap.md` now say "deductive
system". The TODO keeps the letters as the record of the decision.
`Cat.Logic.Gist.BalancedWord` opens with the construction instead.

`verified`: `check-tree src/Cat` 21/21, `check-tree src/Test` 9/9,
`lint changed` clean, all twelve doc files and `roadmap.md` at or
under the 2.0 prose gate. `unverified`: the morphism signature's
implicit/explicit calls (elaboration probes unrun) and
`pres-⨾⁺`/`pres-⨾⁻` (unattempted). Next: `Cat.Logic.Morphism` from
`outputs/.plans/system-morphisms-T1.md`, then promote the spike to
`Cat.Logic.Gist.MorphismInitial`. Session log:
[`notes/2026-07-28-morphisms-polarity-docs.md`](notes/2026-07-28-morphisms-polarity-docs.md).

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
`check-tree` sweeps `.lagda*`. The whole-tree sweep surfaced six
pre-existing reds (the `Data.Thin` four, `Core.Coherence.Paths`,
`Core.Path.Coherence`), itemized in the root `TODO.md`. Whole
tree: 317 of 323. Lint clean.

**Close-out, `verified`**: the spike's general lemmas vendored
home (`So` to Bool, the comparators bridged to builtins in Nat,
`DecEq-List` generalized, the Int kernel with `_⊖_`), the spike
promoted to `Cat.Logic.Gist.BalancedWord` (`src/Cat` 21 of 21,
`src/Core` 137 of 139, the two failures pre-existing). Root
`CLAUDE.md` rewritten to the `writing` skill (6.01 → 1.45 per
100 words) with the Delegation section and the prose-law
priority; the root `TODO.md` opened; the roadmap re-founded (the
foundation track under project 1, the Core reformation gated as
project 2). Commits: `4dd6bd0`..`cfc2147` (the ten), then
`d2c6499`, `7436984`, `e57dce1`, `47a7033`, and the notes
commit.

Next: line 9 item 2 (morphisms), the gloss entries for the cut
and the profile. Log:
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
