# Review: the polarity-collapse spike chain

Three independent, adversarial reviews (Opus, one reviewer per
artifact, run strictly sequentially), covering:

1. `src/Test/SpikePolarityHLevel.lagda.md` — transcribes
   Munch-Maccagnoni polarity over kitcat's `tower`, measures its
   h-level at two models.
2. `src/Test/SpikePolarityTwist.lagda.md` — reduces polarity to a
   two-edge (twist) check; proves closure under both cuts and a
   one-edge theorem at full deductive-system strength.
3. `src/Test/SpikePolarityCollapse.lagda.md` — proves the two twist
   conditions are equivalent at every object of a full deductive
   system, refuting the possibility of a polarity-distinguishing
   model.

Each reviewer worked from the artifact and the library alone, without
being told what the others found or what the constructing session
concluded. This document is the lead session's synthesis of their
three independent reports, not a fourth review.

## Summary Assessment

The kernel-checked mathematics across all three modules is sound. Each
reviewer independently re-derived the load-bearing proofs by hand
against the actual library lemma types — not by trusting the Agda
checker's exit code alone — and found no gap, no gaming, no smuggled
hypothesis, and no vacuous theorem presented as substantive without
disclosure. All three modules are clean under a **freshly re-checked**
run (cache deleted, re-elaborated from source): zero warnings under
global `-Werror`, no holes, no postulates, no unsafe markers.

The defects found are real but are concentrated in one place: the
seam between what the modules' prose claims and what their Agda types
actually state. One of these is a genuine **Critical** finding — a
wrong citation, now propagated into this session's own ledger and
changelog entries — and it should be fixed before this chain is relied
on by future citation. The rest are Major/Minor overclaiming,
underclaiming, redundancy, and disclosure gaps that do not threaten
any proof's correctness.

One thread connects two of the three reviews and is worth naming
up front: the `SpikePolarityHLevel` reviewer flagged (M3) that the
circle model's two cuts are *definitionally* the same operation
(`mult`), so its "both polarities hold, non-degenerately" result might
be a special case rather than a generic phenomenon. The
`SpikePolarityCollapse` reviewer then confirmed, independently, that
at full deductive-system strength the two twist conditions are
*provably* equivalent everywhere — a general theorem that explains,
rather than merely coincides with, the circle model's specific
behavior. The first reviewer's skepticism was well-placed; the third
module answers it.

## Strengths

- **Proof rigor.** All three reviewers re-derived the central chains
  of reasoning by hand — composing each cited library lemma's actual
  type against the claimed endpoints — and confirmed every step
  composes correctly. The `SpikePolarityCollapse` reviewer produced a
  full seven-step independent re-derivation of the chain's headline
  argument (`from-linear.thunkable-twist⁻`) and found the code proves
  exactly what it claims, at full generality (the object, and both
  composed edges, are genuinely arbitrary — nothing is secretly
  specialized).
- **No definition gaming, no undisclosed vacuousness.** Where a
  theorem's hypothesis is unsatisfiable at a cited model (the word
  model's twist-level corollaries in `SpikePolarityTwist`), the
  module's own prose discloses this plainly. No reviewer found a
  theorem dressed up as more substantive than its actual content.
- **Genuine adversarial checks passed.** The `SpikePolarityCollapse`
  reviewer swapped which polarity label attaches to which cut in a
  probe module and confirmed the swap fails to typecheck
  (`UnequalTerms`, exit 42) — the sign convention is forced by
  definitional inequality of the two twists at the word model, not by
  a choice the module could have made differently. The
  `SpikePolarityTwist` reviewer independently confirmed the two
  claimed one-sided closure lemmas really are one-sided in the type
  system, not merely in an unused-argument sense.
- **Clean kernel state.** Fresh (non-cached) `just check` runs on all
  three modules: exit 0, zero warnings, zero holes, zero postulates,
  zero unsafe markers, across three independent reviewer sessions.

## Critical Issues

### C1. Wrong citation for `positive`/`negative`'s source definition — `SpikePolarityHLevel`

The ledger (`src/Cat/Logic/TODO.md:481-482`), the changelog
(`CHANGELOG.md:198-199`), and this session's own planning file
(`outputs/.plans/polarity-hlevel.md:57-58`) all cite "Definition 1" of
`resources/munch-maccagnoni-duploids` as the source of the
`positive`/`negative` definitions transcribed in
`SpikePolarityHLevel`. **Definition 1 does not state that
definition.** It makes polarity a *primitive* map into a two-element
set (a partition), never derived from linearity or thunkability. The
repository's own already-audited digest of that entry says so
directly (`resources/munch-maccagnoni-duploids/README.md:863-864`):
"a set of objects `|D|` with a polarity map `ϖ : |D| → {+, ⊖}`" — the
lead session independently confirmed this digest line before accepting
the finding.

The correct citable source, already on the audited shelf, is
`resources/mmmm-classical-notions/article.tex:1694-1700` — attributed
there (`:1691`, resolved via `article.bbl:264-306`) to Clairambault and
Munch-Maccagnoni, *Duploid situations in concurrent games*, GaLoP XII
2017, not to the primary duploids paper. The shape actually followed
in the module is closest to Sterling's TypeTopology mechanization
(`~/TypeTopology/source/Duploids/DeductiveSystem.lagda:236-245`),
whose own header states in writing that its definition **differs**
from Munch-Maccagnoni's (`Preduploid.lagda:3-8`).

**Why this rises to Critical rather than Major:** the citation is
wrong in a way that is falsifiable from evidence already inside the
module under review. `positive-all`/`negative-all` (circle model) make
one object both positive and negative; `positive-empty`/
`negative-empty` (word model) make one object neither. Both are direct
contradictions of Definition 1's actual content (a total map into a
two-element set is disjoint and exhaustive by construction) — so the
citation, if trusted, would make the module's own headline results
read as impossibilities under the definition it claims to transcribe.

**Fix:** repoint all three citations (ledger, changelog, plan file) to
`article.tex:1694-1700` with the correct attribution, cite
`duploids.pdftext:243` for the forward-implication-only consequence
Definition 1's neighborhood does state, and record the Sterling
TypeTopology mechanization as the shape actually followed (per
`docs/provenance.md`'s promotion route for library-derived shapes).
This is a documentation fix — no proof needs to change.

## Major Issues

### M1 (HLevel). No definition provenance inside the module itself

`SpikePolarityHLevel.lagda.md:4,45` say "Munch-Maccagnoni's
polarities" / "the source definitions" with no resource, section, or
definition number named anywhere in the module. `docs/provenance.md`
practice 3 requires every leaned-on definition to document its source
inline. Independent of C1's citation error, the module should name
*a* citation, correctly, inside itself — not only in the ledger.

### M2 (HLevel). The two models measure structurally different carriers, undisclosed

The circle model's two cuts (`C⁺`, `C⁻` in `ThunkableSquare`) both
compute to `mult`, definitionally — a single-cut carrier. The word
model's two cuts (`BW-comp⁺`, `BW-comp⁻`) are genuinely different
operations, and `associates-refuted` proves it. So the circle-model
"structure" result and the word-model "empty property" result are not
two h-level measurements of one notion at comparable carriers — one is
measured where `kitcat`'s two-operation `associates` reduces to a
single-operation identity (Sterling's original one-cut notion, on the
nose), the other where it doesn't. The module states the circle fact
in passing (`:101`) but never draws this consequence. This is the
thread the Summary Assessment connects to `SpikePolarityCollapse`'s
result.

### M3 (HLevel). The closing claim outruns what the supporting model shows, and outruns the cited paper's own caveat

`:203-204` — "At full deductive-system strength, polarity is
structure" — is supported by exactly one model, and in that model both
polarities hold for a reason the correctly-cited source already gives:
`article.tex:1701-1703` notes an object can be both positive and
negative "in particular for every object X of an associative
category" (i.e., where the two cuts agree). The module's new content
is the *h-level* of that inhabitation, not the inhabitation itself —
worth stating plainly rather than implying the whole result is novel
at the level of "polarity holds here."

### M4 (Twist). Word-model corollaries are vacuous with the disclosure only in prose, not machine-checked

`positive-two-edge`/`negative-two-edge` (`SpikePolarityTwist.lagda.md:370-374`)
have both an uninhabited hypothesis pair and an uninhabited conclusion
at the word model. The module's prose discloses this honestly, but the
two sentences that carry the disclosure cite `linear-refuted`/
`thunkable-refuted`, which the module does not import — so the
disclosure is not itself kernel-checked in this file. A two-line
import and an explicit `¬ positive tt`/`¬ negative tt` statement would
close the gap.

### M5 (Twist). The one-edge theorem's stated hypothesis is stronger than what the proof uses — "the exact consumable" is false as written

`positive-from-unit`/`negative-from-unit` are proved using the unit
law instantiated at a *single* object, but stated with a
universally-quantified hypothesis over all objects. The reviewer
checked a genuinely localized restatement compiles with the identical
proof term. This matters beyond wording: as stated, the general-purpose
form cannot be applied to a carrier that is unital at one object among
non-unital ones, even though the proof doesn't need that generality.
(`module full`, which is what the rest of the chain actually
consumes, is unaffected — it already has the global law from
`balanced`.)

### M6 (Twist). The "generated carrier" tier is silently restricted to loop-only carriers

`gen-diag` forces every twist-generated edge onto an endpoint-identity
loop, so the whole tier is vacuous on any carrier with a non-loop
edge — a fact the module's own prose states as a mechanism (`:149`)
but never draws out as a scope limitation on "generated carrier" in
the closing summary. The only exhibited generated model (`BW`) also
satisfies the strictly stronger one-edge theorem, so this tier is
never shown to buy anything beyond it.

### M7 (Twist). `positive`/`negative` are now duplicated across two live-consumed Test modules

The restatement in `SpikePolarityTwist` is byte-identical to
`SpikePolarityHLevel`'s, for a stated and legitimate reason (an
erasure boundary). But two further modules (`SpikePolarityCollapse`,
`SpikeOperatorCarrier`) now import the *Twist* copy specifically, so
the definitions are functioning as shared library API from a
gate-exempt scratch namespace — exactly what `src/Test/CLAUDE.md`'s
spike-zero policy asks to be promoted rather than accumulated.

### M8 (Collapse). The module's "every deductive system" prose claim is not what's formally stated, though it is derivable

Every declaration in `SpikePolarityCollapse` is parameterized on the
raw tiers `(G, S, C⁺, C⁻, T⁻, T⁺)`, never on `is-deductive-system` or
`deductive-system` directly. The prose repeatedly asserts the
stronger, bundled-record-level claim ("every deductive system carries
it"). The reviewer wrote and checked the missing corollary (twelve
lines: unpack `is-deductive-system` via `axioms→stable` and the two
`.center` projections, then apply `positive→negative`) and confirmed
it closes — so the claim is true, but a reader currently has to
assemble that themselves, which is exactly the kind of step where a
fidelity error would hide.

### M9 (Collapse). "One property" / "one predicate" overstates a checked iff into an unchecked identity

`:12,260` — the module proves `positive x ⟺ negative x`
(`positive→negative`, `negative→positive`), a two-way implication. It
does not prove `positive ≡ negative` as predicates, and the reviewer
points out that reading is directly contradicted by
`SpikePolarityHLevel`'s own `positive-not-prop`/`negative-not-prop` at
the circle model — if the two were literally one predicate in the
strong sense the prose suggests, that would need to survive being a
non-proposition too, which the prose doesn't address either way.
"Logically equivalent" is the accurate phrase; "one property"/"one
predicate" should be softened or the stronger claim proved.

### M10 (Collapse). `split-refuted` and `split-refuted-dual` are byte-identical in signature — no actual duality, and both are weaker than necessary

The reviewer diffed both signatures and found them identical; the
prose describes two distinct facts ("the first and third clauses
contradict... the second and fourth...") but the code delivers one
proposition, proved twice, each proof discarding two of its four
stated hypotheses. The genuinely informative statements are two
two-hypothesis lemmas (`linear (twist⁺ p) → ¬ thunkable (twist⁻ p) →
⊥`, and the dual), which the reviewer also wrote and checked.

## Minor Issues

Consolidated across all three reports; see each reviewer's full
findings (recorded in this session's transcript) for complete detail.
Grouped by artifact:

**`SpikePolarityHLevel`:** `shiftP`/`shiftN` break the repo's `⁺`/`⁻`
naming convention (internal camelCase where the house style uses the
hand marks); `negative-assoc` has no consumer anywhere in the tree;
three near-identical distinctness proofs could share one lemma; the
object quantifier is never actually exercised at either model (both
set `ob = ⊤`); the "truncates nothing" sentence names no contrasting
truncated form to be meaningful; the `verified:` footer convention
appears only in this session's four new modules and nowhere else in
`src/`, worth confirming as an authorized convention before it
spreads further.

**`SpikePolarityTwist`:** the "consumes the three... theorems, nothing
else" sentence is true only collectively, not per-lemma; `mapPred`
duplicates an existing `List.map` composition; a follow-on prose
sentence claims wider applicability than the two sentences after it
already qualify; two `--erased-cubical` module-scoping evidence values
(`linear-τ̂`/`thunkable-ε̂`) feed no theorem in-module (only prose);
prose lint 0.28/100 words, two long-paragraph flags, both under gate;
one hand-label error in prose (calls a positive cut "negative").

**`SpikePolarityCollapse`:** the `centre`/`cross⁻-into`/
`twist⁻-centre` scaffolding is provably unnecessary — the reviewer
showed `retract` follows from the hypothesis in three steps without
it, in both directions, checked; two sentences state tier necessity
where the module only shows tier *consumption* (a different, weaker
claim the next sentence in the same paragraph already correctly
walks back); `word-check` duplicates two already-imported library
theorems under new local names, and the section's real content (the
sign pairing is forced, confirmed by the reviewer's swap-probe) is
never stated in prose; "category" is used where the library's own term
for this untruncated-hom structure is "unital magmoid"
(`Cat.Logic.Base.lagda.md:579`); one garbled sentence at `:19`.

## Reproducibility and Verification

All three re-runs were performed independently by each reviewer, with
cached interfaces deleted first so the check re-elaborated from
source rather than reporting a cache hit:

```
just check Test.SpikePolarityHLevel      -> exit 0, zero warnings (0.929s warm; 7.8s cold)
just check Test.SpikePolarityTwist       -> exit 0, zero warnings
just check Test.SpikePolarityCollapse    -> exit 0, zero warnings
```

Obligation/unsafe-marker greps (`postulate`, `{!`, `TERMINATING`,
`NON_TERMINATING`, `NO_POSITIVITY_CHECK`, `--allow-unsolved-metas`,
`sorry`, `admit`, `primTrustMe`) — zero hits in all three files beyond
each module's own "no postulates" prose sentence.

Prose linter (`writing` skill's `prose-lint.py`, gate ≤2.0
violations/100 words): `SpikePolarityHLevel` 0.19, `SpikePolarityTwist`
0.28, `SpikePolarityCollapse` 0.00. All well under gate.

Each reviewer additionally wrote and ran disposable adversarial probe
modules (outside the tracked tree, deleted after use, confirmed via
`git diff --stat` showing no residue) to test specific claims: word-
model vacuousness (`SpikePolarityTwist` reviewer), sign-swap failure
and per-direction hypothesis minimality (`SpikePolarityCollapse`
reviewer), and Definition-1 fidelity cross-checking against three
independent sources (`SpikePolarityHLevel` reviewer). All probe
results are reported inline in each reviewer's findings and are
summarized under Strengths and the issues above.

No formal obligation-count discrepancy was found anywhere in the
chain: the "no holes, no postulates" claim in each module's closing
prose is accurate.

## Inline Annotations

- `src/Test/SpikePolarityHLevel.lagda.md:4` — unattributed citation;
  see C1.
- `src/Cat/Logic/TODO.md:481-482` — wrong citation, propagated from
  the module; see C1.
- `CHANGELOG.md:198-199` — same citation, same fix; see C1.
- `outputs/.plans/polarity-hlevel.md:57-58` — same citation in this
  session's own planning artifact; see C1.
- `src/Test/SpikePolarityHLevel.lagda.md:101` — circle-model single-
  cut fact stated but its consequence for M2 not drawn.
- `src/Test/SpikePolarityHLevel.lagda.md:203-204` — closing claim; see
  M3.
- `src/Test/SpikePolarityTwist.lagda.md:56-57` — missing import of
  `linear-refuted`/`thunkable-refuted`; see M4.
- `src/Test/SpikePolarityTwist.lagda.md:211,223-230` — "exact
  consumable" overclaim; see M5.
- `src/Test/SpikePolarityTwist.lagda.md:149,386-389` — generated-
  carrier scope; see M6.
- `src/Test/SpikePolarityCollapse.lagda.md:36,258` — bundled-record
  claim without a bundled-record-level proof; see M8.
- `src/Test/SpikePolarityCollapse.lagda.md:12,260` — "one property"/
  "one predicate" overclaim; see M9.
- `src/Test/SpikePolarityCollapse.lagda.md:225-233` — duplicate-
  signature lemmas; see M10.

## Recommendation

**Accept the mathematics as verified; fix the provenance and prose
before this chain is cited further.**

No proof in any of the three modules needs repair. Priority order for
the fix pass, ranked by the reviewers' own severity assessment:

1. **C1** — repoint the citation in all three affected files
   (module, ledger, changelog — and this session's own plan file).
   This is the only finding serious enough to block confident external
   citation of the chain.
2. **M4, M8** — close the two disclosed-but-not-machine-checked gaps
   (word-model emptiness import; the bundled `is-deductive-system`
   corollary) — both are small, both were already written and
   confirmed to compile by the reviewers.
3. **M5, M9, M10** — correct the three overclaiming/misleading
   statements (unit-law generality, "one property," the duplicate
   `split-refuted-dual`).
4. **M1, M2, M3, M6, M7** and the Minor list — a documentation and
   naming pass; none is urgent, all improve the chain's durability if
   it's promoted out of `Test/` per the spike-zero policy.

## Sources

- `src/Test/SpikePolarityHLevel.lagda.md` (full)
- `src/Test/SpikePolarityTwist.lagda.md` (full)
- `src/Test/SpikePolarityCollapse.lagda.md` (full)
- `src/Cat/Logic/Type.lagda.md`, `src/Cat/Logic/Base.lagda.md` (tower,
  cuts, tiers, `balanced`, cited line ranges per each reviewer's report
  above)
- `src/Cat/Logic/Gist/ThunkableSquare.lagda.md`,
  `src/Cat/Logic/Gist/BalancedWord.lagda.md`,
  `src/Cat/Logic/Gist/AssociatesDefect.lagda.md`
- `src/Test/SpikeOperatorCarrier.lagda.md` (downstream consumer,
  confirmed live)
- `resources/munch-maccagnoni-duploids/duploids.pdftext` (Definition 1,
  l.180-186; partition, l.224-228; Definition 2, l.233-241; forward
  consequence, l.243) and `README.md` (digest, audit status: 29/29
  CONFIRMED, Vetted 2026-07-29)
- `resources/mmmm-classical-notions/article.tex` (Polarity definition,
  l.1694-1700; attribution, l.1691), `article.bbl` (l.264-306), and
  `README.md` (digest, audit status: 30/30 CONFIRMED, Vetted
  2026-07-29)
- `~/TypeTopology/source/Duploids/DeductiveSystem.lagda`,
  `~/TypeTopology/source/Duploids/Preduploid.lagda`
- `docs/provenance.md`, `docs/guidelines/naming.md`, `src/Test/CLAUDE.md`
- `src/Cat/Logic/TODO.md`, `CHANGELOG.md`,
  `outputs/.plans/polarity-hlevel.md`,
  `outputs/.plans/polarity-distinguishing-model.md`
- Evidence notes: `outputs/.drafts/polarity-collapse-chain-review-evidence.md`
- Plan: `outputs/.plans/polarity-collapse-chain-review.md`
