# Convention-corpus review — rulings sheet

**GATED: post-refactor.** Lane's ruling (2026-07-11): nothing about
the repo's existing conventions is standardized until THE REFACTOR
lands and Lane says go. This sheet is banked intelligence for that
arc — the findings stand, the ruling questions wait, no revision
below executes before the gate opens. The context layer itself
(skills suite, HARNESS.md, docs/provenance.md, resources/, notes
taxonomy, CLAUDE.md contract) is the current arc's deliverable and
proceeds; it is the foundation the post-refactor standardization
builds on.

Run date: 2026-07-11. Eight reviewers over the pre-session
convention corpus; styleguide.md quarantined by ruling (style arc
deferred until after the context layer; its observations are parked
in the run transcript, no dispositions taken). Each document below:
proposed disposition, the load-bearing findings, and the questions
only Lane can answer.

## README.md — revise

Findings: identity paragraph is 2026-03 future-tense aspiration;
no mention of AI assistance or docs/provenance.md anywhere (the
public face is silent on the exemplar layer); credits cite modules
that no longer exist (Core.Set.Omega; Lib.SSet.*/Lib.CSet.* —
remnants only in Stash/); Foundations list drifted from the actual
reference set (cites Chen arXiv:2503.05790 and Sterling reflexive
graph lenses, used nowhere else); no build section (`just
check-all`, Agda requirement, `just --list`).

Rulings:
- R-A1. Lead with the AI-assistance/provenance statement right
  after the title (exemplar-forward), or mathematical identity
  first and provenance second?
- R-A2. Foundations section: align to design.md's references, or
  replace with a pointer to design.md? Do Chen and reflexive-graph
  lenses stay or go?
- R-A3. Credits naming removed modules: delete, or rescope with a
  licensing note if derived code survives in Stash/?

## coh.md — delete

A completed 2026-03-10 pre-implementation memo for what became
Cat.Coherence; every claim is realized in committed code or
restated canonically in design.md/gloss.md; vocabulary retired
(noy → pre). Untracked; `rm` suffices.

Ruling:
- R-B1. Does the legacy Cat.Coherence pentagon/triangle (Cat.Type
  era, ✅ March 2026) get a "standing results from earlier strata"
  line in gloss.md before deletion, or is supersession by T4/T8
  sufficient record?

## docs/design.md — revise (largest single revision)

Findings: canonical-record names wrong throughout (says
codep-structure/-axioms/-category; code and ledger say
hcategory-*); names derived-law modules that no longer exist
(Cat.Codep.Coupling/Unit); the re-anchoring mechanism section
describes a retired carrier decomposition; the document ends before
the coherence arc — nothing on the Coherent overlay, θ-core/gauge
collapse, covariant op, or the regress theorem (T5–T12); the
primary Cat.* exposition is still the legacy Cat.Type theory;
multiple fresh-start violations ("This replaced…", "now merged");
several claims worded stronger than their ledger status (Kₙ
associahedra beyond T4; the braid-tier defect table); literature
attributions carry no epistemic labels and no resources/ backing.

Rulings:
- R-C1. Restructure Codep-first now (hcategory as the theory,
  Cat.Type/Monoidal demoted to a bounded pre-refactor section), or
  fix only the canonical chapter and restructure at THE REFACTOR?
- R-C2. Naming authority: hcategory-* (code + gloss) or codep-*
  (lexicon)? Which spelling is law — lexicon gets corrected, or the
  code is due a rename?
- R-C3. Braid-tier and Kₙ claims: add 📐 gloss entries for what is
  actually established and cite them, wording the rest as
  conjectural?

## docs/architecture.md — revise

Findings: names Cat.Type canonical four times (Codep is canonical);
bin/docs-drift parses strata [0-2] while Stratum 3 exists (the
machine-parseable claim overstates coverage); phantom row
Cat.VirtualProposed (no such file); Cat.Experiment.Base exists on
disk but is unmapped; correction-history narration in the Triangle
paragraph; Stratum-3 paragraphs drifted from mapping into proof
exposition; no "legacy/frozen" status marker for the pre-refactor
modules.

Rulings:
- R-D1. Restructure around Cat.Codep as canonical (Strata 0–2
  marked pre-refactor), or keep dependency-ordered strata and only
  correct the labels?
- R-D2. Cat.VirtualProposed: delete the phantom row, or materialize
  the design as a real Stash//Test/ file?
- R-D3. Cat.Experiment/: sanctioned namespace (add to tables), or
  move src/Cat/Experiment/Base.lagda.md into src/Test/?

## docs/lexicon.md — rewrite (confirmed; owed from roadmap)

Findings: entry layer ~half stale (codep-* trilayer, retired
carrier vocabulary, dead modules, dropped composite-ext); rename
table is pure old→new history (fresh-start violation); pre/post
entries lack the ratified sequential-agency semantics; closed
suffix system doesn't cover shipped families (-invol, gauge-,
bridge-, θ-, swap·); the entire duality vocabulary cluster (T9–T12)
is absent; internal contradiction between the coherence-level
naming rule and the shipped record name hcategory-2-coherent.

Rulings:
- R-E1. Scope: lexicon widens to the single vocabulary registry
  (Gloss/freeze terms, ledger statuses inline), or stays Cat.*-only
  with cross-references?
- R-E2. Pending "at refactor" renames: move to a notes/plans/
  refactor ledger, or keep a forward-only "reserved names" section?
- R-E3. hcategory-2-coherent vs the "levels are named by identity"
  rule: rename the record (e.g. hcategory-coherent) at next touch,
  or revise the lexicon rule?
- R-E4. Does "RCC (representable codependent)" name the planned
  general stratum, or is the label retired?

## docs/gloss.md + src/Gloss/CLAUDE.md — revise (small, surgical)

Bijection verified: five Gloss modules ↔ five 🧪 markers, all
headers/Frozen-from/Core-only conform. Findings: ledger's
maintenance section points at the wrong document for promotion
criteria (says CLAUDE.md; they live in src/Gloss/CLAUDE.md);
"bijection over entries" should say "over 🧪 markers" (T13 has two
certificates across its parts — settled practice, undocumented);
one incident-as-precedent clause to restate positively; T19 omits
Cat.Codep.Instances for its walking-arrow half; T15/T16 cite Kelly
and Melliès with no resources/ backing — the ledger currently
outruns provenance practice 1.

Rulings:
- R-F1. When prose cites a 📐 result: is it CONJECTURED under
  provenance.md (the typechecker is the record), or does
  provenance.md gain a distinct label for rigorous-but-unmechanized
  arguments so 📐 prose may say "established"?
- R-F2. T15/T16 sources: vet Kelly + Melliès into resources/ now,
  or annotate the ledger references explicitly pending-vetting?

## All.lagda.md + justfile + .envrc — revise (small)

Findings: All imports Test.Scratch while CLAUDE.md says Test is
"not in All" (tooling sides with the file: sync-all treats Test/*
as unmanaged-but-kept); All's pragma redundantly carries
--no-sized-types (already global); seven live imports sit after the
WIP block (grouping drift; `just sync --regenerate` fixes); All
lags the filesystem (Cat.Experiment.Base unimported); `--regenerate`
mode undocumented in justfile comment and CLAUDE.md table; AGDA env
override undocumented; .envrc carries an uncommented Claude-Code
setting on a harness-generic surface.

Rulings:
- R-G1. Test.* in All: CLAUDE.md's "not in All" wins (delete
  Test.Scratch, All strictly Test-free), or sync-all's
  unmanaged-but-kept policy wins (amend CLAUDE.md)?
- R-G2. All.lagda.md: stays header-free, or gains a one-line prose
  pointer to CLAUDE.md's All Module section?

## styleguide.md — DEFERRED by ruling

Style arc runs after the context layer. The reviewer's observations
(line widths match bin/lint exactly; type-signature layout and
reserved-identifier tiers confirmed in practice; where-clause,
import-ordering, and record-casing rules diverge from the canonical
development; dead examples: Spine, Bin.set, 1lab snippets; pcom
vocabulary absent) are parked in the run transcript for that arc.
Per ruling: practice is not normative evidence; no dispositions
taken.
