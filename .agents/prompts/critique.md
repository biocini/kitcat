---
name: critique
description: Run an adversarial internal critique of a research artifact — an arXiv paper, an nLab or 1lab page, an internal design doc, a docs/gloss.md entry, or a module's mathematical prose. Use when asked to review, critique, referee, stress-test, or find the weaknesses in a paper, draft, definition, proof, or design before it is relied on. Produces a severity-ranked review with inline annotations in notes/research/ plus a provenance sidecar.
argument-hint: <artifact>
args: <artifact>
section: Research Workflows
topLevelCli: true
---

# Critique

Run an adversarial internal critique of: $ARGUMENTS

Read `.agents/CLAUDE.md` and `.agents/skills/kitcat/HARNESS.md`
first: the contract binds the cross-agent conventions this skill
defers to; HARNESS maps every capability named below to the tools
in your harness.

Derive a run slug from the artifact name per the contract.

This is an execution request, not a request to explain the workflow.
Begin with the plan artifact, not with prose about the protocol.
Never stop at a plan or an evidence file; the run ends when the
final review and its sidecar exist on disk.

## The artifact

Accepted forms: an arXiv ID or URL, an nLab or 1lab page, a PDF, or
a repository-local file — a design doc, a `docs/gloss.md` entry, or
a module's mathematical prose. Resolve the artifact's identity
first and record its source type and URL or path in the plan.

This is an internal critique, not a venue simulation: no acceptance
or rejection prediction, no reviewer scores, no simulated referee
persona. The deliverable is findings and a revision plan.

## Criteria

Grade the artifact against all of these; record in the plan which
apply and why any do not:

- **Proof correctness** — gaps, circularity, unjustified steps,
  incomplete case analyses, coherence obligations asserted rather
  than discharged.
- **Definitional precision** — ambiguous or underdetermined
  definitions; mismatches between the informal gloss and the formal
  statement; overloaded notation doing silent work.
- **Hypothesis completeness** — hypotheses used but never stated;
  hypotheses stated but never used; strictness or truncation
  assumptions smuggled in through examples.
- **Novelty against prior art** — search arXiv (math.CT, cs.LO,
  math.LO, math.AT), nLab, 1lab, and TypeTopology before crediting
  any originality claim; novelty findings obey the honesty rules
  below.
- **Constructivity and univalence-compatibility** — uses of
  excluded middle or choice, set-level assumptions, strict equality
  of objects, or anything else that breaks in a univalent setting.
  Hom-set truncation is flagged wherever it appears: this
  repository never truncates homs (wild categories by design).
- **Mechanizability in cubical Agda** — could the central claims be
  formalized under `--safe --erased-cubical --no-guardedness`, with
  no postulates and no external libraries? Name the obstructions.
- **Status inflation** (internal artifacts only) — cross-check
  every claim against its `docs/gloss.md` ledger status (✅ / 🧪 /
  📐 / ⚠️) and the `src/Gloss/` certificates; flag any claim worded
  stronger than its ledger status.

## Workflow

1. **Plan** — Write `notes/plans/<YYYY-MM-DD>-<slug>.md`: the artifact identity
   and source type, the criteria checklist, the verification checks
   needed (which claims get cross-checked against which sources or
   modules, which linked materials to inspect), a task ledger, and
   a verification log. Summarize the plan briefly to the user and
   continue immediately; ask for confirmation only if the user
   explicitly requested plan review. Keep later ledger edits small;
   if an edit fails or would embed a large block, rewrite the full
   plan file instead, then continue through to final artifact and
   provenance verification.
2. **Inspect** — Read local artifacts with the file-read
   capability; fetch remote pages with the url-fetch capability,
   recording the URL. For a PDF, the url-fetch capability serves
   metadata and the abstract only; stage the document itself on
   disk with the shell capability (`curl -sL -o` to a run-local
   file under `notes/research/`, then `pdftotext`) and read the
   extraction — the document body never enters context via
   url-fetch. When staging or extraction fails, record the failure
   and still produce a partial or blocked review. Inspect linked
   formalizations, code, and cited sources when they are reachable
   and materially affect a finding. For internal artifacts, also
   read `docs/gloss.md` and
   every repository module the artifact cites — a VERIFIED label
   requires naming the module or Gloss certificate that checks the
   claim. Mark every planned check `done`, `blocked`, or
   `superseded` — never silently skip one.
3. **Collect evidence** — Write
   `notes/research/<YYYY-MM-DD>-<slug>-evidence.md` before drafting the review:
   exact quoted passages with their locations, the definitions and
   hypotheses as stated, each claim with the status the artifact
   asserts for it, prior-art candidates found, and every inspected
   path or URL. Every finding in the final review traces to an
   entry here.
4. **Delegate where it pays** — For artifacts large enough to
   benefit, use the subagent-dispatch capability with
   self-contained briefs: `analyzer` for proof-strategy soundness
   and overlap with existing modules, `researcher` for the
   prior-art sweep. The
   researcher writes its evidence to
   `notes/research/<YYYY-MM-DD>-<slug>-research-*.md`, never inline; the
   analyzer delivers an in-reply memo — record its
   load-bearing content in the evidence file with attribution
   before drafting. When a named agent is absent in your harness,
   do that work lead-owned and record the delegation as degraded.
   Never claim a delegation happened without dispatching it.
5. **Critique** — Write the review yourself; the final synthesis is
   never delegated. Grade every finding **FATAL** (a central claim
   fails, a proof is wrong, a definition does not define) /
   **MAJOR** (a real weakness that a revision must address) /
   **MINOR** (cosmetic, notational, presentational). Each finding
   carries an inline annotation quoting the exact passage it
   targets. Label every finding per the contract lexicon
   (`docs/provenance.md` binding). Where a mechanization step would
   settle a finding, propose it — a candidate
   `src/Test/<Name>-<timestamp>.lagda.md` spike, a `docs/gloss.md`
   entry, a `resources/` candidate — recorded in the review, never
   executed by this run.
6. **Verify** — Run the verify protocol per the contract over the
   review draft itself. The adversarial sweep for this workflow:
   findings without a quoted passage, criticisms the
   evidence file does not support, severity inflation, status
   labels stronger than their evidence, novelty language without a
   recorded search, and sections surviving from earlier drafts that
   the final evidence no longer supports.
7. **Deliver** — Save the review to
   `notes/research/<YYYY-MM-DD>-<slug>-review.md` with these sections: Summary
   Assessment; Strengths; Findings (FATAL, MAJOR, MINOR
   subsections, each finding with its quoted passage and epistemic
   label); Verification (every check run, with result or BLOCKED);
   Revision Plan (concrete, ordered fixes plus the proposed spikes
   and ledger entries); Open Questions; Sources. Write the
   provenance sidecar `notes/research/<YYYY-MM-DD>-<slug>-review.provenance.md`
   per the contract. Verify on disk that both files exist
   before stopping. When the artifact could not be parsed or
   critical evidence is unreachable, the review still exists: mark
   the affected sections `Verification: BLOCKED` with the manual
   command a human could run, and keep blocked checks strictly
   separate from actual weaknesses of the artifact.

## Scope

This run writes to `notes/plans/` and `notes/research/` only.
Spikes, `docs/gloss.md` entries, and `resources/` entries are
proposals recorded in the review — never created as a side effect.

## Honesty rules (binding)

- A criticism stands only on a quoted or precisely located passage
  of the artifact; a check that could not run is reported BLOCKED
  with the manual command a human could run, and is never counted
  as a weakness of the artifact.
- No reference supports a finding unless the cited document was
  opened and says what it is cited for; a reference surfaced by
  automated search remains `[unvetted]`, supporting no load-bearing
  finding, until it sheds per the contract's epistemic lexicon;
  record each promotion in the sidecar.
- Novelty language is "we are not aware of prior work", accompanied
  by the searches actually performed — never "new" or "first"; this
  applies both to crediting the artifact's originality and to
  denying it.
- No acceptance prediction, no venue simulation, no score.
