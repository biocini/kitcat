---
name: audit
description: Audit a paper in type theory, category theory, univalent mathematics, or programming language foundations against a formalization — compare stated definitions, theorem statements, and hypotheses against a mechanization (this repository's modules, or an external formalization read as reference only). Use when asked to audit a paper, check statement-versus-mechanization consistency, find hypothesis or definitional mismatches, or determine what a paper claims versus what is actually machine-checked. Produces a claim-by-claim audit table in notes/research/ with a provenance sidecar.
argument-hint: <paper-and-formalization>
args: <paper-and-formalization>
section: Research Workflows
topLevelCli: true
---

# Paper-Formalization Audit

Run a paper-versus-formalization audit for: $ARGUMENTS

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness.

Derive a short slug from the audit target (lowercase, hyphens, no
filler words, at most 5 words). Every file this run writes uses that
slug.

This is an execution request, not a request to explain the workflow.
Begin with the plan artifact, not with prose about the protocol.

## Scope

The comparison target is a mechanization: either this repository's
modules — where `docs/gloss.md` (the theorem ledger) and the frozen
`Gloss.*` certificates are the ground truth for what is actually
proven — or an external formalization (1lab, TypeTopology, a
proof-assistant library), which is read as reference only and never
modified. An audit reports findings; remediation is at most
proposed in the artifact. A run writes nothing outside `notes/` —
no `src/` edits, no `docs/` edits, no spikes.

## Audit dimensions

Check each claim along these axes:

- **Definitional choices** — does the formalization's definition
  coincide with the paper's, or a provably equivalent variant, or a
  genuinely different object?
- **Implicit hypotheses** — assumptions the paper uses without
  stating, or that the formalization requires but the paper omits
  (and the reverse).
- **Strictness versus weakness** — strict equalities in the paper
  realized as paths, coherences, or higher cells; on-the-nose
  commutativity versus up-to-homotopy.
- **Universe handling** — level polymorphism, size conditions,
  smallness or local-smallness assumptions the paper glosses over.
- **Truncation assumptions** — h-level conditions the paper imposes
  that the formalization does or does not. This library never
  truncates homs: a paper's hom-set assumption versus wild homs here
  is a reportable delta, not something to fix.
- **Constructivity** — choice principles, excluded middle,
  impredicativity, or classical steps the paper uses that a
  constructive mechanization cannot.

Also flag unproven or postulated steps on the formalization side,
and mechanization risk: paper claims whose formalization would be
substantially harder than the paper's presentation suggests.

## Workflow

1. **Plan** — Write `notes/plans/<slug>.md`: which paper (URL or
   DOI), which formalization (repository modules, or an external
   library and version), the claims to check, a task ledger, and a
   verification log. Summarize the plan briefly to the user and
   continue immediately; ask for confirmation only if the user
   explicitly requested plan review. Keep later ledger edits small;
   if an edit fails or would embed a large block, rewrite the full
   plan file instead, then continue through to final artifact and
   provenance verification.
2. **Gather** — Paper side: retrieve the paper with the url-fetch
   capability; use the paper-search and web-search capabilities to
   locate the current version, errata, and companion material.
   Formalization side: when auditing this repository, read the
   modules with the file-read and file-search capabilities and
   consult `docs/gloss.md` and `resources/` before searching
   outward; dispatch the `analyzer` agent for dependency and
   module-structure questions. When the sweep is wide enough to
   benefit from delegated triage, dispatch the `researcher`
   agent with a self-contained brief; its evidence notes go to
   `notes/research/<slug>-research-*.md`, never inline. When a named
   agent is absent in your harness, do the work lead-owned and
   record the delegation as degraded. Mark every planned claim
   `done`, `blocked`, or `superseded` — never silently skip one.
3. **Compare** — Build the claim-by-claim table yourself; the
   comparison judgment is never delegated. One row per paper claim,
   with columns: paper statement (with its location in the paper) |
   formalization artifact (module and definition name) | status. The
   statuses:
   - **MATCHES** — the formalization states and proves the claim.
     In this repository, a MATCHES row carries a VERIFIED citation:
     the module or `Gloss.*` certificate, machine-checked. Against
     an external formalization, MATCHES is at most SOURCE-CHECKED —
     external code is never VERIFIED.
   - **MISMATCH** — state the delta precisely: which hypothesis,
     which definitional choice, which strictness or truncation
     divergence, and in whose favor.
   - **OMITTED** — the claim has no formalization counterpart.
   - **IMPLICIT-HYPOTHESIS** — one side relies on a hypothesis the
     other does not state; name the hypothesis and the side that
     hides it.
4. **Cite** — Add inline citations and check every source with the
   url-fetch capability: the URL resolves, and the document states
   what it is cited for — record that as SOURCE-CHECKED. Epistemic
   labels are strict: VERIFIED applies only to claims machine-checked
   in this repository (name the module or Gloss certificate); every
   mathematical claim harvested from the paper or an external
   formalization is CONJECTURED, typically written
   `CONJECTURED, SOURCE-CHECKED against <ref>`. References surfaced
   by automated search are `[unvetted]` and never support a
   load-bearing claim; a reference sheds `[unvetted]` only when a
   human confirms the opened document or a `resources/` entry covers
   it — record each promotion (who, or which entry) in the sidecar.
5. **Verify** — Run an adversarial pass over the draft: table rows
   whose status is stronger than their evidence (a MATCHES without a
   named module, a MISMATCH whose delta is vague), unsupported
   claims, single-source critical claims, overstated confidence,
   novelty language without a recorded search, and sections
   surviving from earlier drafts that the final evidence no longer
   supports. Dispatch the `verifier` agent when present —
   it re-checks the citations and runs this adversarial pass;
   otherwise self-review. Grade findings FATAL / MAJOR / MINOR. Fix
   FATAL findings before delivery and run one more pass after the
   fixes; note MAJOR findings in Open Questions; accept MINOR.
6. **Deliver** — Save the audit to `notes/research/<slug>-audit.md`,
   ending with a Sources section listing the paper (URL or DOI) and
   the formalization (module paths for this repository, repository
   URL and version for an external one). Save its provenance sidecar
   to `notes/research/<slug>-audit.provenance.md` recording: date
   and who requested the audit; sources consulted vs accepted vs
   rejected (with reasons), each accepted source with its vetting
   status (`[unvetted]` / SOURCE-CHECKED / `resources/` entry); the
   intermediate research files used, each with its producer (which
   agent, or lead-owned degraded); blocked capabilities and degraded
   delegations, each with what was done instead; and verification
   status — PASS (clean final pass), PASS WITH NOTES (MAJOR findings
   remain in Open Questions), or BLOCKED (a required check could not
   run; name it). Sources worth permanent vetting are proposed in
   the sidecar as candidate `resources/` entries, not created
   unilaterally. Verify on disk that both files exist before
   stopping; never stop at an intermediate draft.

## Honesty rules (binding)

- VERIFIED means machine-checked in this repository, nothing else;
  an external formalization's proof supports at most SOURCE-CHECKED.
- No reference supports a claim unless the cited document was opened
  and says what it is cited for; and a reference surfaced by
  automated search remains `[unvetted]` — supporting no load-bearing
  claim — until a human or a `resources/` entry confirms it.
- Findings are reported, never fixed mid-audit; every remediation is
  a proposal inside the audit artifact.
- Blocked capabilities and failed checks are reported as BLOCKED in
  the provenance sidecar; a missing check is never smoothed over.
