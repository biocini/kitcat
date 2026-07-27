---
description: Audit a formalization against its informal source — statement fidelity, obligation and axiom inventory, definition gaming, and reproducibility of the build.
argument-hint: <formalization-and-source>
disable-model-invocation: true
---

Audit the formalization against its informal source for: $ARGUMENTS

Derive a short slug from the audit target (lowercase, hyphens, no filler
words, ≤5 words). Use this slug for all files in this run.

This is an execution request, not a request to explain the workflow. Continue
immediately.

An audit answers one question: **does the checked code actually establish what
the informal source claims?** A green build is necessary but nowhere near
sufficient.

## Required artifacts

- Plan: `outputs/.plans/<slug>.md`
- Evidence notes: `outputs/.drafts/<slug>-audit-evidence.md`
- Audit report: `outputs/<slug>-audit.md`
- Provenance: `outputs/<slug>-audit.provenance.md`

## Workflow

1. **Toolchain** — Resolve the toolchain block (`.euler/TOOLCHAIN.md`,
   or a `## Toolchain` section in the project `CLAUDE.md`). If absent, ask the
   user for the check command, sorry token(s), and unsafe markers. If the
   checker cannot run, mark mechanical checks `BLOCKED` and continue with
   source-layer and on-disk audits only.
2. **Plan** — Write `outputs/.plans/<slug>.md`: which informal source, which
   library files, which claimed correspondences to check, and the audit
   dimensions (fidelity, obligations, axioms, definitions, reproducibility).
   If the toolchain block defines `probe`, run it as the environment sanity
   check. Briefly summarize the plan and continue immediately. Do not ask for
   confirmation unless the user explicitly requested plan review.
3. **Gather** — Use the `researcher` subagent when the source or codebase is
   large; for narrow targets, read directly. Extract the informal statements
   with anchors (theorem numbers, pages) and the claimed formal counterparts
   with `file:line`. Write evidence notes to
   `outputs/.drafts/<slug>-audit-evidence.md` before writing the report:
   quoted informal statements, quoted formal declarations, side-by-side
   correspondences, and every command run with its outcome.
4. **Fidelity comparison** — For each claimed pair (informal statement ↔
   formal declaration):
   - Do the binders, hypotheses, and conclusion correspond, or is the formal
     version weaker, stronger, vacuous, or differently scoped?
   - Are informal side conditions (nonemptiness, finiteness, decidability,
     freshness) present, silently dropped, or silently added?
   - Is any definition crafted so a "theorem" becomes definitional or trivial
     (definition gaming)?
   - Does the encoding (intrinsic/extrinsic, bundled/unbundled, equality
     choice) change what the statement says relative to the source?
5. **Mechanical inventory** —
   - Run the toolchain block's `check` and record the exact command and
     outcome.
   - Grep the audited files for `sorry-token` and `unsafe-markers`; enumerate
     every hit with `file:line`.
   - Trace dependencies of flagship theorems: do they secretly rest on an
     admitted lemma or an axiom?
   - Reproducibility: if the toolchain block provides `clean-build`, run it
     (or record `BLOCKED` if it would be destructive/slow and the user
     declined). A build that only passes on a dirty checkout is a finding.
6. **Coverage check** — Every informal theorem in scope has a formal
   counterpart or an acknowledged gap; every formal declaration in the audited
   files plays a role or is flagged as scaffolding. Compare against the run's
   informal→formal mapping table when one exists.
7. **Source verification** — When the audit is non-trivial, dispatch the
   `verifier` agent to run the source layer over the evidence notes: confirm
   every informal anchor resolves and supports the quoted statement, and every
   `file:line` still shows the quoted declaration. For narrow audits, do this
   pass yourself. Record confirmed and dead/stale anchors in the evidence
   notes.
8. **Report** — Write exactly one audit artifact to
   `outputs/<slug>-audit.md`:
   - Summary verdict
   - Correspondence table (informal anchor ↔ `file:line` ↔ fidelity status)
   - Findings: mismatches, omissions, gamed definitions, reproduction risks,
     each with severity (FATAL / MAJOR / MINOR) and quoted evidence
   - Mechanical inventory: checker runs, obligation and unsafe-marker counts
   - Coverage gaps
   - `Sources` section with anchors for the informal source and all inspected
     files
9. **Provenance** — Write `outputs/<slug>-audit.provenance.md` with date,
   checker runs performed, sources consulted vs. accepted, and verification
   status (`PASS` / `PASS WITH NOTES` / `BLOCKED`).
10. **On-disk verification** — Before responding, verify that
   `outputs/<slug>-audit.md` and the provenance file exist, and that counts
   quoted in the report match fresh grep output. Do not claim the audit is
   complete unless the files exist.

Severity guidance: a correspondence that is not equivalent in a falsifiable
respect, an open obligation contradicting a completeness claim, or an
undisclosed axiom is FATAL. Missing side conditions and undocumented encoding
choices are MAJOR. Naming, placement, and exposition are MINOR.
