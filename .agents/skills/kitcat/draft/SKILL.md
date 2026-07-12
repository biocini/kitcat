---
name: draft
description: Turn collected research — notes/research/ files, docs/gloss.md entries, Gloss certificates — into one polished paper-style mathematical exposition with LaTeX, theorem statements carrying their ledger status, and full citation. Use when asked to write a paper, draft an exposition, write up findings or a research thread, produce a formalization report, or turn notes into a document. Produces a cited paper in notes/research/ with a provenance sidecar.
argument-hint: <topic-or-research-thread>
args: <topic-or-research-thread>
section: Research Workflows
topLevelCli: true
---

# Paper Draft

Write a paper-style exposition for: $ARGUMENTS

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness.

Derive a short slug from the topic (lowercase, hyphens, no filler
words, at most 5 words). Every file this run writes uses that slug.

This is an execution request, not a request to explain the workflow.
Begin with the plan artifact, not with prose about the protocol.

## Hard rules (binding on every draft)

1. **Every theorem statement carries its ledger status with it.**
   Each definition, theorem, lemma, and proposition is tagged where
   it is stated with its `docs/gloss.md` status (✅ machine-checked
   committed / 🧪 machine-checked evidence in `Gloss.*` / 📐 rigorous
   argument, not mechanized / ⚠️ partially conjectured) or, for
   claims outside the ledger, VERIFIED or CONJECTURED. A statement
   never appears stronger than its status: no bare "Theorem" whose
   proof is a sketch, no prose paraphrase that drops the tag its
   formal statement carries.
2. **Every formal claim cites its provenance.** Each formal claim
   names the module that proves it, the `Gloss.*` certificate that
   evidences it, or the external source that states it. A claim with
   none of the three does not appear as a claim — see the gap rule
   below.

## Inputs

This workflow synthesizes what already exists; it is not a research
run. Draw from, in priority order: `notes/research/` files on the
topic, `docs/gloss.md` entries and their `src/Gloss/` certificates,
`resources/` vetted source entries (cite these by entry when they
cover a source), and the latest `notes/session-logs/` entry plus
`docs/roadmap.md` for current-state context. Use the
file-search and file-read capabilities to collect them; confirm a
cited module's status against `docs/gloss.md` rather than assuming
it from a note. When the collected material is too thin to support
the requested exposition, say so and ask — with the user-question
capability when needed — rather than padding with invention.

## Workflow

1. **Plan** — Write `notes/plans/<slug>.md`: proposed title, the
   section outline, the key claims the paper will make, the source
   material each claim draws from, a task ledger, and a verification
   log keying every load-bearing claim to its `docs/gloss.md` entry,
   `Gloss.*` certificate, module, or external source — claims with
   no key are marked as gaps up front. Summarize the plan briefly to
   the user and continue immediately; ask for confirmation only if
   the user explicitly requested outline review. Keep later ledger
   edits small; if an edit fails or would embed a large block,
   rewrite the full plan file instead, then continue through to
   final artifact and provenance verification. Mark every planned
   section and claim `done`, `blocked`, or `superseded` — never
   silently skip one.
2. **Draft** — Write the exposition yourself; synthesis is never
   delegated. Clean Markdown with LaTeX where it materially helps —
   displayed equations, typing rules, commuting diagrams described
   in prose or Mermaid when the structure is source-supported.
   Sections, adapted as the material demands but never dropping the
   mechanization-status section:
   - title and abstract
   - introduction / problem statement
   - definitions
   - main results, with proofs or proof sketches (a sketch is
     labeled a sketch)
   - mechanization status — which modules typecheck under the
     library's flags, which `Gloss.*` certificates exist, which
     `src/Test/` spikes support a claim, and what remains
     unmechanized
   - related work
   - limitations and open questions
   - sources appendix with direct URLs or DOIs for all external
     references

   Nothing is invented. A result the exposition needs but the
   repository and sources do not supply appears as an explicit
   labeled gap — `**GAP:** <what is missing and what would close
   it>` — never as connective prose that implies the result holds.
   Diagrams and comparison tables appear only when source-supported
   and decision-changing; every one carries its provenance.
3. **Cite** — Attach inline citations per the hard rules. Epistemic
   labels are strict: VERIFIED applies only to claims
   machine-checked in this repository (name the module or Gloss
   certificate); every mathematical claim harvested from literature
   is CONJECTURED, typically written `CONJECTURED, SOURCE-CHECKED
   against <ref>`. Check every external source with the url-fetch
   capability: the URL resolves, and the document states what it is
   cited for — record that as SOURCE-CHECKED. References surfaced by
   automated search are `[unvetted]` and never support a
   load-bearing claim; a reference sheds `[unvetted]` only when a
   human confirms the opened document or a `resources/` entry covers
   it — record each promotion (who, or which entry) in the sidecar.
   Novelty language is "we are not aware of prior work" plus the
   searches performed — never "new" or "first".
4. **Verify** — Run an adversarial pass over the cited draft:
   statements stronger than their ledger status, claims without a
   module / certificate / source, proofs presented as complete that
   are sketches, gaps smoothed into prose, single-source critical
   claims, overstated confidence, novelty language without a
   recorded search, and sections surviving from earlier drafts that
   the final evidence no longer supports. Dispatch the
   `verifier` agent when present — it re-checks the
   citations and runs this adversarial pass; otherwise self-review
   and record the delegation as degraded. Grade findings FATAL /
   MAJOR / MINOR. Fix FATAL findings before delivery and run one
   more pass after the fixes; note MAJOR findings in Limitations and
   Open Questions; accept MINOR. Sweep once more for any claim that
   sounds stronger than its support: downgrade or remove it now
   rather than deliver it.
5. **Deliver** — Save exactly one final draft to
   `notes/research/<slug>-paper.md` and its provenance sidecar to
   `notes/research/<slug>-paper.provenance.md` recording: date and
   who requested the draft; sources consulted vs accepted vs
   rejected (with reasons), each accepted source with its vetting
   status (`[unvetted]` / SOURCE-CHECKED / `resources/` entry); the
   input files used — notes, gloss entries, certificates — each with
   its producer (which agent, or lead-owned degraded); the gaps left
   in the draft; blocked capabilities and degraded delegations, each
   with what was done instead; and verification status — PASS (clean
   final pass), PASS WITH NOTES (MAJOR findings remain in
   Limitations and Open Questions), or BLOCKED (a required check
   could not run; name it). Sources worth permanent vetting are
   proposed in the sidecar as candidate `resources/` entries, not
   created unilaterally. Verify on disk that both files exist before
   stopping; never stop at an intermediate draft.

## Scope guard

A draft run writes only `notes/plans/<slug>.md` and
`notes/research/<slug>-paper*.md` — no `docs/` edits, no `src/`
edits, no spikes, no ledger changes. Mechanization work the draft
reveals as needed (spikes to run, gloss entries to add, `resources/`
entries to vet) is proposed in the draft's open questions and the
sidecar, never executed as a side effect.

## Honesty rules (binding)

- No reference supports a claim unless the cited document was opened
  and says what it is cited for; a reference surfaced by automated
  search remains `[unvetted]` — supporting no load-bearing claim —
  until a human or a `resources/` entry confirms it.
- Blocked capabilities and failed checks are reported as BLOCKED in
  the provenance sidecar; a missing check is never smoothed over.
