# Provenance: standards for AI-assisted research in this repository

Kitcat is a research library in univalent mathematics developed with
substantial AI assistance under human direction. This document is
the repository's binding standard for honesty, attribution, and
citation in that work. It is also the public statement of how AI
contributes. Every workflow skill, agent, and contributor operates
under these rules.

## Epistemic labels

Claim strength is explicit everywhere (ledger, memos, research
briefs, prose):

- **VERIFIED**: machine-checked in this repository. The label
  always names the module or `Gloss.*` certificate. Nothing else
  carries VERIFIED.
- **SOURCE-CHECKED**: the claimant opened the cited document, and
  it states the claim at the cited location. Orthogonal to
  VERIFIED: a literature claim is typically
  `CONJECTURED, SOURCE-CHECKED against <ref>`.
- **CONJECTURED**: asserted without machine-checking. Every
  mathematical claim harvested from literature or produced in a
  memo is CONJECTURED until the typechecker says otherwise.
  Implementation gates on a spike for conjectured claims.
- **`[unvetted]`**: a reference surfaced by automated search that
  nothing has yet confirmed. No claim may lean on it. It sheds the
  marker in one of two ways. First, an **audited** `resources/`
  entry covers it: identity hash-verified and the independent
  statement audit recorded, the human-free fidelity bar. A bare
  entry without its audit lifts nothing. Second, a human confirms
  the opened document directly. The run's provenance sidecar
  records each promotion (which audited entry, or who). A citation
  on an audited entry, where Lane has not yet exercised discretion,
  carries `audited; discretion pending` there. Lane's ratification
  and veto are self-initiated discretion over the shelf, not a gate
  the pipeline queues behind. A veto retires the entry and voids
  every claim that leaned on it.
- The ledger statuses in `docs/gloss.md` (✅ machine-checked
  committed, 🧪 machine-checked evidence in `Gloss.*`, 📐 rigorous
  argument not mechanized, ⚠️ partially conjectured) govern claim
  strength wherever a result appears. Prose is never worded
  stronger than the status it cites.

## The nine practices

1. **Verified references.** No citation supports a claim unless a
   human opened the cited document and confirmed it says what the
   citation claims. Vetted sources live as `resources/<slug>/`
   entries (citation, vetting record, sha256 of the vendored
   document, with documents local-only and hashes tracked).
   `resources/README.md` is the format authority. Hallucinated
   references are the failure mode this rule exists to make
   impossible.
2. **Machine-checked claim of record.** The mathematics of record
   is what the typechecker accepts. A plausible proof is not a
   proof. The answer to "did the AI get it right" is a kernel check
   or an explicit CONJECTURED label, never confidence.
3. **Definition provenance.** The kernel checks proofs, not that
   definitions capture the intended concepts, and this is a
   definitions-led library. Every definition the development leans
   on documents its informal source (paper, `resources/` entry) or
   its status as original to this repository. A named human vouches
   for the correspondence.
4. **Novelty hygiene.** Novelty claims read "we are not aware of
   prior work" and list the searches actually performed, never
   "new" or "first". Folklore results carry the folklore label.
   When automated search locates prior art, the credit goes to the
   prior art, not the search. Candidate novelty claims carry a
   citation-research-pending flag in the ledger until the search is
   done.
5. **Comprehension gate.** No AI-produced code lands in a commit
   unless the responsible human understands it and can justify its
   design. Kernel acceptance is necessary, not sufficient.
6. **Per-contribution disclosure.** Commits with substantial
   AI-produced content carry the trailer
   `Assisted-by: Claude (<model>)` (or the assisting system). This
   document is the standing repo-level disclosure. The trailers are
   the per-contribution record.
7. **Artifact before announcement.** Public claims never exceed
   what a checked artifact supports. Announcements link the
   machine-checked source or the provenance-carrying document, not
   a summary.
8. **Named human responsibility.** A human (the repository owner)
   takes full responsibility for all content, however generated.
   Disclosure names AI systems as tools, never as authors.
9. **Provenance logs.** Research runs write provenance sidecars
   (sources consulted/accepted/rejected with vetting status,
   blocked capabilities, verification status). Sessions write
   append-only logs in `notes/`, and the latest entry bridges
   sessions, with `docs/roadmap.md` carrying the standing targets.
   Lab-notebook entries (`CHANGELOG.md`) use the run-status
   register `verified / unverified / blocked / inferred`: a
   separate vocabulary from the epistemic labels above, describing
   runs and checks, never mathematical claims. The record of how a
   result came to be is part of the result.

## Code citations

Code adapted from or following an external source carries a credit
comment at the definition that realizes it. The house forms:

```agda
-- Credit: 1lab, Equiv.Fibrewise
-- Following Rijke, Theorem 11.2.4
-- From Capriotti–Kraus (arXiv:1707.03693), Section 3.2
```

The obligation travels with the construction. A construction that
reaches the implementer through an intermediary (an analyzer memo,
a dispatch brief, a `resources/` digest) is still adapted from its
source. The intermediary's citation anchors must land as credit
comments in the code. A handoff never launders provenance.

A credit comment is a citation and meets the same standard as any
other (practice 1). The cited location states the construction,
resolved through the audited `resources/` entry when one covers
the source. A change that adds or alters credit comments receives
a citation review (the `verifier`'s code-citation mode) before
commit. The review is ordered per the contract's verify protocol
(fidelity review before the mechanical gate).

## AI contribution statement

AI assistants (principally Claude, via Claude Code and the Pi
coding agent) produce the proof engineering, literature research,
drafting, and tooling in this repository. They operate under the
direction and review of Lane Biocini, who sets the research
program, makes all rulings, and vouches for every committed
artifact. Machine-checking in Cubical Agda is the trust boundary
for mathematical claims. These standards are the trust boundary for
everything else. Errors are attributable to the human owner, not to
the tools.

## Policy context

These standards calibrate against the external policies below, as
of 2026-07-11. The landscape is moving. Entries carry dates and
name the documents that state them. All opened 2026-07-11:

- arXiv: LLMs are not authors, and authors must report significant
  tool use (2023-01-31,
  <https://blog.arxiv.org/2023/01/31/arxiv-announces-new-policy-on-chatgpt-and-similar-tools/>).
  In May 2026 arXiv's Computer Science section announced a one-year
  submission ban on incontrovertible evidence of unchecked LLM
  content, hallucinated references the canonical trigger. The
  announcement came via its section chair, with no arXiv-hosted
  policy page to date. Coverage:
  <https://library.smu.edu.sg/topics-insights/arxiv-tightens-policy-hallucinated-references-what-researchers-should-know-about>
  (2026-06-10),
  <https://www.insidehighered.com/news/faculty/books-publishing/2026/05/22/ban-authors-who-submit-ai-content-welcome-unenforceable>
  (2026-05-22).
- mathlib contributing guide (the source's own stamp: mid-2026,
  <https://leanprover-community.github.io/contribute/index.html>):
  mandatory AI disclosure on PRs, `LLM-generated` labels,
  contributor comprehension required, own-words rule for community
  prose.
- Leiden Declaration on AI and Mathematics (2026-06-02,
  IMU-endorsed, <https://leidendeclaration.ai/>): tool disclosure
  sections, human responsibility for correctness, proactive
  crediting of sources behind AI-synthesized results, and
  peer-reviewed venues over press releases.
- ACM authorship policy (updated 2026-05-14,
  <https://www.acm.org/publications/policies/new-acm-policy-on-authorship>):
  disclosure of AI writing assistance is no longer required. AI
  used in the conduct of the research still needs a detailed
  description in the methods section. All named authors are
  accountable for problematic content regardless of its source.
- IEEE requires disclosure of AI-generated content in the
  acknowledgments
  (<https://journals.ieeeauthorcenter.ieee.org/become-an-ieee-journal-author/publishing-ethics/guidelines-and-policies/submission-and-peer-review-policies/>).
  Its AI-authorship bar appears at society level (IEEE RAS,
  <https://www.ieee-ras.org/publications/guidelines-for-generative-ai-usage/>)
  and defers IEEE-wide to the PSPB Operations Manual (pp. 5–6, not
  yet opened here). Springer Nature bars LLM authorship and
  requires Methods-section documentation
  (<https://www.nature.com/nature-portfolio/editorial-policies/ai>).
- Agda community: no adopted AI-policy text as of 2026-07-11
  (agda/agda CONTRIBUTING.md and HACKING.md, agda-stdlib HACKING.md
  opened, GitHub code search over both repos). The absence is a
  deliberate, recent decision. A blanket-ban proposal
  (<https://github.com/agda/agda/pull/8456>) closed unmerged
  2026-04-15. <https://github.com/agda/agda/pull/8507> merged
  2026-07-10 with its AI-policy section removed after the
  2026-05-27 developer meeting (the merged CONTRIBUTING.md contains
  no AI language, and the PR body still describes the removed ban).

This repository holds itself to the strictest of these
simultaneously.
