# Provenance — standards for AI-assisted research in this repository

Kitcat is a research library in univalent mathematics developed with
substantial AI assistance under human direction. This document is
the repository's binding standard for honesty, attribution, and
citation in that work, and its public statement of how AI
contributes. Every workflow skill, agent, and contributor operates
under these rules.

## Epistemic labels

Claim strength is explicit everywhere — ledger, memos, research
briefs, prose:

- **VERIFIED** — machine-checked in this repository. The label
  always names the module or `Gloss.*` certificate. Nothing else
  carries VERIFIED.
- **SOURCE-CHECKED** — the cited document was opened by the claimant
  and states the claim at the cited location. Orthogonal to
  VERIFIED: a literature claim is typically
  `CONJECTURED, SOURCE-CHECKED against <ref>`.
- **CONJECTURED** — asserted without machine-checking. Every
  mathematical claim harvested from literature or produced in a memo
  is CONJECTURED until the typechecker says otherwise;
  implementation gates on a spike for conjectured claims.
- **`[unvetted]`** — a reference surfaced by automated search that
  nothing has yet confirmed. It supports no load-bearing claim, and
  it sheds the marker when an **audited** `resources/` entry covers
  it — identity hash-verified and the independent statement audit
  recorded, the human-free fidelity bar; a bare entry without its
  audit lifts nothing — or when a human confirms the opened
  document directly. Each promotion is recorded (which audited
  entry, or who) in the run's provenance sidecar; a citation on an
  audited entry where Lane's discretion is unexercised carries
  `audited; discretion pending` there. Lane's ratification and veto
  are self-initiated discretion over the shelf, not a gate the
  pipeline queues behind; a veto retires the entry and voids every
  claim that leaned on it.
- The ledger statuses in `docs/gloss.md` (✅ machine-checked
  committed, 🧪 machine-checked evidence in `Gloss.*`, 📐 rigorous
  argument not mechanized, ⚠️ partially conjectured) govern claim
  strength wherever a result is mentioned: prose is never worded
  stronger than the status it cites.

## The nine practices

1. **Verified references.** No citation supports a claim unless a
   human opened the cited document and confirmed it says what it is
   cited for. Vetted sources live as `resources/<slug>/` entries
   (citation, vetting record, sha256 of the vendored document —
   documents local-only, hashes tracked; `resources/README.md` is
   the format authority). Hallucinated references are the failure
   mode this rule exists to make impossible.
2. **Machine-checked claim of record.** The mathematics of record is
   what the typechecker accepts. A plausible proof is not a proof;
   the answer to "did the AI get it right" is a kernel check or an
   explicit CONJECTURED label, never confidence.
3. **Definition provenance.** The kernel checks proofs, not that
   definitions capture the intended concepts — and this is a
   definitions-led library. Every load-bearing definition documents
   its informal source (paper, `resources/` entry) or its status as
   original to this repository, and a named human vouches for the
   correspondence.
4. **Novelty hygiene.** Novelty claims are worded "we are not aware
   of prior work", accompanied by the searches actually performed —
   never "new" or "first". Folklore results are labeled folklore.
   When automated search locates prior art, the prior art is
   credited, not the search. Candidate novelty claims carry a
   citation-research-pending flag in the ledger until the search is
   done.
5. **Comprehension gate.** No AI-produced code is committed unless
   the responsible human understands it and can justify its design.
   Kernel acceptance is necessary, not sufficient.
6. **Per-contribution disclosure.** Commits with substantial
   AI-produced content carry the trailer
   `Assisted-by: Claude (<model>)` (or the assisting system). This
   document is the standing repo-level disclosure; the trailers are
   the per-contribution record.
7. **Artifact before announcement.** Nothing is claimed publicly
   beyond what a checked artifact supports; announcements link the
   machine-checked source or the provenance-carrying document, not a
   summary.
8. **Named human responsibility.** A human (the repository owner)
   takes full responsibility for all content, however generated. AI
   systems are disclosed as tools and are never authors.
9. **Provenance logs.** Research runs write provenance sidecars
   (sources consulted/accepted/rejected with vetting status, blocked
   capabilities, verification status); sessions write append-only
   logs in `notes/session-logs/`, and the latest entry bridges sessions,
   with `docs/roadmap.md` carrying the standing targets. Lab-notebook
   entries (`CHANGELOG.md`) use the run-status register
   `verified / unverified / blocked / inferred` — a separate
   vocabulary from the epistemic labels above, describing runs and
   checks, never mathematical claims. The record
   of how a result was produced is part of the result.

## AI contribution statement

Proof engineering, literature research, drafting, and tooling in
this repository are produced by AI assistants (principally Claude,
via Claude Code and the Pi coding agent) operating under the
direction and review of Lane Biocini, who sets the research program,
makes all rulings, and vouches for every committed artifact.
Machine-checking in Cubical Agda is the trust boundary for
mathematical claims; these standards are the trust boundary for
everything else. Errors are attributable to the human owner, not to
the tools.

## Policy context

External policies these standards are calibrated against, as of
2026-07-11 (the landscape is moving; entries are date-stamped and
each names the document that states it; all opened 2026-07-11):

- arXiv: LLMs are not authors; significant tool use is reported
  (2023-01-31,
  <https://blog.arxiv.org/2023/01/31/arxiv-announces-new-policy-on-chatgpt-and-similar-tools/>).
  In May 2026 arXiv's Computer Science section announced — via its
  section chair, with no arXiv-hosted policy page to date — a
  one-year submission ban on incontrovertible evidence of
  unchecked LLM content, hallucinated references the canonical
  trigger; coverage:
  <https://library.smu.edu.sg/topics-insights/arxiv-tightens-policy-hallucinated-references-what-researchers-should-know-about>
  (2026-06-10),
  <https://www.insidehighered.com/news/faculty/books-publishing/2026/05/22/ban-authors-who-submit-ai-content-welcome-unenforceable>
  (2026-05-22).
- mathlib contributing guide (the source's own stamp: mid-2026;
  <https://leanprover-community.github.io/contribute/index.html>):
  mandatory AI disclosure on PRs, `LLM-generated` labels,
  contributor comprehension required, own-words rule for community
  prose.
- Leiden Declaration on AI and Mathematics (2026-06-02,
  IMU-endorsed; <https://leidendeclaration.ai/>): tool disclosure
  sections; human responsibility for correctness; proactive
  crediting of sources behind AI-synthesized results;
  peer-reviewed venues over press releases.
- ACM authorship policy (updated 2026-05-14,
  <https://www.acm.org/publications/policies/new-acm-policy-on-authorship>):
  disclosure of AI writing assistance is no longer required; AI
  used in the conduct of the research must still be described in
  detail in the methods section; all named authors are accountable
  for problematic content regardless of its source.
- IEEE requires disclosure of AI-generated content in the
  acknowledgments
  (<https://journals.ieeeauthorcenter.ieee.org/become-an-ieee-journal-author/publishing-ethics/guidelines-and-policies/submission-and-peer-review-policies/>);
  its AI-authorship bar is stated at society level (IEEE RAS,
  <https://www.ieee-ras.org/publications/guidelines-for-generative-ai-usage/>)
  and deferred IEEE-wide to the PSPB Operations Manual (pp. 5–6,
  not yet opened here). Springer Nature bars LLM authorship and
  requires Methods-section documentation
  (<https://www.nature.com/nature-portfolio/editorial-policies/ai>).
- Agda community: no adopted AI-policy text as of 2026-07-11
  (agda/agda CONTRIBUTING.md and HACKING.md, agda-stdlib
  HACKING.md opened; GitHub code search over both repos) — and
  the absence is a deliberate, recent decision: a blanket-ban
  proposal (<https://github.com/agda/agda/pull/8456>) closed
  unmerged 2026-04-15, and
  <https://github.com/agda/agda/pull/8507> merged 2026-07-10 with
  its AI-policy section removed after the 2026-05-27 developer
  meeting (the merged CONTRIBUTING.md contains no AI language;
  the PR body still describes the removed ban).

This repository holds itself to the strictest of these
simultaneously.
