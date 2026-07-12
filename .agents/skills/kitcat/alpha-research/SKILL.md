---
name: alpha-research
description: Acquire and question academic papers for the research workflows in type theory, category theory, univalent mathematics, and programming language foundations. Use when asked to find papers on a topic, fetch or read a specific paper by arXiv id or DOI, ask questions about a paper, inspect a paper's accompanying formalization repository, verify a vendored document against its recorded hash, or prepare a source for a resources/ entry. Delivers fetched documents, hashes, and paper answers into the requesting workflow's run.
argument-hint: <paper-id-or-query>
args: <paper-id-or-query>
section: Utilities
---

# Paper Acquisition

Search, fetch, or question papers for: $ARGUMENTS

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness. The
paper-search capability resolves through tiers — a dedicated paper
tool set, a paper CLI via shell, or web-search plus url-fetch — and
every tier reaches all of arXiv. Paper questions go to paper-search,
current topics to web-search and url-fetch, mixed questions to both
with the two evidence streams kept distinct. This skill runs inside
a requesting workflow (a review, comparison, audit, or direct
request); its findings, hashes, and proposals are recorded in that
workflow's run artifact and provenance sidecar. On a direct request
with no enclosing workflow, findings and BLOCKED reports are
delivered in chat, and any working copies still go to
`notes/research/` with their hashes stated.

Before searching outward, check what the repository already holds:
`resources/` (vetted entries — cite by entry when one covers the
source) and `docs/gloss.md`. Prefer semantic search when the tier
offers modes. When paper-search degrades to web-search plus
url-fetch, scope queries to the primary venues: arXiv (math.CT,
cs.LO, math.LO, math.AT), nLab, 1lab, TypeTopology, author pages,
proof-assistant library documentation.

Every reference surfaced by automated search is `[unvetted]`,
supporting no load-bearing claim until a human confirms the opened
document or a `resources/` entry covers it; each promotion (who
confirmed, or which entry) is recorded in the requesting workflow's
provenance sidecar. A tier that fails on authentication or a
missing tool is reported BLOCKED with the manual command a human
could run; never simulate a search or claim its result.

## Fetching and questioning

Fetch by stable identifier — arXiv id or DOI — never a mutable
landing page when one exists. Compute the sha256 of any vendored
file the moment it lands (`shasum -a 256 <file>` via shell) and
record hash and filename. A user-supplied file for an existing
`resources/` entry is verified against the entry's recorded hash
before anything is cited from it; a mismatch is FATAL — stop, cite
nothing, and resolve with the user which document the entry
describes. A fetched copy for a source with no entry is a working
copy: it lives with the requesting run's intermediates in
`notes/research/`, hash recorded, so a later entry can adopt it.

Q&A runs against the vendored local copy — never a remembered
abstract or a search snippet; fetch the full text when checking
exact statements. Paper claims are `CONJECTURED, SOURCE-CHECKED
against <ref>`; VERIFIED only for machine-checked claims naming the
module or Gloss certificate. An accompanying formalization
repository (Agda, Coq, Lean) is read with url-fetch as reference
only — SOURCE-CHECKED at best, VERIFIED only when re-checked here.

## Feeding resources/ and scope

`resources/README.md` is the format authority. Acquisition prepares
the raw material an entry needs — citation record, sha256 and
filename, what the document was checked to say — and proposes the
candidate entry in the requesting workflow's provenance sidecar;
only the human vetting step creates entries, with the working copy
in `notes/research/` available for adoption. This skill writes only
working copies and evidence notes under `notes/research/`: no
`resources/` writes, no `docs/` or `src/` edits.
