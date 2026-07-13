---
name: hott
description: Look up or explain a concept, definition, or theorem from the univalent-mathematics foundations, grounded in the library's standard reference — Rijke, Introduction to Homotopy Type Theory (resources/rijke-hott/). Use to find the standard definition of a HoTT notion (the identity type, is-equiv, is-contr, the h-level hierarchy, the fundamental theorem, function extensionality, univalence, the circle, …), locate where Rijke treats a topic, or ground a kitcat construction in the foundational text — always separating what Rijke states from what this repository has machine-checked.
argument-hint: <concept | definition | theorem | question>
args: <concept | definition | theorem | question>
section: Research Workflows
topLevelCli: true
---

# HoTT foundations lookup

Look up, in the univalent-mathematics foundations: $ARGUMENTS

Read `.agents/CLAUDE.md` and `.agents/skills/kitcat/HARNESS.md`
first: the contract binds the cross-agent conventions this skill
defers to; HARNESS maps every capability named below to the tools
in your harness.

The reference is the library's foundational source, `resources/rijke-hott/`
(Rijke, *Introduction to Homotopy Type Theory*, arXiv 2212.11082).
This is a reference lookup grounded in the vendored text, not an open
web search; and it is an execution request, not a request to explain
the workflow — resolve the target and answer.

## Locate

Navigate the vendored source through the entry's committed map,
never by guessing a file:

1. Read `resources/rijke-hott/README.md` — the section map lists the
   three parts and every lecture with its subsections and the
   load-bearing definitions/theorems at `<lecture>.tex:LINE`, and the
   **Content digests** section carries statement-level digests of
   those items at the same anchors. Find the target with the
   file-search capability; the digest orients the lookup and often
   carries what the answer needs — but the SOURCE-CHECKED label
   attaches only after the vendored source is read at the anchor
   (step 2). An answer given from the digest alone is cited as
   "per the entry digest at <anchor>", never SOURCE-CHECKED.
2. For anything beyond the digest's statement — hypotheses in full,
   the surrounding development, a proof's shape — read the vendored
   source at the anchor (`resources/rijke-hott/<lecture>.tex`) with
   the file-read capability. The `.tex` is gitignored but present on
   disk; if it is absent, the entry records the re-fetch command —
   report the gap as BLOCKED with that command, do not fabricate the
   statement.
3. When the target is broader than one anchor (a topic, a
   comparison), read the relevant subsections across the lecture,
   and neighbouring lectures the map points to.

## Answer

Deliver in chat, grounded in what the source says:

- **The standard formulation.** State Rijke's definition or theorem
  as the source gives it, with its hypotheses, citing the location
  `rijke-hott/<lecture>.tex:LINE` — SOURCE-CHECKED (the opened
  document states it there). Keep the source's own vocabulary; note
  where the source offers several equivalent formulations (e.g.
  `is-equiv` as bi-invertible vs half-adjoint vs contractible-fibers)
  and which the text takes as primary.
- **The kitcat cross-reference.** Then say what THIS repository has
  of it: a `docs/gloss.md` entry and the module or `Gloss.*`
  certificate that machine-checks it (VERIFIED — name it), or that
  kitcat has no mechanized counterpart yet. Flag any divergence
  between the source's setting and this library's (wild categories,
  `--erased-cubical`, no hom-set conditions, the ternary-first
  idiom) — a kitcat construction inherits the standard vocabulary,
  not necessarily the standard proof.
- **Where to read more.** Point to the lecture and subsection in the
  map for the fuller development.

Keep it proportional: a single-definition lookup is a few sentences
and one citation; a topic ("how does Rijke build the h-levels")
walks the relevant subsections in order.

## Honesty rules (binding)

- SOURCE-CHECKED means the claimant opened the vendored source at
  the cited `<lecture>.tex:LINE` this run and it states the claim
  there; a digest is a derivative and licenses only "per the entry
  digest at <anchor>". Quote or paraphrase only what is actually in
  the text read.
- VERIFIED is reserved for what is machine-checked in THIS repository
  — a named module or `Gloss.*` certificate. Rijke stating a theorem
  is never VERIFIED for kitcat; it is the source's claim.
- The entry's standing governs what a citation on it may bear (the
  contract's Ingestion section: the statement audit is the
  load-bearing gate; Lane's discretion is separate and
  self-initiated). Note the standing when a caller leans on the
  entry as authority — and a mathematical claim stays CONJECTURED
  until machine-checked in this repository, whatever the entry's
  standing.
- A capability with no visible tool, or a missing vendored file, is
  reported BLOCKED with the manual command a human could run; never
  simulate the source or invent a statement or a line number.

This skill reads the reference and answers in chat; it writes no
files and edits nothing. A gap it exposes — a notion kitcat should
mechanize, a map anchor that has drifted — is a proposal stated in
chat, never executed as a side effect.
