---
name: hott
description: Look up or explain a concept, definition, or theorem from the univalent-mathematics and cubical foundations, grounded in the library's foundational references — Rijke, Introduction to Homotopy Type Theory (resources/rijke-hott/) and its cubical-idiom companion, Bentzen, Naive cubical type theory (resources/bentzen-naive-cubical/). Use to find the standard definition of a HoTT notion (the identity type, is-equiv, is-contr, the h-level hierarchy, the fundamental theorem, function extensionality, univalence, the circle, …), understand cubical reasoning (paths as functions of the interval, transport, hcomp and composition scenarios, connections, the cubical groupoid laws, dependent paths), locate where the references treat a topic, or ground a kitcat construction in the foundational texts — always separating what a source states from what this repository has machine-checked.
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

The reference is the library's foundational shelf — the contract's
"Foundational references" section owns the entry list and the
grounding convention; this lookup grounds in two of its entries:
`resources/rijke-hott/` (Rijke, *Introduction to Homotopy Type
Theory*) for the univalent-mathematics vocabulary and theorem
statements, and its cubical-idiom companion
`resources/bentzen-naive-cubical/` (Bentzen, *Naive cubical type
theory*) for the cubical reasoning idiom — interval and path
primitives, transport and composition scenarios, connections, the
cubical groupoid laws, dependent paths. Bentzen develops no
univalence: univalent-foundations lookups stay grounded in Rijke.
This is a reference lookup grounded in the vendored texts, not an
open web search; and it is an execution request, not a request to
explain the workflow — resolve the target and answer.

## Locate

Ground per the contract's Foundational references convention —
through the entry's committed map and digests, never a guessed
file:

1. Choose the grounding entry by register: univalent-mathematics
   definitions and theorem statements ground in Rijke; the cubical
   reasoning idiom grounds in Bentzen. A target spanning both
   registers (a path-algebra law and its cubical derivation, say)
   reads both.
2. Read the entry's README (`resources/<entry>/README.md`): locate
   the target in the entry's section map and its statement-level
   digest with the file-search capability. The digest orients the
   lookup and often carries what the answer needs; the convention
   governs what a digest-only answer may claim.
3. For anything beyond the digest's statement — hypotheses in full,
   the surrounding development, a proof's shape — read the vendored
   source at the anchor (`resources/rijke-hott/<lecture>.tex`,
   `resources/bentzen-naive-cubical/ictt.tex`) with the file-read
   capability. The `.tex` is gitignored but present on disk; a
   missing file is reported per the convention, never fabricated.
4. When the target is broader than one anchor (a topic, a
   comparison), read the relevant subsections across the lecture or
   section, and neighbouring ones the map points to.

## Answer

Deliver in chat, grounded in what the source says:

- **The standard formulation.** State the definition or theorem as
  the grounding entry gives it, with its hypotheses, citing the
  location (`rijke-hott/<lecture>.tex:LINE` or
  `bentzen-naive-cubical/ictt.tex:LINE`) — SOURCE-CHECKED (the
  opened document states it there) — and naming which entry grounds
  which register: Rijke for the univalent-mathematics statement,
  Bentzen for the cubical idiom. Keep the source's own vocabulary;
  note where a source offers several equivalent formulations (e.g.
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
- **Where to read more.** Point to the lecture or section and the
  subsection in the entry's map for the fuller development.

Keep it proportional: a single-definition lookup is a few sentences
and one citation; a topic ("how does Rijke build the h-levels",
"how does Bentzen derive the connections") walks the relevant
subsections in order.

## Honesty rules (binding)

- SOURCE-CHECKED and the digest-only citation form follow the
  contract's Foundational references convention; either label
  attaches only to what was actually resolved at its anchor this
  run. Quote or paraphrase only what is actually in the text read.
- VERIFIED is reserved for what is machine-checked in THIS repository
  — a named module or `Gloss.*` certificate. A shelf entry stating a
  theorem is never VERIFIED for kitcat; it is the source's claim.
- The entry's standing governs what a citation on it may bear (the
  contract's Ingestion section: the statement audit is the
  load-bearing gate; Lane's discretion is separate and
  self-initiated). Note the standing when a caller leans on the
  entry as authority — and a mathematical claim stays CONJECTURED
  until machine-checked in this repository, whatever the entry's
  standing.
- A capability with no visible tool is reported BLOCKED with the
  manual command a human could run; never simulate the source or
  invent a statement or a line number.

This skill reads the reference and answers in chat; it writes no
files and edits nothing. A gap it exposes — a notion kitcat should
mechanize, a map anchor that has drifted — is a proposal stated in
chat, never executed as a side effect.
