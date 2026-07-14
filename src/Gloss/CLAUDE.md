# Gloss/ — frozen evidence certificates

`Gloss.*` modules are machine-checked certificates backing entries
in `docs/gloss.md`. They are tracked, in `All`, and immutable in
a specific sense: they witness what was proven, at the commit it
was proven against.

## Invariants (hold for every file here)

- **Ledger bijection**: every Gloss module is named by a 🧪 entry
  in docs/gloss.md, and every 🧪 entry names its Gloss module.
  A header line states the entry: `Gloss: machine-checked evidence
  for Tnn in docs/gloss.md.`
- **Self-contained modulo Core**: imports from `Core.*` and other
  `Gloss.*` modules ONLY — never `Cat.*` or other volatile
  namespaces. Every needed Cat.* definition is inlined as a frozen
  copy marked `Frozen from <Module> @ <commit>`.
- **Nominal identity**: inlined records are nominally distinct
  types. A Gloss file consuming another Gloss file's frozen
  INSTANCE must import that file's frozen RECORD (Gloss-internal
  import) — never re-freeze its own copy.
- **Proof content is immutable.** Never edit a frozen block or a
  certificate's proofs except as an intentional re-freeze at a new
  named commit (update the `@ <commit>` markers together). A
  comment-only re-freeze — revising run-idiom comments inside a
  certificate's fences — keeps every code token byte-identical to
  the source at pin: only comment text changes (full comment lines
  or trailing comments on code lines), the markers of the touched
  frozen blocks gain a re-freeze clause (certificate-owned fences
  carry no markers — their comment edits are free, enumerated in
  the freeze report like the rest), every comment delta is
  enumerated old→new in the freeze report, and a re-typecheck
  proves the edit innocuous. A comment that is the source module's own text inside
  a frozen block is a fact of the source and is carried, never
  revised. If a claim needs revision, fix the ledger entry, not
  the evidence.
- Names are descriptive PascalCase, no timestamps (timestamps
  belong to `Test/`).

## Presentation (Lane, 2026-07-13 — Glosses are public-facing)

The name "Gloss" is chosen after glosses in actual mathematical
texts: a digression relevant to the mainline of inquiry, written
to be read. The presentation standard is HIGHER than Test/:

- **Synopsis, mandatory, at the very beginning**: a comprehensive
  opening section describing the theorem(s) the certificate
  houses and where each is located in the document (an identifier
  name suffices), explaining the relevance and the context of the
  result — the reader grasps the motivation and the mathematical
  meaning before any code.
- **Register**: a Gloss is readable by someone with no
  familiarity with this repository's operations, roadmap, or
  internal taxonomy — a comprehensible mathematical artifact,
  illuminating when read in the future and directly able to
  assist inclusion in a mathematical paper or thesis. Its
  terminology is standard mathematical vocabulary, the artifact's
  own identifiers (module and definition names), or a coinage
  that carries mathematical content and is defined at first use.
  Operational vocabulary is a violation anywhere in a
  certificate's prose or comments: ledger entry numbers (`T11`),
  run and arc names, memo and review references, and contentless
  internal shorthand (`Layer B`, `arm 2`). Cross-reference a
  companion certificate by module name (`Gloss.PropPinning`), and
  state a cited result's content, never its ledger number.
- **No templated prose**: stock sentences and
  formulaic boilerplate recurring across certificates are an
  antipattern — each certificate is written fresh, as an original
  mathematical text about its own result. Custody metadata is the
  sole sanctioned recurring form: the bijection header line and
  the `Frozen from … @ <commit>` markers — custody, not
  exposition.
- **Division of labor**: `Test/` is the tier
  for scrap work, in-flight decisions, pre-registered run
  criteria, and everything that benefits from the repository's
  operational idiom and cross-references; `Gloss/` is the
  canonization tier — the formal mathematical presentation of a
  result that deserves it. Content that still needs the
  operational register to be understood is not ready for Gloss.
- **Outcomes are stated as mathematics, never as run vocabulary**:
  verdict apparatus (`VERDICT`, `DERIVED`,
  `STUCK`, `GATE`, `WALL`, kill criteria) is the dispatch
  contract's language and stays in `Test/`. A certificate states
  what is proven (with the proof), what is refuted (with the
  countermodel), and what is not derivable (with the documented
  obstruction — the rejected term and the missing equation, in
  plain language around the preserved raw residue). Where the
  method matters mathematically (routes fixed in advance of the
  attempt), narrate it in one plain sentence; the apparatus stays
  out. Agda identifiers inside frozen code are facts of the
  artifact — prose may name them, and renaming one is a
  code-level re-freeze decision escalated to Lane, never a prose
  edit. Ledger locators follow the certificate: when a retrofit
  renames a heading or label that docs/gloss.md cites, the
  entry's citation updates in the same change — fix the pointer,
  never keep rag for the pointer's sake.
- **The standard covers the whole document, not just the
  synopsis**: section prose is expository, never terse — each
  section says what it establishes and why it matters before the
  code, at the register of a mathematical text's gloss.
- **Citations are polished** (full, resolvable, in the house
  credit forms), and **formalization justifications are stated**:
  why this code formalizes that mathematical object or result —
  the correspondence argued, not assumed.
- **Freeze only what is volatile**: the self-contained-modulo-Core
  discipline exists because `Cat.*` and other development
  namespaces may change — a frozen copy pins a proposed structure
  at a point in time. `Core.*` is the stable API and is imported,
  never frozen; and a generic lemma discovered during a freeze
  (path algebra, generally-applicable helpers) is NOT vendored
  into the certificate — it is landed in its matching `Core.*`
  module first and imported, per the Import and Placement
  Discipline. The coder and the review pipeline own catching
  this; a generic helper re-derived inside a Gloss is a defect.

## Promoting Test/ → Gloss/

Promote only when ALL hold:

1. The file is the primary machine evidence for a specific
   gloss.md entry — the promotion and the ledger edit happen
   together.
2. The result is NOT mechanized in a committed module. Gloss is
   for evidence whose only home is the artifact: negative results
   (walls, countermodel kills), measurements, models/instances not
   yet worth a library module, reductions cited by prose. If the
   content landed as a real module (✅ in the ledger), the Test
   file is history — keep or delete, never promote.
3. The investigation arc is closed and the verdict accepted.
   Mid-flight spikes stay in Test/.

Ritual: rename (descriptive, untimestamped); freeze per the
invariants above; expect a compile-fix step (Test files rot
silently — `codep-category` in PcomConservation was the precedent);
lint-clean (72 prose / 85 code); add to `All`; header line. Freeze
fidelity is proven mechanically, never eyeballed (Lane,
2026-07-13): extract every ```agda fence from the source spike AT
ITS PINNED COMMIT and from the certificate, and diff — the only
permitted deltas are the module rename, the `Frozen from … @
<commit>` markers, and any explicitly-marked non-frozen additions
block. When one spike feeds more than one certificate, the diff
runs per carried block and the freeze report carries a coverage
map: every source fence accounted for exactly once — carried by a
named certificate, provided by Gloss-import (the map points at the
byte-matching copies in the providing certificate), or remaining
in the spike uncertified. The T21 freeze (`ExtractAgreeIndependence` from
`Test.CodepExtractAgree-… @ dde1f57`) is the exemplar, and
tracked-Test provenance (`Frozen from Test.<Name> @ <commit>`) is
the ruled pattern for records whose first committed home is the
Test tier.

Triggers to check: writing or upgrading a 🧪 ledger entry;
committed code or docs citing a Test/ file (promote it or drop the
citation — committed artifacts must not reference scratch);
arc-close and session-log sweeps, where every Test/ file gets an
explicit fate: promote / keep-active / delete-absorbed.

## Retirement

Gloss is append-mostly. A certificate stays even after its theorem
is mechanized in a committed module — it remains the
frozen-at-proof-time witness. Retire a certificate only if its
ledger entry is itself retracted.
