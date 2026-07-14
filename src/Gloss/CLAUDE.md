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
  named commit (update the `@ <commit>` markers together). If a
  claim needs revision, fix the ledger entry, not the evidence.
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
- **Readability = reduced jargon and no metadata-specific
  identifiers**: a Gloss is readable by someone with NO
  familiarity with this repository's operations, roadmap, or
  operational idiom and taxonomy (never "the naked bridge" —
  say what the term means mathematically or do not use it). It is
  a comprehensible mathematical artifact, illuminating when read
  in the future, and directly able to assist inclusion in a
  mathematical paper or thesis.
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

Existing certificates predating this standard are a scheduled
retrofit (synopsis + de-jargonizing + Core-lemma extraction),
never silent precedent.

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
block. The T21 freeze (`ExtractAgreeIndependence` from
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
