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
lint-clean (72 prose / 85 code); add to `All`; header line.

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
