# TODO — Bb.VirtualGraphs

Open work general enough to survive whatever shape the live
deductive-system definition takes.

- Literature pass on skew-monoidal and adjacent one-sided-unital
  settings, before any novelty claim for one-sided unitality here.
- Vendor Melliès, *Asynchronous Games 3*. It is the only known
  place the future/buffer reading of the two twists could be
  source-checked at all. An untracked copy already sits at the
  repository root.
- Vendor Cartwright and Felleisen, "Extensible Denotational
  Language Specifications" (TACS 1994) — the paper
  `resources/kiselyov-having-effect/` reconstructs.
- Vendor CatColab RFC 0004, "Internal languages for models"
  (Patterson, 2026-04-10).
- Vendor the remaining `Test.*` spike results — hypothesis groups
  E (neutral) and F (natural), the material this tree's own
  `README.md` already flags as waiting for a later pass. Thirteen
  files: `src/Test/SpikeCandidateGenerator`,
  `SpikeEdgeCoherence`, `SpikeFramedShape`,
  `SpikeGluingCharacteristic`, `SpikeGradeSelector`,
  `SpikeMediationWild`, `SpikeNaturalModuli`, `SpikeNaturalTier`,
  `SpikeNaturalTruncation`, `SpikeNeutralReadback`,
  `SpikeNeutralTier`, `SpikeSelfMediation`, `SpikeTwistMediation`
  (all `.lagda.md`). Import each file's checker-verified theorems
  about its model — the concrete equalities, refutations, and
  witness types it actually proves — restated over this tree's
  flat carrier, the same way the rest of the consolidation was
  done. Do not import a file's own verdict prose as written.
  `notes/2026-08-03-vgds-torsor-correction.md` found that several
  of these files scored their circle-model conclusions against
  contractibility of a moduli space, when the type in question is
  a torsor (a free, transitive orbit under a generated group) —
  a materially weaker and different condition than
  contractibility, not the same fact under looser language. Each
  file's actual verdict needs re-deriving from its raw proved
  facts against the torsor criterion before anything it concludes
  is restated here; the checker-verified Agda itself is not in
  question, only which prose conclusion it supports.
