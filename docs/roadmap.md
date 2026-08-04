# Roadmap: ongoing projects

High-level overview of the ongoing projects in this repository, in
the rough order in which we wish to proceed. Lane's direction
overrides the ordering at any time. Any agent, from any workflow,
reads this file for what the repository works toward. It is a
standing document, never a session artifact. Session history lives
in the session logs (`notes/`). Repo-level maintenance lives in the
root `TODO.md`. This file carries only the projects and their
gates. Update it when a project lands, when a ruling adds new work,
or when a ruling re-gates a project. Do not update it per session.

1. **The LB certification program, THE CHIEF MOTIVATION (Lane,
   2026-07-20).** Formalizing the LB/∂LB apparatus (the braided,
   polarized, linear/dependent type theory implemented at
   `~/src/ocaml/lb`) is what kitcat's development is for at this
   time. The program map (the kernel/spine correspondence audit,
   eight phases, the certificate→ledger targets) is
   `notes/2026-07-20-lb-certification-program.md`. The currency is
   certificates: every phase ships a named kitcat theorem or
   instance that upgrades a ∂LB claim-ledger row
   (`[~] → [✓-Agda]`, commit-pinned) or discharges an audit
   finding.

   **The foundation track (folded in, Lane 2026-07-28).** The
   deductive-system line in `Cat.Logic` carries the program's
   foundations: virtual graphs with readback, the deductive-system
   record (contractible cuts plus invertibility, stability a
   theorem), and the free balanced word model
   (`Cat.Logic.Gist.BalancedWord`) as the profile oracle. The
   associativity profile is settled: pre-duploid
   plus `mixed-assoc`, the four unit laws, and the twist-flanked
   family, with generic `associates` refuted at the free point.
   Open, in order: morphisms of systems, the free system and
   initiality (the coherence theorem as an NbE result), and the
   `Mag` rebuild: `hcategory` without interchange as the
   θ²-collapsed one-twist instance of that record, program of record
   `src/Bb/VgCategoryShape/README.md`. The working ledger is
   `src/Cat/Logic/TODO.md`.

   Phases in brief:
   - **0** anchor: the certificate convention, `End(I)` commutative
     by Eckmann–Hilton, the ruling batch.
   - **1** the center: Müger transparency, silent-exchange
     soundness.
   - **2** balanced + the S¹ no-UIP model: `Id(a,a) ≅ ℤ`, the
     ribbon-arc stages A/C1 with their consumers named, the
     filler-first eliminator study in parallel. Progress
     2026-07-28: the winding grade is syntactic at the free
     balanced point (endo-homs ℤ-graded, the double twist the
     `+1` generator).
   - **3** dialogue: negation as representability, `∗`-autonomous
     specialization, balanced-dialogue, dialogical = ribbon twist.
     Chir folds in as the two-sided presentation (Lane,
     2026-07-20). Re-gated (Lane, 2026-07-28): rests on the
     deductive-system representability apparatus in `Cat.Logic`,
     not on the archived category tree.
   - **4** duploids + braided Hasegawa–Thielecke (⟨open-1⟩
     machine-checked). Re-gated (Lane, 2026-07-28): enters through
     the associativity profile verdict and the reflection theorem (line 7
     of `src/Cat/Logic/TODO.md`). The balanced duploid is the
     target notion.
   - **5** the free instance and kernel soundness: `Gₙ` in Agda +
     the three-way oracle pin, the LB MA-core free instance, claim
     15, `Gn.equal` certified as deciding the free hom-equality.
     Progress 2026-07-28: decidable hom-equality at the free
     balanced point is the pattern's point case.
   - **6** modalities/additives: consumer-gated spine extensions,
     `⊕`/`&`, the braided cofree comonoid/Seely.
   - **7** the fenced frontier: gluing-style normalization
     completeness, the universe ω-limit, the infinitary server
     (non-gating).

   Phases 0→4 are structure-ordered. 5(a) may open in parallel
   after 0. The ribbon-arc plan (`notes/2026-07-20-ribbon-arc.md`)
   and its open rulings carry over inside phases 2–5.

2. **The Core reformation (composite-rx), GATED (Lane,
   2026-07-28).** Reformulate the Core systems under composites
   and reflexive graphs, and port `Core.Rx` to `Core.Rx` in
   the endeavor: an engine for the whole proof-theoretic
   apparatus, skew to the LB line but not orthogonal to it. The
   staged plan is `docs/composite-rx-refactor/`, with
   `Bb.CatsWithExplicitInterchange` the porting reference
   throughout. The gate: the design of `hcategory` without
   interchange, clarified through the deductive-system apparatus (the
   foundation track above), lands first. Precondition: the Rx
   promotion plan carries audit findings from 2026-07-24; correct
   its notes before the program opens (tracked in `TODO.md`).

3. **Bimodule record spike (B1–B3), RE-GATED (Lane, 2026-07-28).**
   The record restates over the deductive-system spine when the
   reformation reaches it. The origin design block is the
   2026-07-13 prove-shakedown session log, and the Kelly entry
   (audited) grounds its unit-coherence framing. Its predecessor
   landed 2026-07-13: extract-agree irreducibility is T21, cited
   at `Bb.CatsWithExplicitInterchange.Gist.CodepExtractAgree`.

4. **Workflow suite, next phases.** The ingestion-pipeline split
   (Lane, 2026-07-13): a fetch skill that parses the entries'
   custody frontmatter (url + hash) for acquisition and re-fetch,
   leaving the `ingest` agent focused on quality control and
   analysis (maps, digests). Memory externalization stays the
   standing rule: every design a run opens on lives in a tracked
   home. Shelf standing: 16 entries, custody-clean
   (`just resources-verify`). The open statement audits are in the
   root `TODO.md`.
