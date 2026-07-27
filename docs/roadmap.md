# Roadmap: ongoing projects

High-level overview of the ongoing projects in this repository, in
the rough order in which we wish to proceed. Lane's direction
overrides the ordering at any time. Any agent, from any workflow,
reads this file for what the repository is working toward. It is a
standing document, never a session artifact. Session history,
activity provenance, and next-step previews live in the session
logs (`notes/`, one entry per session, written by `/log` at close).
This file carries only the projects and their gates. Update it when
a project lands (its gate satisfied), when a ruling adds new work,
or when a ruling re-gates a project (its gate or ordering changed).
Do not update it per session. The `/log` close checks these
triggers each session and edits only when one fires.

1. **The LB certification program, THE CHIEF MOTIVATION (Lane,
   2026-07-20).** Formalizing the LB/∂LB apparatus (the braided,
   polarized, linear/dependent type theory implemented at
   `~/src/ocaml/lb`) is what kitcat's development is for at this
   time. The program map (the kernel/spine correspondence audit,
   eight phases, and the certificate→ledger targets) is
   `notes/2026-07-20-lb-certification-program.md`. The currency is
   certificates: every phase ships a named kitcat theorem or
   instance that upgrades a ∂LB claim-ledger row
   (`[~] → [✓-Agda]`, commit-pinned) or discharges an audit
   finding. Phases in brief:
   - **0** anchor: the certificate convention, `End(I)` commutative
     by Eckmann–Hilton, the ruling batch.
   - **1** the center: Müger transparency, silent-exchange
     soundness.
   - **2** balanced + the S¹ no-UIP model: `Id(a,a) ≅ ℤ`, the
     ribbon-arc stages A/C1 with their consumers named, the
     filler-first eliminator study in parallel.
   - **3** dialogue: negation as representability, `∗`-autonomous
     specialization, balanced-dialogue, dialogical = ribbon twist.
     **Chir re-gated here** (Lane, 2026-07-20): it folds in as the
     two-sided presentation, the dialogue-chiralities equivalence
     as a Properties comparison. Its former standalone slot
     retires, the attic design re-derived in place.
   - **4** duploids + braided Hasegawa–Thielecke (⟨open-1⟩
     machine-checked).
   - **5** the free instance and kernel soundness. Absorbs the
     former "framed syntax instance" project: `Gₙ` in Agda + the
     three-way oracle pin, the LB MA-core free instance, claim 15,
     `Gn.equal` certified as deciding the free hom-equality.
   - **6** modalities/additives: consumer-gated spine extensions,
     `⊕`/`&`, the braided cofree comonoid/Seely.
   - **7** the fenced frontier: gluing-style normalization
     completeness, the universe ω-limit, the infinitary server
     (non-gating).

   Phases 0→4 are structure-ordered. 5(a) may open in parallel
   after 0. The ribbon-arc plan (`notes/2026-07-20-ribbon-arc.md`)
   and its six open rulings carry over inside phases 2–5.

2. **THE REFACTOR**: the re-founding of the `Cat.*` tree over
   `Cat.Codep`'s `hcategory`. **OPENED 2026-07-14 (Lane): the core
   record replacement is active, sequenced AHEAD of Chir.** The
   substrate spikes and the coherence program earned it. T1–T24
   built the `hcategory` record, every unit/assoc law, the full
   coherence tower, and strict self-duality, all Chir-free.
   `hcategory` therefore becomes the library's canonical category
   record, **renamed `category` at its new `Cat.Type` home (Lane,
   2026-07-14)**, moved up from `Cat.Codep.Base`. P1 compat spike
   DONE 2026-07-14 (all three bridges DERIVED, the `emb`
   curry/uncurry round-trip is definitional). Branch:
   `refactor-cat-core`. Plan (phases P0–P8) across three analyzer
   memos: `notes/research/2026-07-14-refactor-required-items.md`,
   `…-refactor-stage1-2-plan.md`, `…-cat-tree-triage.md`.
   - **THE `Cat.Codep` NAMESPACE RETIRES, a core deliverable, not
     optional** (Lane, standing intention across multiple sessions,
     encoded here 2026-07-14 after a process failure that had the
     plan RETAIN it). The whole namespace goes: deprecated, pruned
     out. Every member relocates to `Cat.*` proper
     (`Cat.Codep.Coherence`, `.Coherent`, `.Op`, `.Triangle`,
     `.Instances` move up), and the relocation deletes the
     `Cat.Codep` aggregator. NOTHING in the new tree threads
     through `Cat.Codep` (the one current offender is `Cat.Base`'s
     `import Cat.Codep.Coherence` for `assoc-tower`). This gates
     the rest of the downstream: do not re-found or thread new work
     through `Cat.Codep`. `Cat.Codep.Base → Cat.Type` (Stage 1) was
     the first step. The remaining relocations complete it.
   - **Core phase (Chir-independent, in progress).** The
     pre-refactor records rebase onto `hcategory` or retire.
     `Cat.Type`/`Cat.Base` TRANSPLANT: their 1-categorical API
     (universal properties, functors, nat-trans, adjunctions) lands
     on the derived surface `hcategory` already provides.
     `Cat.Coherence` RETIRES (superseded by the richer coherence
     tower). `Cat.Virtual` REBASES over `hcategory` (classified
     composition, Lane ruled 2026-07-14, the two-strikes-risk
     item). `Cat.Dep`: DELETED 2026-07-14 (abandoned experiment,
     Lane). P1, the compat/fiber spike pinning the `emb`
     curry/uncurry bridge, gates the `Cat.Base` transplant.
   - **Downstream, Chir-independent (after the core):** the
     polarity-agnostic tree: `Iso`, `Yoneda`, `Covariant`, the base
     `Cat.Monoidal` record, `Groupoid`, and the currently-WIP
     `Product`, `Slice`, `Displayed`, `Data.Thin.Category`
     (re-expressing them over the new record is also their un-WIP
     path). **`Cat.Rezk` comes out** for a from-scratch re-approach
     with fresh research (Lane, 2026-07-14). Its `decode-gen` holes
     are a genuine HIT path-characterization wall. Re-plan them
     given the new apparatus. Do not fold them into the mechanical
     rebuild. **`Cat.Bimodule` arrives new here**: the
     regular-representation bimodule hom (spiked green 2026-07-13
     as `Test.CodepBimodule-20260713-234309`, all DERIVED over β,
     and Lane ruled 2026-07-14 it graduates to this `Cat.*` home,
     NOT gloss).
   - **Braid/ribbon monoidal subtree: REFACTOR-gated, not Chir**
     (Lane, 2026-07-14, corrects the earlier attribution):
     `Cat.Monoidal.Braid`, `.Hexagon`, `.Twist` gate on THIS
     `Cat.*` replacement, not on Chir. They receive the same
     tensor-level alignment as the rest of the Monoidal subtree
     (pre/post, tensor-`·`, `Virtual`→`category`) as part of
     finishing the refactor, and do NOT wait for targets 3–4.
     **LANDED 2026-07-20** on the new spine (`Braid`, `Hexagon`,
     `Indiscrete`, `Twist`, `Iso`, the hexagon displacement, and
     the swap-half presentation equivalence in
     `Cat.Monoidal.Properties`). The ribbon side continues inside
     project 1 (the LB certification program, phases 2–5).
   - **Chir-GATED remainder (still behind targets 3–4):** the T16
     monoidal-side mechanization, if ruled a deliverable.

3. **Bimodule record spike (B1–B3)**: the record, regular filling,
   emb-parity (B4 struck: refuted). Opens on the pre-registered
   design block in the 2026-07-13 prove-shakedown session log. The
   Kelly entry (audited) grounds its unit-coherence framing. It
   yields priority to the certification program's phases 0–1
   (Lane, 2026-07-20). (Its predecessor, the faithful-stratum
   substrate spike A1–A3, LANDED 2026-07-13: all three checks
   green, extract-agree's irreducibility enshrined as T21 /
   `Gloss.ExtractAgreeIndependence`. The A1/A2/A3 ledger-entry
   promotions EXECUTED 2026-07-13 as ratified: T22
   `Gloss.TautologicalFilling`, T23 `Gloss.InterchangeCircularity`,
   T24 📐 citing the tracked spike @ dde1f57.)

4. **Workflow suite, next phases**: three items.
   - The memory-externalization sweep into canonical repo homes
     (gloss.md, session logs, roadmap, with memory left as
     pointers, per R10, never gitignored working memory). This now
     explicitly includes **pre-registered design memos** (Lane,
     2026-07-13: every design a run opens on must live in a
     tracked home; memo B's externalization into the 2026-07-13
     session log is the pattern).
   - The untracked-file cleanup: every stray cleaned up, ignored,
     or given a canonical home. Includes the 25 legacy `src/Test/`
     files swept into tracking 2026-07-13.
   - The **ingestion-pipeline split** (Lane, 2026-07-13): a fetch
     prompt/skill that systematically parses the entries' custody
     frontmatter (url + hash) for acquisition and re-fetch, and
     moving the pipeline's logistical parts out of the `ingest`
     agent, leaving it focused on quality control and analysis
     (maps, digests).

   Shelf standing: eight entries, all on the custody frontmatter,
   all statement-audited. Seven vetted by Lane 2026-07-13, kelly's
   discretion open. T16 and T15 both lifted under the audit-keyed
   rule: no ⚠️ source-identifications remain.

5. **Housekeeping**: the style conformance sweeps (ruled GO, Lane
   2026-07-13, docs/guidelines/rulings.md).
   - The **frontmatter sweep**: convert every tracked `.lagda.md`
     to the YAML frontmatter convention (ruled 2026-07-14,
     author/date/contents core + optional synopsis,
     docs/guidelines/module-anatomy.md). The tooling (build.py
     rendering + the tolerant `bin/lint` frontmatter canary) and a
     limited two-file pilot (`Core.Path.Base`, `Core.Type`) landed
     2026-07-14. The BULK is this target's scheduled work: the 123
     header-less Core files plus reformatting the old-prose-header
     files, then flipping the canary to require-presence.
   - Remove globally-redundant per-module flags.
   - The ternary-first conformance sweep over Core's ~112 legacy
     `∙`-chains.
   - The WIP-module probe sections (`Core.Path.Composition` and
     siblings) migrate to `Test/`.
   - Plus the carried items: `Cat/Type` whitespace (Lane's call),
     the Coherent killcheck casing nit, conservativity battery
     re-migration.
