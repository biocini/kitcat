# Roadmap — ongoing projects

High-level overview of the ongoing projects this repository is
engaged in, in the rough order in which we wish to proceed —
subject to Lane's direction, which overrides the ordering at any
time. Any agent, from any workflow, reads this file for what the
repository is working toward; it is a standing document, never a
session artifact. Session history, activity provenance, and
next-step previews live in the session logs
(`notes/session-logs/`, one entry per session, written by `/log`
at close); this file carries only the projects and their gates.
Update it when a project lands (its gate satisfied), is added
(new work ruled into existence), or is re-gated (its gate or
ordering changed by a ruling) — not per session: the `/log` close
checks these triggers each session and edits only when one fires.

1. **Bimodule record spike (B1–B3)** — the record, regular
   filling, emb-parity (B4 struck — refuted). Opens on the
   pre-registered design block in the 2026-07-13 prove-shakedown
   session log; the Kelly entry (audited) grounds its
   unit-coherence framing. (Its predecessor, the faithful-stratum
   substrate spike A1–A3, LANDED 2026-07-13: all three checks
   green, extract-agree's irreducibility enshrined as T21 /
   `Gloss.ExtractAgreeIndependence`; the A1/A2/A3 ledger-entry
   promotions EXECUTED 2026-07-13 as ratified — T22
   `Gloss.TautologicalFilling`, T23 `Gloss.InterchangeCircularity`,
   T24 📐 citing the tracked spike @ dde1f57.)
2. **THE REFACTOR** — the re-founding of the `Cat.*` tree over
   `Cat.Codep`'s `hcategory`. **OPENED 2026-07-14 (Lane): the core
   record replacement is active, sequenced AHEAD of Chir.** The
   substrate spikes and the coherence program earned it — T1–T24
   built the `hcategory` record, every unit/assoc law, the full
   coherence tower, and strict self-duality, all Chir-free — so
   `hcategory` becomes the library's canonical category record. Plan
   and required-items inventory (phases P0–P8): the analyzer memo
   `notes/research/2026-07-14-refactor-required-items.md`.
   - **Core phase (Chir-independent, in progress).** The
     pre-refactor records rebase onto `hcategory` or retire:
     `Cat.Type`/`Cat.Base` TRANSPLANT (their 1-categorical API —
     universal properties, functors, nat-trans, adjunctions — is
     stated over the derived surface `hcategory` already provides);
     `Cat.Coherence` RETIRES (superseded by the richer coherence
     tower); `Cat.Virtual` REBASES over `hcategory` (classified
     composition; Lane ruled 2026-07-14 — the two-strikes-risk item).
     `Cat.Dep` was DELETED 2026-07-14 (abandoned experiment, Lane).
     P1 — the compat/fiber spike pinning the `emb` curry/uncurry
     bridge — gates the `Cat.Base` transplant.
   - **Downstream, Chir-independent (after the core):** the
     polarity-agnostic tree — `Iso`, `Yoneda`, `Covariant`, the base
     `Cat.Monoidal` record, `Groupoid`, and the currently-WIP
     `Product`, `Slice`, `Displayed`, `Rezk`, `Data.Thin.Category`
     (re-expressing them over `hcategory` is also their un-WIP path).
     **`Cat.Bimodule` is added new here** — the
     regular-representation bimodule hom (spiked green 2026-07-13 as
     `Test.CodepBimodule-20260713-234309`, all DERIVED over β; Lane
     ruled 2026-07-14 it graduates to this `Cat.*` home, NOT gloss).
   - **Chir-GATED slice (the only part still behind targets 3–4):**
     the braid/ribbon monoidal downstream — `Cat.Monoidal.Braid`,
     `.Hexagon`, `.Twist` — plus the T16 monoidal-side mechanization
     if ruled a deliverable. This is what the earlier "opened only on
     Lane's word" gate actually governs; the core does not wait on it.
3. **Chir.*** — single-carrier polarity-as-representability;
   parked pending Lane's five rulings; Spikes A/B/C specced with
   kill criteria (memory: chirality record).
4. **Framed syntax instance** — the syntax instance targeting the
   plain record; the braid/twist layer follows.
5. **Workflow suite, next phases** — the memory-externalization
   sweep into canonical repo homes (gloss.md, session logs, roadmap;
   memory left as pointers, per R10 — never gitignored working
   memory), now explicitly including **pre-registered design memos**
   (Lane, 2026-07-13: every design a run opens on must live in a
   tracked home — memo B's externalization into the 2026-07-13
   session log is the pattern); the untracked-file cleanup (every
   stray cleaned up,
   ignored, or given a canonical home — includes the 25 legacy
   `src/Test/` files swept into tracking 2026-07-13); and the
   **ingestion-pipeline split** (Lane, 2026-07-13): a fetch
   prompt/skill that systematically parses the entries' custody
   frontmatter (url + hash) for acquisition and re-fetch, and the
   externalization of the pipeline's logistical parts out of the
   `ingest` agent, leaving it focused on quality control and
   analysis (maps, digests). Shelf standing: eight entries, all on
   the custody frontmatter, all statement-audited; seven vetted by
   Lane 2026-07-13, kelly's discretion open; T16 and T15 both
   lifted under the audit-keyed rule — no ⚠️
   source-identifications remain.
6. **Housekeeping** — the styleguide conformance
   sweeps (ruled GO, Lane 2026-07-13; docs/styleguide.md
   "Rulings"): the **frontmatter
   sweep** — convert every tracked `.lagda.md` to the YAML
   frontmatter convention (ruled 2026-07-14 — author/date/contents
   core + optional synopsis; docs/styleguide.md Opener). The tooling
   (build.py rendering + the tolerant `bin/lint` frontmatter canary)
   and a limited two-file pilot (`Core.Path.Base`, `Core.Type`)
   landed 2026-07-14; the BULK is this target's scheduled work — the
   123 header-less Core files plus reformatting the old-prose-header
   files, then flipping the canary to require-presence; removal of
   globally-redundant per-module flags; the ternary-first
   conformance sweep over Core's ~112 legacy `∙`-chains; the
   WIP-module probe sections (`Core.Path.Composition` and
   siblings) migrated to `Test/`. Plus the carried items:
   `Cat/Type` whitespace (Lane's call); the Coherent killcheck
   casing nit; conservativity battery re-migration.
