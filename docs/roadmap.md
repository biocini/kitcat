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

1. **Faithful-stratum substrate spike (A1–A3)** — the main
   mathematical line: substrate records, Π-integral composite,
   res-invariance. Kill criteria are pre-registered in the spike
   design (memory: memo A in the ontology log).
2. **Bimodule record spike (B1–B3)** — the record, regular
   filling, emb-parity (B4 struck — refuted).
3. **THE REFACTOR** — the conditional promotion of `Cat.Codep`:
   if the hcategory line keeps earning it (the substrate spikes
   and the coherence program keep landing), `hcategory` becomes
   the library's canonical category record and the `Cat.*` tree
   is re-founded over it. End state: the pre-refactor records
   (`Cat.Type`, `Cat.Base`, `Cat.Virtual`, `Cat.Coherence`) are
   rebased onto `hcategory` or retired; the downstream tree
   (`Cat.Monoidal` and its submodules, `Groupoid`, `Iso`,
   `Product`, `Slice`, `Yoneda`, `Displayed`, `Rezk`,
   `Covariant`, `Dep`) is re-expressed over the new foundation,
   with per-module dispositions (rebase / keep / retire) decided
   when the refactor opens, not before. Downstream of targets
   1–2. Gates behind it: the Chir dialogue tier, the braid/ribbon
   layer, the monoidal side of the chirality convergence theorem,
   and the post-refactor standardization arc — opened only on
   Lane's word.
4. **Chir.*** — single-carrier polarity-as-representability;
   parked pending Lane's five rulings; Spikes A/B/C specced with
   kill criteria (memory: chirality record).
5. **Framed syntax instance** — the syntax instance targeting the
   plain record; the braid/twist layer follows.
6. **Workflow suite, next phases** — the memory-externalization
   sweep into canonical repo homes (gloss.md, session logs, roadmap;
   memory left as pointers, per R10 — never gitignored working
   memory), now explicitly including **pre-registered design memos**
   (Lane, 2026-07-13: every design a run opens on must live in a
   tracked home — memo B's externalization into the 2026-07-13
   session log is the pattern); the T15 Kelly `resources/` entry
   still to vendor (paywalled, needs Lane's access) to upgrade T15
   off ⚠️; the untracked-file cleanup (every stray cleaned up,
   ignored, or given a canonical home — includes the 25 legacy
   `src/Test/` files swept into tracking 2026-07-13); and the
   **ingestion-pipeline split** (Lane, 2026-07-13): a fetch
   prompt/skill that systematically parses the entries' custody
   frontmatter (url + hash) for acquisition and re-fetch, and the
   externalization of the pipeline's logistical parts out of the
   `ingest` agent, leaving it focused on quality control and
   analysis (maps, digests). Shelf standing: seven entries vetted
   by Lane 2026-07-13; kelly-maclane-conditions audited, field
   pending its re-extraction's confirming pass.
7. **Housekeeping** — the styleguide conformance sweeps (ruled GO,
   Lane 2026-07-13; docs/styleguide.md "Rulings"): author/date
   headers onto the 123 header-less Core files; removal of
   globally-redundant per-module flags; the ternary-first
   conformance sweep over Core's ~112 legacy `∙`-chains; the
   WIP-module probe sections (`Core.Path.Composition` and
   siblings) migrated to `Test/`. Plus the carried items:
   `Cat/Type` whitespace (Lane's call); the Coherent killcheck
   casing nit; conservativity battery re-migration.
