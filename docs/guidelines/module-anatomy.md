# Module anatomy

- **Opener** (ruled 2026-07-14, superseding the 2026-07-13
  prose-header ruling): a leading YAML frontmatter block, then the
  first fence, OPTIONS pragma, blank line, `module … where`. Three
  registers, cleanly separated. **(1) frontmatter** — a `---` …
  `---` block at the very top, machine-readable metadata; required
  core `author` (string), `date` (`YYYY-MM`), `contents` (string),
  and any further keys tolerated unenforced (`tags`, `status`,
  `updated`, …) — that tolerance is the extensibility. **(2) the
  `contents:` tagline** — one plain line naming the module's content
  (structured and indexable; it replaces the old prose content
  sentence). **(3) synopsis prose** — optional documentation prose
  below the frontmatter, blank-line-separated, rendered as the
  docs-page intro; omit it for small modules.
  `src/Core/Path/Base.lagda.md:1-5` is the exemplar (frontmatter,
  blank, fence — no synopsis); `src/Core/Kan.lagda.md:1-6` shows the
  post-fence body shape. The frontmatter rule is uniform across
  tracked `src/` — library modules, `Gloss.*` certificates, and
  untimestamped `Test/` regression witnesses alike; timestamped
  `Test/` scratch is exempt. Everything before the first fence is
  ignored by Agda, so the block never affects the typecheck. A
  tolerant canary (`just lint frontmatter`) validates the core
  where a block is present, and frontmatter lines carry a 100-char
  width soft cap (`bin/lint`, wider than the 72 prose limit — a
  `contents:` tagline is one unwrappable line); the tree-wide
  conversion of the header-less and prose-header files is
  docs/roadmap.md target 6.
- **Pragma tracks the stratum**: default
  `--safe --erased-cubical --no-guardedness`; pure-MLTT foundation
  leaves use `--cubical-compatible`
  (`src/Core/Data/Nat/Base.lagda.md:5`); `--cubical` only where
  Glue is required, with the deviation justified in the opening
  prose (`src/Core/Univalence.lagda.md:3-8`). Ruled 2026-07-13: no
  flag redundant with the global `kitcat.agda-lib` set appears in
  a per-module pragma (the sporadic `--no-sized-types` lines are a
  scheduled cleanup).
- **Imports**: immediately after the header, one `open import` per
  line, `Core.Type`/`Core.Base` first then rough dependency order.
  Plain opens dominate; `using`-lists where the pull is
  deliberately narrow or a clash exists
  (`src/Core/Function/Embedding.lagda.md:26-28`). Qualified alias =
  the type's own name (`import Core.Data.Nat.Properties as Nat`).
  Builtins are imported and renamed only by the module that owns
  the wrapping (`src/Core/Type.lagda.md:8-17`); fixity may be
  assigned inside the renaming
  (`src/Core/Data/Sigma/Type.lagda.md:13`).
- **Prose and headings**: `##`/`###` only, never `#`; small modules
  (< ~60 lines) use no headings. Section prose states the
  mathematics of the next block; single-sentence fence-splits are
  free. Tree ratio ≈ 1 prose : 3.8 code.
- **Aggregators** contain only pragma, header, re-exports. Three
  shapes: data-type aggregators namespace operations under the
  type's name and export the bare type flat
  (`src/Core/Data/Nat.lagda.md:10-20` — consumers write `Nat.set`,
  `Nat.add.unitr`); stratum aggregators re-export flat, `hiding` to
  resolve collisions (`src/Core/Function.lagda.md:13-24`); a facade
  re-exports a curated selection when a module is the canonical
  door to another's content (`src/Core/Interval.lagda.md:16-22`).
