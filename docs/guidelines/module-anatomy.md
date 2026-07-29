# Module anatomy

- **Opener** (ruled 2026-07-14, superseding the 2026-07-13
  prose-header ruling): a leading YAML frontmatter block, then the
  first fence, OPTIONS pragma, blank line, `module … where`. Three
  registers, cleanly separated. **(1) frontmatter**: a `---` … `---`
  block at the very top, machine-readable metadata. The required
  core is `author` (string), `date` (`YYYY-MM`), and `contents`
  (string). Further keys pass unenforced (`tags`, `status`,
  `updated`, …). That tolerance is the extensibility. **(2) the
  `contents:` tagline**: one plain line that names the module's
  content (structured and indexable, it replaces the old prose
  content sentence). **(3) synopsis prose**: optional documentation
  prose below the frontmatter, blank-line-separated, rendered as
  the docs-page intro. Omit it for small modules.
  `src/Core/Path/Base.lagda.md:1-5` is the exemplar (frontmatter,
  blank, fence, no synopsis). `src/Core/Kan.lagda.md:1-6` shows the
  post-fence body shape. The frontmatter rule is uniform across
  tracked `src/`: library modules, `Gloss.*` certificates, and
  untimestamped `Test/` regression witnesses alike. Timestamped
  `Test/` scratch is exempt. Agda ignores everything before the
  first fence, so the block never affects the typecheck. A tolerant
  canary (`just lint frontmatter`) validates the core where a block
  is present. Frontmatter lines carry the same 100-char width cap as
  prose and code (`bin/lint`). The tree-wide
  conversion of the header-less and prose-header files is tracked
  in the root `TODO.md`.
- **Pragma tracks the stratum**: default
  `--safe --erased-cubical --no-guardedness`. Pure-MLTT foundation
  leaves use `--cubical-compatible`
  (`src/Core/Data/Nat/Base.lagda.md:5`). `--cubical` only where the
  proof needs Glue, with the deviation justified in the opening
  prose (`src/Core/Univalence.lagda.md:3-8`). Ruled 2026-07-13: no
  flag redundant with the global `kitcat.agda-lib` set appears in
  a per-module pragma (the sporadic `--no-sized-types` lines are a
  scheduled cleanup).
- **Imports**: immediately after the header, one `open import` per
  line, `Core.Type`/`Core.Base` first, then rough dependency order.
  Plain opens dominate. `using`-lists appear where the pull is
  deliberately narrow or a clash exists
  (`src/Core/Function/Embedding.lagda.md:26-28`). The qualified
  alias is the type's own name
  (`import Core.Data.Nat.Properties as Nat`). Only the module that
  owns the wrapping imports and renames builtins
  (`src/Core/Type.lagda.md:8-17`). Fixity may sit inside the
  renaming (`src/Core/Data/Sigma/Type.lagda.md:13`).
- **Prose and headings**: `##`/`###` only, never `#`. Small modules
  (< ~60 lines) use no headings. Section prose states the
  mathematics of the next block. Single-sentence fence-splits are
  free. Tree ratio ≈ 1 prose : 3.8 code.
- **Aggregators** contain only pragma, header, re-exports. Three
  shapes. Data-type aggregators namespace operations under the
  type's name and export the bare type flat
  (`src/Core/Data/Nat.lagda.md:10-20`, consumers write `Nat.set`,
  `Nat.add.unitr`). Stratum aggregators re-export flat, with
  `hiding` to resolve collisions
  (`src/Core/Function.lagda.md:13-24`). A facade re-exports a
  curated selection when a module is the canonical door to
  another's content (`src/Core/Interval.lagda.md:16-22`).
