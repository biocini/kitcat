# Toolchain

- check: `just check-tree` (typechecks every module under `src/`,
  listing failures; nonzero exit on any failure)
- check-file: `just check {file}` (dot-path or `src/` file path)
- sorry-token: `postulate`, `{!`
- unsafe-markers: `TERMINATING`, `NON_TERMINATING`,
  `NO_POSITIVITY_CHECK`, `--allow-unsolved-metas`, a per-module pragma
  missing `--safe`, `-W` warning suppressions
- lib-layout: literate modules `src/**/*.lagda.md`; module names mirror
  paths (`src/Cat/Logic/Base.lagda.md` → `Cat.Logic.Base`); namespaces
  per the table in `CLAUDE.md` (`just stats` for the live inventory);
  default per-module pragma
  `{-# OPTIONS --safe --erased-cubical --no-guardedness #-}`
- probe: `agda --version`
- search-dirs: `src/`
- style-guide:
  - law: match the local idiom of the module you edit; escalate style
    questions rather than improvise (`CLAUDE.md`'s Style law)
  - exemplar: `Core.*`

No `clean-build`: `just check-tree` is the whole-library check.
