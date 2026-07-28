# API surface

- **What earns a public name**: the type, its operations, reusable
  lemmas, conversions, interface modules. Proof scaffolding,
  single-use fillers, and local abbreviations are `private`.
  Spelled aliases for operator types are public and cheap
  (`Equiv = _≃_`, `Emb = _↪_`): name-aliases, not re-typed
  primitives.
- **`module _` for shared telescopes** whenever ≥2 definitions
  share one.
- **Instances live in `Impl` modules**, one concern per file, named
  `Class-Type`. The aggregator re-exports them under the type's
  `impl` namespace. Inline `instance` blocks appear only where the
  instance is inseparable from the type.
- **Width**: 100 throughout, prose and code alike (code raised
  from 85, ruled by Lane 2026-07-20; prose raised from 72, ruled
  by Lane 2026-07-28), enforced on new and changed lines
  (`just lint changed`). The baseline falls deliberately. It is not
  license for new over-width lines.
- **Unicode is purposeful**: notation freely (`∂`, `⌞_⌟`,
  `Σ x ∶ A , B`, where `∶` is U+2236), subscripts for corner
  variables, with spelled aliases for discoverability.
- `ind` is the canonical name for hand-rolled eliminators, inside
  the type's module scope.
