# Records

- **`no-eta-equality`** on every record except principled
  single-field wrappers where definitional eta is the point
  (`Lift`, `Irr`, `Fin`, `Instance`). This is the CLAUDE.md
  constraint as practiced (43/47).
- **Field order**: superclass instance field, then data, then
  erased (`@0`) laws.
- **Exit row**: `open X public` (traits: `open X ⦃ … ⦄ public`
  hiding superclass fields), then `{-# INLINE X.constructor #-}`.
  Records meant only for qualified access skip the `open`
  (`is-qinv`).
- **Derived members live inside the record body** after `field`.
  Consumer-facing projection interfaces are parameterized modules
  beside the type (`module Equiv (e : A ≃ B)`).
- **Implicit universe parameters are earned by inference.** A
  `Level` parameter is implicit exactly when a later explicit
  argument's type determines it by unification (`ob : Type o`
  determines `o`). A universe confined to field types, or to the
  record's own sort, is not inferable at type formation. Declare it explicit. Core practices this:
  `hMap (u : Level) {v} (X : Type v)` makes the field-only `u`
  explicit and infers `v` from `X`
  (`src/Core/Function/Partial/Fiber.lagda.md:39`). This is the
  level case of the general rule. See guidelines/elaboration.md
  for the three recovery tiers, the endpoint question, and the
  probes that decide a case.
