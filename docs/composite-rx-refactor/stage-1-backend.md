# Stage 1: backend, `Core.Rx`

The promotion of `Cat.Graph.Refl.*` into `Core`, split at the Kan
cut. Precondition: Stage 0 complete (0.4 especially).

## 1.1 Rename

`Cat.Graph.Refl.*` → `Core.Rx.*`, module by module with `just mv`,
which sweeps `src/`, covering the suite's internal imports and the
two certificate importers (`Test.KanIdentities`, `Test.RxBundle`).

By hand, outside the sweep ([evidence](evidence.md) inventory):

- `bin/profile` line 12: the usage-string example names
  `Cat.Graph.Refl.Lens`.
- `docs/guidelines/elaboration.md`,
  `docs/guidelines/profiling.md`: if 0.4 abstracted these sites, the
  entries are already gone. Verify rather than assume.
- The 2026-07-24 notes reference the old names. This document set
  supersedes them, and they receive no maintenance.

Module-name mapping is one-to-one (`Type`, `Base`, `Properties`,
`Lens`, `Poly`, `Fibration`, `Classify`, `Simplex`, `Univalent`),
subject to D1 (instances) and D7 (lens placement) below.

## 1.2 Split at the cut

Into `Core.Rx.Transport` (above `Core.Transport.*`):

| name | forcing dependency |
| --- | --- |
| `rx.to-edge` | `transport` |
| `coproduct` | `transport`, `transport-filler` |
| `rx.tensor` | `coproduct` |
| `rx.univalence.concat`, `.inv` | `_∙_` |
| `image`, `is-univalent-family` | `_≃_`, `aut` |

Everything Tier-1 stays below `Core.Kan`, including
`rx.univalence.to-id` and `fan-contr`, which need only `ap fst` and
`prop-inhabited→is-contr` (in `Core.Base` after 0.1). The
`rx.univalence` interface therefore splits across the cut: a
`univalence` module below carrying `fan-contr`/`to-id`, extended
above by `concat`/`inv`. Shape the extension so use sites read
naturally (`po`-style instantiation). The split is an accepted
wrinkle of the stratification, not a defect to engineer away.

`Core.Rx.Properties` (above): the `po` calculus, the closure
calculus (`total-path-object`, `prod`/`coprod`/`cotensor`/`tensor`/
`compr-path-object`, `disc`/`codisc`), `fibration-is-prop` (from
0.2), the `*-structure-is-prop` proofs. All forced
([architecture](architecture.md)).

`Core.Rx.Lens`/`Poly`/`Fibration`/`Univalent`: per D7 for the
unforced lens-structure set. `Poly` above `Core.Transport`
regardless. `Univalent` on `--cubical` regardless.

## 1.3 Re-point the conventions note

`notes/2026-07-24-refl-inference-policy.md` names `rx.to-edge` and
other members by their current homes. Amend its examples for the
migrated names. The guidelines are *abstracted* under 0.4, never
renamed through.

## Open within this stage

**D1**: do the instances promote? `Classify` (the `U`-small
classifiers, `Magma`, unordered pairs) and `Simplex` (`AugSpx`,
lists) are instances, not machinery, and pull `Core.Data.Trunc`,
`Core.Data.Bool`, `Core.Data.Fin.Monotone.*` into whatever namespace
holds them. Options: promote with the machinery, stay in `Cat`, move
to `Lib`. Neither has any importer today.

## Acceptance

- `Core.Kan` imports `Core.Rx.Base` with no cycle.
- Whole-library check unchanged (`Core` 137/139, `Test` green, `Cat`
  green under invariant D8).
- `just profile Core.Kan` within the measured noise band
  (1,025–1,072 ms, the import measured neutral,
  [evidence](evidence.md)).
- **`Core.Rx.Type` and `Core.Rx.Base` import only `Core.Type`,
  `Core.Base`, `Core.Data.Sigma`.** The placement claim transfers
  from `Test.RxTier1`'s transcription to the modules themselves,
  closing the transcription-drift channel. The certificate then
  shrinks to the identities its imports do not carry
  (`fan-of-discrete`, `disc-fan-contr`) or retires.
