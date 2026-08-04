# Stage 0: preparation

Four items, individually checkable, all mechanical. 0.4 lands before
Stage 1 or the sweep and the rename collide in the same files.

## 0.1 Centralize the pure contractibility lemmas

Move into `Core.Base`:

| lemma | current home |
| --- | --- |
| `Singl-contr` | `Core.Transport.Base` |
| `Singl-contr-cofan` | `Core.Groupoid` |
| `prop-inhabited→is-contr` | `Core.Transport.Properties` |

All three are pure (no `transp`, no `hcom`), VERIFIED in
`Test.RxTier1`, which defines them with imports restricted to
`Core.Type`/`Core.Base`/`Core.Data.Sigma`. Today
`Core.Rx.Properties` imports the first two from those two
unrelated modules. After the move the backend's only contractibility
imports are `Core.Base`'s own.

Consumers to re-point: the old homes re-export nothing (a move, not
a forwarding alias), so importers of the moved names switch to
`Core.Base`. `Core.Groupoid` loses its one live consumer with the
move (decision D10 governs the module's fate, at Stage 2.4).

*Acceptance:* whole-`Core` count unchanged (137/139).
`Core.Kan.Total-sys-contr` is `Singl-contr (sys-composite φ s)`:
VERIFIED as `refl`, `Test.KanIdentities` probe 4.

## 0.2 Lift `fibration-is-prop`

`fibration-is-prop : (D : rx.disp G w z) → is-prop (rx.is-cov-fibration G D)`
sits `private` in `Core.Rx.Univalent`, on `--cubical`. It
uses only `Π-is-prop` and `is-contr-is-prop`, nothing from `ua`. It
is the `is-composable` propositionality proof (Stage 3.3/3.5). Left
where it is, `deductive-system` would land on full cubical.

Destination: `Core.Rx.Properties` now, becoming
`Core.Rx.Properties` at Stage 1 (its inputs live at
`Core.HLevel.Base`/`Core.Transport.Properties`, so it sits above
`Core.Kan`, a forced placement, [architecture](architecture.md)).

*Acceptance:* `Core.Rx.Univalent` still checks on `--cubical`
with the lemma imported. No other module changes.

## 0.3 Fix the mis-attributed import

`Core.Path.Coherence` line 20 imports `is-contr→is-set` and
`total-contr-unique` from `Core.Transport.Base`. They are
`Core.Kan`'s. Under `-Werror` the `ModuleDoesntExport` warning is
fatal on its own.

*Acceptance:* the module's failure mode reduces to its nine holes.
The `Core` count stays 137/139. (The holes are Stage-5 material.)

## 0.4 The guidelines chore

`docs/guidelines/CLAUDE.md` (landed) bans live-tree references in
guidelines. Consequent sweep: 24 sites, 17 `file:line` citations
(`module-anatomy` 10, `definitions-and-proofs` 3, `naming` 2,
`records` 1, `profiling` 1) and 7 dot-paths (`module-anatomy` 3,
`definitions-and-proofs`, `elaboration`, `profiling`,
`prose-and-comments` 1 each), plus `docs/guidelines/README.md`,
which advertises the banned practice. Abstract per the policy
(self-contained fragments with invented names). Do not rename
through them.

Enumerate the sites with:

```
rg -n 'src/|Core\.|Cat\.|HData\.|Lib\.|Data\.' docs/guidelines/
```

*Acceptance:* the `rg` sweep over `docs/guidelines/` finds no live
module names, file paths, or `file:line` citations outside
`CLAUDE.md`'s own statement of the rule. `just lint` unchanged.
