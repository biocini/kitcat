# Evidence base

Measured 2026-07-24, against the tree at `2f3ac3c` plus the
untracked planning artifacts. Reproduction commands at the end.

## Environment

- `just check-tree src/Core`: **137/139**. Failures:
  `Core.Coherence.Paths` (4 unsolved metas), `Core.Path.Coherence`
  (9 holes, plus a fatal mis-attributed import at line 20:
  `is-contr→is-set` and `total-contr-unique` are `Core.Kan`'s, not
  `Core.Transport.Base`'s). Both failures are committed state.
- `just check-tree src/Test`: **17/17** (`.lagda.md` only; the six
  `.agda` scratch files sit outside `check-tree`).
- `just check-tree src/Cat`: **59/59**. `Cat.Depreciated` (49
  modules, 15,545 lines) is green.
- `just profile Core.Kan`, cold, four runs: **1,025–1,072 ms** (run
  noise ≈ ±50 ms, acceptance criteria elsewhere cite this band).
  Named costs: `comp-pathp₂-rfill` 91 ms, `comp-pathp₂-assoc` 52,
  `hcom-unique` 47, `comp-pathp₂-commutes` 29, `comp-pathp₂-unique`
  29, `comp-pathp₂-lcoh` 25, `pcom.base.fibers` 25,
  `comp-pathp₂-rcoh` 24, `comp-pathp₂-map` 23, `contr-face` 21,
  `comp-pathp₂-over` 15, `sys-lid` 14. The `comp-pathp₂` family is
  ≈ 290–310 ms combined, ≈ 430 lines.
- Import cost of a Tier-1-sized interface in `Core.Kan` (proxy:
  `import Test.RxTier1` added, profiled twice): 1,045 and 1,067 ms:
  **neutral within the noise band**. Caveats: the real
  `Core.Rx.Base` is somewhat larger than the 209-line certificate,
  and Stage 2's restatements are a separate (refl-certified) change.

## Certificates

All four re-elaborate green from cold.

| module | cold | carries |
| --- | --- | --- |
| `Test.RxTier1` | 137 ms | The Tier-1 layer compiles on `Core.Type`+`Core.Base`+`Core.Data.Sigma`. `Singl-contr`, `prop-inhabited→is-contr` pure. `fan-of-discrete`, `disc-fan-contr` |
| `Test.RxVirtual` | 117 ms | Virtual-graph, term/coterm displays, push/pull below `Core.Kan`. Pull = op-push definitionally. The displayed-reflexivity field IS the per-hand unit law (the unital boundary) |
| `Test.RxBundle` | 187 ms | Bundled records lose graph inference at display-keyed sites. Indexed records keep it |
| `Test.KanIdentities` | 199 ms | The eight identities: `Sys`=`PartialsP` (retyping), `HSys`=`PartialsP`, `Total-sys`=fan (refl), `Total-sys-contr`=`Singl-contr` (refl), `sys-filler`=`hfil` (refl), `sys-composite`=`hcom` (refl), `SysLift`=displayed fan with `SinglP-contr` witness, the two `emb`s refl-equal |

## Displaced-composition census

20 names. 16 in `Core.Kan`: `comp-pathp`, `₁`, `₁-fill`, `₁-over`,
`₂`, `₂-fill`, `₂-over`, `₂-rfill`, `₂-unitl`, `₂-commutes`,
`₂-unique`, `₂-lcoh`, `₂-rcoh`, `₂-assoc`, `₂-map`, `pathp-ends`.
4 in `Core.Path.Base`: `₁-ap`, `₂-ap`, `₂-merge`, `₂-merge-map`.
Adjacent: `pcom→∙` (`Core.Kan`), held only by the dead
`Core.Path.Composition`.

Per-name, with direct consumers outside the defining module:

| name | direct consumers | class |
| --- | --- | --- |
| `comp-pathp` | none anywhere | **deletable now** |
| `comp-pathp₁` | `₁-ap`, `₁-over`, `Cat.Depreciated.Displayed.*` | held |
| `comp-pathp₁-fill` | `Depreciated.Displayed.Base` | held |
| `comp-pathp₁-over` | `Depreciated.Displayed.Base` | held |
| `comp-pathp₁-ap` | `Depreciated.Displayed.Coherence`, `Test.MiscFloor` | held |
| `comp-pathp₂` | `Core.Path.Exchange` (2 uses), family, Depreciated widely | held, **the transitive root** |
| `comp-pathp₂-fill` | `₂-lcoh`, `₂-rcoh`, both `Monoidal` Bifunctors | held |
| `comp-pathp₂-over` | both `Monoidal` Bifunctors | held |
| `comp-pathp₂-rfill` | `₂-unitl`, `₂-commutes`, `₂-rcoh`, `Legacy.Properties` | held |
| `comp-pathp₂-unitl` | `Legacy.Hexagon` (×3) | held |
| `comp-pathp₂-commutes` | `Monoidal.Coherence`, `Legacy.Coherence`, `Legacy.Properties` | held |
| `comp-pathp₂-unique` | `₂-assoc` | held |
| `comp-pathp₂-lcoh` | `₂-assoc` | held |
| `comp-pathp₂-rcoh` | `₂-assoc` | held |
| `comp-pathp₂-assoc` | `₂-merge`, `Legacy.Hexagon`, `Legacy.Properties` | held |
| `comp-pathp₂-map` | `₂-merge-map` | held |
| `comp-pathp₂-ap` | `₂-merge`, `Monoidal.Coherence`, Legacy | held |
| `comp-pathp₂-merge` | `₂-merge-map` only | held |
| `comp-pathp₂-merge-map` | `Legacy.Hexagon`, `Legacy.Properties` | held |
| `pathp-ends` | `Depreciated.Iso` | held |

Under invariant D8 (`Cat.Depreciated` green), **only `comp-pathp` is
deletable today**. The other nineteen sit under the placement
contract of [stage-2-discipline](stage-2-discipline.md) §2.5, which
is what keeps a hold from becoming tenure. Note the asymmetry the
table makes plain: **eighteen have no `Core` consumer at all**. They
exist in `Core.Kan` and `Core.Path.Base` only to serve a tree this
refactor deletes.

When Stage 4 retires Depreciated, the reachability cascades:
`₂-merge-map` falls, then `₂-merge`, then `₂-assoc` (whose only live
consumer it was) with its feeders `₂-unique`/`₂-lcoh`/`₂-rcoh` and
their feeders `₂-fill`/`₂-rfill`. `₁-ap` falls, then `₁`. `₂-map`
falls. **The sole transitive root after Stage 4 is `comp-pathp₂`**,
via `whisker-rl-conj`/`whisker-lr-conj` in `Core.Path.Exchange`, and
only `Test.DoubleLoopTensor` imports `Core.Path.Exchange`. Whether
anything survives is decision D9, not arithmetic.

## Dead surface in `Core.Kan`

Zero consumers src-wide: `HSys` (textually `PartialsP`), `sys-path`,
`SysExt`, `sys-lid`, `hc`, `kext`, `TotalP`, `extend→is-contr`,
`ap-comp-dep`, `path→square`, `square-sym-h`, `square-sym-v`,
`hcom-unique` (47 ms), `hcom-lid-unique`, `com-unique`,
`com-lid-unique`, `hcom-cong`. ≈ 120 lines.

Not dead, and why:

- `Chain`: `Core.Univalence` uses the combinators. Its import moves
  with Stage 2.3's relocation.
- `Total-sys`: in use through `Total-sys-contr`'s type in
  `Core.Transport.J` (`J-sys` is the contraction plus a transport).
- `conn`: `Core.Interval`, `Core.Groupoid`, `Core.Equiv.Base`,
  `Core.Function.Connected`.
- `cone`: zero live consumers, kept as Stage 3.4's transcription
  target (the gist's `ι`).
- `contr-face`: held only by `Core.Coherence.Paths` (red, imported
  only by the retired `src/All.lagda.md`). Stage-5 material, not
  live surface.
- `is-contr→extend`: one live consumer.

Aliases: `sys-composite` = `hcom` bare, `sys-filler` = `hfil`
permuted, `Sys`/`PartialsP`/`HSys` three names for one type.
Consumers to re-point at the collapse: `Core.Composite`,
`Core.Transport.J`.

## Duplication

- Singleton contractibility, three statements in unrelated modules,
  all pure (VERIFIED, `Test.RxTier1`): `Singl-contr`
  (`Core.Transport.Base`), `Singl-contr-cofan` (`Core.Groupoid`),
  `prop-inhabited→is-contr` (`Core.Transport.Properties`).
  `Cat.Graph.Refl.Properties` imports the first two from those
  unrelated homes.
- The ternary representable action, three curryings
  ([standpoint](standpoint.md) Tier 3): two full `iso→equiv` proofs
  (~110 lines) for one operation, and `yon-unbiased = repr` an alias
  with no consumers.

## Module liveness

Dead already (importer is the retired `src/All.lagda.md` only):
`Core.Path.Composition`, `Core.Path.Coherence` (red),
`Core.Coherence.Paths` (red), `Core.Coherence.Base`.

After Stage 0.1 moves `Singl-contr-cofan` to `Core.Base`,
`Core.Groupoid`'s one live consumer has its home and the module
joins `Core.Groupoid.Virtual` at zero live consumers.
`Core.Path.Exchange`'s only importer is `Test.DoubleLoopTensor`.
Fates: decisions D9, D10.

## Rename inventory (Stage 1)

Agda importers of `Cat.Graph.Refl.*`: the suite itself,
`Test.KanIdentities`, `Test.RxBundle`, all under `just mv`'s `src/`
sweep. Outside the sweep, by hand: `bin/profile` line 12
(usage-string example), `docs/guidelines/elaboration.md`,
`docs/guidelines/profiling.md`, and the 2026-07-24 notes.

## Provenance of `Core.Composite`

Token-identical to the reference's `Lib.Core.Composite` modulo
renames (`comp`→`com`, `Cyl`→`Sys`, `u`→`s`, `v`→`t`): the bodies of
`fillerP`, `HSysOps`, and `SysFunctor` match λ-for-λ. In-repo
history starts at the file's addition (`a938d00`). The
correspondence is textual. The port dropped `LiftP-is-contr`
(restored at Stage 2.1), `cyl-compose`
([unscheduled](unscheduled.md)), the `Sub`-valued filler layer
(`Fill`, `composite→Ext`, `filler→Fill`), and `subst-cyl`,
`is-virtual-system`, `plid-refl`, `ceqv`.

## Reproduction

```
just check-tree src/Core
just check-tree src/Test
just check-tree src/Cat
just profile Core.Kan       # repeat ≥2×; compare to the noise band
just profile Test.RxTier1   # and the other three certificates
rg -nP 'comp-pathp₂(?![-])' src   # census spot-checks; vary the name
```
