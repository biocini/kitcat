# Survey — 2026-07-24 — Core.Kan against Composite and the reflexive graphs

**Superseded by `docs/composite-rx-refactor/`**, the plan of record;
its `evidence.md` carries the corrected censuses with reproduction
commands. Retained as the arc's working record. The census counts
below were derived by reading rather than mechanically, and two of
them were wrong; the corrections are applied in place.

The structural findings behind `2026-07-24-rx-promotion-plan.md`. That
document is the plan; this one is why it takes the shape it does, plus
the material it does not schedule.

Sources triangulated: `Core.Kan`, `Core.Path.*`, `Core.Composite`,
`Core.Groupoid`, `Core.Groupoid.Virtual`, `Core.Coherence.*`,
`Core.Transport.*`; the reference construction at
`reference/core-category/Composite.lagda.md`; and `Core.Rx.*`.

The reference tree is not expected to typecheck — it is retained as
notes. Only the first block of `Composite.lagda.md` (the
`Lib.Core.Composite` module, ll. 1–237) is inside its code fence; the
`VG.Native` material from l. 238 sits outside the fence, carries
holes, and was never checked.

Certificates: `Test.KanIdentities`, `Test.RxTier1`, `Test.RxVirtual`,
`Test.RxBundle`.

## One theorem, four costumes

| | the space | centre | contraction |
| --- | --- | --- | --- |
| `Core.Kan` | `Total-sys φ s = Σ x , sys-composite φ s ≡ x` | `(composite , plid)` | `p i , λ j → p (i ∧ j)` |
| reference | `Comp φ u = Σ s , composite φ u ≡ s` | `(composite , plid)` | `p i , λ j → p (i ∧ j)` |
| `Core.Transport.Base` | `Σ y , x ≡ y` | `(x , refl)` | `q i , λ j → q (i ∧ j)` |
| `Core.Rx` | `rx.fan (discrete A) x` | `fan-center x` | via `prop-inhabited→is-contr` |

Not an analogy. VERIFIED (`Test.KanIdentities`): `Total-sys φ s` is
`rx.fan (discrete A) (sys-composite φ s)` and `Total-sys-contr φ s` is
`Singl-contr (sys-composite φ s)`, both by `refl`. The reference's
`Comp-is-contr` is the same term again modulo renaming.

Reading: a Kan operation is a choice of centre in a contractible fan.
`hcom` picks the centre, `hfil` is the contraction, and every
uniqueness lemma in `Core.Kan` is `is-contr→is-prop` at some fan.
`Core.Rx` already has that vocabulary; `Core.Kan` re-derives it.

## `Sys` is the reference's `Cyl`

| reference | in tree | relation |
| --- | --- | --- |
| `Cyl φ A` | `Core.Kan.Sys φ A` | identical |
| `base φ u` | `sys-base φ u` | identical |
| `lid u` | `sys-lid u` | identical |
| `Ext φ u` | `SysExt φ u` | identical |
| `composite φ u` | `sys-composite φ u` (= `hcom`) | identical (VERIFIED) |
| `filler φ u i` | `sys-filler φ s i` (= `hfil φ i s`) | identical (VERIFIED) |
| `filler.plid`/`pbase` | `sys-filler.plid`/`pbase` | identical |
| `HCyl`, `hfiller`, `hcomposite` | `Core.Composite.HSysOps` | ported |
| `CylP`/`baseP`/`fillerP`/`compP` | `Core.Composite.SysP` | ported |
| `CylFunctor` | `Core.Composite.SysFunctor` | ported |
| `Comp`, `Comp-is-contr` | `Core.Kan.Total-sys{,-contr}` | ported, relocated |
| `J-cyl`, `𝓙` | `Core.Transport.J.J-sys`, `J` | ported, relocated |

So `Core.Composite` is the in-tree descendant of the reference. It is
reachable only through `Core.Prelude`; nothing imports it directly.

Dropped in the port:

1. **`cyl-compose`** — no analogue anywhere in `src/`. See below.
2. **`LiftP-is-contr`** — `SysP` kept `syslift-center` and lost the
   contractibility, which is the load-bearing half. Scheduled as plan
   item 2.1.
3. `Fill`, `composite→Ext`, `filler→Fill` — the `Sub`-valued filler.
   `Core.Kan`'s `hcom-unique`/`hcom-lid-unique`/`com-unique`/
   `com-lid-unique` are stronger, and unused.
4. `subst-cyl`, `is-virtual-system`, `plid-refl`, `ceqv`.

## The Kan condition is a covariant fibration

VERIFIED (`Test.KanIdentities`). For `P : A → Type v`, the displayed
graph over `discrete A` with `edge x y p a b = PathP (λ i → P (p i)) a b`
has `SysLift p a` as its displayed fan on the nose, and

```agda
probe-lift-contr : rx.is-cov-fibration (discrete A) disp-of
probe-lift-contr x y p a = SinglP-contr {A = λ i → P (p i)} a
```

So `push` is `transport`, `lift` is `transport-filler`, and
`lift-unique` is `SinglP-contr .paths`. Every type family is both a
covariant and a contravariant fibration over `discrete A`, and that is
the content of `transp`.

This is the sharpest of the three connections and the one the port
dropped.

## `HComposite` is an unbiased lens

`HComposite p q r = Σ s , HCell p q r s` has a left leg, a right leg, a
middle, and a composite. `unbiased-lens` has `linj`, `rinj`,
`munitor`, `runitor` over an edge-indexed family.

| unbiased lens | `Core.Kan` | `Core.Groupoid` |
| --- | --- | --- |
| edge-indexed family | `HCell p q r`, indexed by the middle | `emb`, indexed by the tight cell |
| `linj` | `pcom.lsplit` | `yon` |
| `rinj` | `pcom.rsplit` | `noy` |
| `munitor` | `pcom.unit` | `emb-parametric` |
| `runitor` | `pcom.ideml`/`idemr` | `yon-comp`/`noy-comp` |
| `unb-lens-structure-is-prop` | `pcom.contr` | `representable-contr` |

The three representability developments are three curryings of one
ternary operation. VERIFIED (`Test.KanIdentities`):

```agda
emb a y q z r ≡ repr.emb {A = λ _ → A} q w a z r   -- refl
```

- `Core.Groupoid.emb` represents the left leg (`representable-contr`)
- `Core.Groupoid.Virtual.repr.emb` the middle (`repr-singl-contr`);
  `repr.op-emb` is its argument swap
- `Core.Path.Composition.Repr` is a third copy of the middle one

Two full `iso→equiv` proofs (`emb-equiv` ≈60 lines, `repr.emb-equiv`
≈50) for one operation. `Core.Groupoid.Virtual` already carries
`yon-unbiased = repr`, an alias with no consumers.
`Lens.unb-lens-structure-is-prop` shows the general route: uncurry
over the fan, collapse at the centre with `Π-contr-dom`, read off the
residual fan or cofan.

## `cyl-compose` — unscheduled, and the one idea with no analogue

```agda
cyl-compose : (φ ψ : I) (t₁ : Cyl φ A) (t₂ : Cyl ψ A)
            → composite φ t₁ ≡ base ψ t₂ → Cyl (φ ∨ ψ) A
cyl-compose φ ψ t₁ t₂ p i (φ = i1) = p (ψ ∧ ~ i)
cyl-compose φ ψ t₁ t₂ p i (ψ = i1) = p (φ ∧ ~ i)
cyl-compose φ ψ t₁ t₂ p i (i = i0) = p (φ ∧ ψ)
```

Composition problems compose: a system on `φ`, a system on `ψ`, and an
identification of the first's composite with the second's base give a
system on `φ ∨ ψ`. This makes `Sys` a structure over the lattice of
face formulas — the cut of the virtual double category of tubes.

Every `Core.Kan` site that writes a boundary like `∂ i ∨ ∂ j` or
`∂ i ∨ ~ j` and shuffles faces by hand is doing this inline:
`cat.rfill`, `cat.bfill`, `cat.lcoh`, `cat.rcoh`, `Path.paste-refl`,
`Path.commutes`, `pcom.lsplit`, `pcom.rsplit`, `pcom.catl`,
`pcom.catr`. Ten instances of one operation.

Not scheduled in the plan, pending the two questions below.

## Reference questions (Lane's call)

1. **`cyl-compose`'s clauses** mention only `p`, never `t₁ .walls` or
   `t₂ .walls`. That looks wrong for a genuine gluing and may be a
   placeholder. Determines whether the section above is worth
   anything.
2. **`hcom` at reference l. 109** —
   `hcom φ t p = hcomp i1 (cyl-compose φ i1 t (λ _ _ → s) p)` — shadows
   `Core.Kan.hcom` with an unrelated operation. Rename, or deliberate?
3. **`Cyl-map-filler`** is commented out with the note "Also
   definitional". It is not: `Cyl-map-composite` directly above needs a
   real `hcom`, and `f` does not commute with `hcomp`. The in-tree
   `SysFunctor` correctly omits it. Correct the reference, or leave it
   as the historical record?
4. **The `Sub` layer** — `Fill`, `composite→Ext`, `filler→Fill`. Keep
   it at all, or let `Total-sys` plus `is-prop` carry it?

## Name-level censuses

Measured 2026-07-24. `Cat.Depreciated` and `src/Test` excluded from
"live".

### Displaced composition

Live consumers are `Core.Path.Base` and `Core.Path.Exchange` only.

| name | defined in | live consumers |
| --- | --- | --- |
| `comp-pathp₂` | `Core.Kan` | `Core.Path.Base`, `Core.Path.Exchange` |
| `comp-pathp₁` | `Core.Kan` | `Core.Path.Base` |
| `comp-pathp₂-assoc` | `Core.Kan` | `Core.Path.Base` |
| `comp-pathp₂-map` | `Core.Kan` | `Core.Path.Base` |
| `comp-pathp` | `Core.Kan` | — |
| `comp-pathp₁-fill` | `Core.Kan` | — |
| `comp-pathp₁-over` | `Core.Kan` | — |
| `comp-pathp₂-fill` | `Core.Kan` | — |
| `comp-pathp₂-over` | `Core.Kan` | — |
| `comp-pathp₂-rfill` | `Core.Kan` | — |
| `comp-pathp₂-unitl` | `Core.Kan` | — |
| `comp-pathp₂-commutes` | `Core.Kan` | — |
| `comp-pathp₂-unique` | `Core.Kan` | — |
| `comp-pathp₂-lcoh` | `Core.Kan` | — |
| `comp-pathp₂-rcoh` | `Core.Kan` | — |
| `pathp-ends` | `Core.Kan` | — |
| `comp-pathp₁-ap` | `Core.Path.Base` | — |
| `comp-pathp₂-ap` | `Core.Path.Base` | — |
| `comp-pathp₂-merge` | `Core.Path.Base` | — |
| `comp-pathp₂-merge-map` | `Core.Path.Base` | — |

Reachability inside `Core.Kan` from the live roots: `-assoc` uses
`-unique`, `-lcoh`, `-rcoh`; `-lcoh` uses `-fill`; `-rcoh` uses
`-rfill`. So those five are held.

**Deletable now (1):** `comp-pathp`, which has no consumer anywhere.

The six names first listed alongside it — `comp-pathp₂-commutes`,
`-unitl`, `-over`, `comp-pathp₁-fill`, `-over`, `pathp-ends` — are
not deletable: each has a live consumer in `Cat.Depreciated`, and
that tree typechecks (59/59 under `src/Cat`), so deleting them breaks
the build. The error was reading this survey's own "live" convention,
which excludes `Cat.Depreciated`, as a deletion licence. It is not
one while the deprecated tree stands as the porting reference.

**Held under the placement contract (19):** everything but
`comp-pathp`. The holds cascade — `₂-merge-map`, then `₂-merge`, then
`₂-assoc` with `₂-unique`/`₂-lcoh`/`₂-rcoh` and their
`₂-fill`/`₂-rfill`; `₁-ap` then `₁`; `₂-map`; and the six above.

**Surviving root (1):** `comp-pathp₂`, via two uses in
`Core.Path.Exchange` — itself imported only by
`Test.DoubleLoopTensor`. The "surviving roots (4)" this survey first
recorded counted one step of reachability; transitively `₁`,
`₂-assoc` and `₂-map` are held only by consumers that retire with
`Cat.Depreciated`.

Cost: the family is ~430 lines of `Core.Kan` and ≈300 ms of its
~1,050 ms cold elaboration; `comp-pathp₂-rfill` alone is ≈90 ms.

### Dead surface in `Core.Kan`

No consumers outside `Core.Kan`: `HSys` (textually identical to
`PartialsP`), `sys-path`, `SysExt`, `sys-lid`, `hc`, `kext`, `TotalP`,
`extend→is-contr`, `ap-comp-dep`, `path→square`, `square-sym-h`,
`square-sym-v`, `hcom-unique`, `hcom-lid-unique`, `com-unique`,
`com-lid-unique`, `hcom-cong`.

`Chain` was listed here in error: `Core.Univalence` uses the chain
combinators, so its relocation to `Core.Path` carries an import fix.

`Total-sys` shows no textual consumer but is load-bearing through
`Total-sys-contr`'s type, which `Core.Transport.J` uses.

Live and staying: `Sys`, `sys-base`, `sys-composite`, `sys-filler`
(`Core.Composite`, `Core.Transport.J`), `PartialsP`
(`Core.Composite`), `conn` (`Core.Interval`, `Core.Groupoid`,
`Core.Equiv.Base`, `Core.Function.Connected`), `contr-face`
(`Core.Coherence.Paths`).

`sys-composite = hcom` is a bare alias, and the plumbing layer speaks
`hcom`. `sys-filler` is `hfil` with arguments permuted; `sys-path` is
`sys-filler` eta-expanded. `Sys φ A` is `PartialsP φ (λ _ → A)`
(VERIFIED), so there are three names for one type.

### Duplicated contractibility

`Singl-contr` (`Core.Transport.Base`) and `Singl-contr-cofan`
(`Core.Groupoid`) live in unrelated modules; `Core.Rx.Properties`
imports one from each. Both are pure — no `transp`, no `hcom` —
and belong in `Core.Base` (VERIFIED: `Test.RxTier1` defines both with
imports restricted to `Core.Type`/`Core.Base`/`Core.Data.Sigma`).

`prop-inhabited→is-contr` (`Core.Transport.Properties`) is likewise
two lines and pure.

### Broken modules

`Core/Coherence/Paths.lagda.md` — 4 holes (`face₁₄`, `face₄₅`,
`face₁₂`, `face₃₅`), a 25-line commented `face₂₃`, and a fully
commented named `pentagon`.

`Core/Path/Coherence.lagda.md` — 9 holes, plus a mis-attributed import
at l. 20 (`is-contr→is-set` and `total-contr-unique` are `Core.Kan`'s,
not `Core.Transport.Base`'s), which is fatal on its own under
`-Werror`.

Both attack Mac Lane coherence for the path groupoid by explicit
cube-filling, from two different routes — `HComposite` contractibility
and the `E₃` representable fiber — and neither is finished.
`Core.Coherence.Base` already isolates the right engine
(`coh-project`, `coh-project₃`, `coh-project-glued`) and typechecks.

### Guidelines

24 live-tree references, banned by `docs/guidelines/CLAUDE.md`:
17 `file:line` citations into `src/` (`module-anatomy` 10, `naming` 2,
`definitions-and-proofs` 3, `records` 1, `profiling` 1) and 7
dot-paths (`module-anatomy` 3, `definitions-and-proofs`,
`elaboration`, `profiling`, `prose-and-comments` 1 each).
`docs/guidelines/README.md` additionally advertises the banned
practice.

## Environment

`just check-tree src/Core` — 137 of 139 pass, the two failures above.
`just check-tree src/Cat` — 59 of 59 pass, `Cat.Depreciated` included
(49 modules, 15,545 lines, green). `just profile Core.Kan` —
1,025–1,072 ms cold across four runs; treat ±50 ms as noise rather
than reading a single figure as a baseline. `Core.Rx` — two
external Agda importers, `Test.KanIdentities` and `Test.RxBundle`,
plus textual references in `bin/profile`, `docs/guidelines/`, and
these notes.
