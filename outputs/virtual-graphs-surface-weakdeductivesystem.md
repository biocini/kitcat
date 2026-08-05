# Surface audit: `Bb.WeakDeductiveSystem` against `Bb.VirtualGraphs`

Read-only content-level audit. Every `.lagda.md` file in
`src/Bb/WeakDeductiveSystem/` (sixteen modules) checked against its
claimed or inferred destination in `src/Bb/VirtualGraphs/`, by direct
comparison of identifiers and proof terms, not by matching citation
text.

## Method

`Bb.WeakDeductiveSystem` is the tree frozen at commit `1db09db`: a
verbatim copy of `Cat.Logic` as it stood immediately before the (D′)
record cut of 2026-07-28
(`src/Bb/WeakDeductiveSystem/README.md:42-57`). `Cat.Logic` still
carries same-named successor modules for every file in
`Bb.WeakDeductiveSystem` except the five modules Lane moved into the
archive outright (`NeutralUnit`, `TwistFidelity`,
`AssociatesCountermodel`, `FramedCut`, `FramedGroup` — these have no
live `Cat.Logic.Gist` counterpart, only the archived one).

For every `Bb.WeakDeductiveSystem` file with a same-named
`Cat.Logic` counterpart, `diff -u` against that counterpart shows the
gap is small and mechanical: module-path renames, prose micro-edits,
and (where relevant) the `readback` field the (D′) cut added. No
diff introduces or removes a theorem beyond that field. Since the
`Bb.VirtualGraphs.CHANGELOG.md` documents vendoring the *current*
`Cat.Logic.*`/`Cat.Logic.Gist.*` modules "entire" into named
`Bb.VirtualGraphs` destinations, and the diffs show
`Bb.WeakDeductiveSystem`'s content is a near-subset of those same
`Cat.Logic` modules, the content is covered by that Cat.Logic-channel
vendoring even where the `Bb.VirtualGraphs.CHANGELOG.md` names only
`Bb.WeakDeductiveSystem` for a narrower slice (e.g. `Base`'s pin-K
route) or does not name `Bb.WeakDeductiveSystem` at all. Every such
claim below is checked directly against the destination file's text,
not inferred from the diff alone.

One systematic, tree-wide finding recurs across nearly every file and
is stated once here rather than repeated: `Bb.VirtualGraphs` never
restates the four record-bundling constructions `is-invertible`
(combining `fiber⁻`/`fiber⁺`), `is-composable` (combining
`contr⁺`/`contr⁻`), `is-deductive-system` (combining `stable`/
`composable`/`invertible` or `composable`/`invertible`), and
`deductive-system` (the `graph`+`axioms` package, with `opᴰ`/
`opᴰ-invol`/`op-axioms`). Confirmed absent by exhaustive grep:

```
rg -n "record is-invertible|record is-composable" src/Bb/VirtualGraphs/
rg -n "is-deductive-system|^record deductive-system|opᴰ" src/Bb/VirtualGraphs/
```

both return no hits in `Bb.VirtualGraphs`. This is architectural, not
a content loss: every constituent theorem the records would bundle
(`is-invertible⁻`, `is-invertible⁺`, `is-composable⁺`,
`is-composable⁻`, and their `is-prop` lemmas) is present individually
throughout the tree, consistent with the tree's stated design —
"flat-parameter lemma modules over one minimal carrier" — which never
bundles structure into records the way the source trees do. Below,
this is marked **(record-bundling gap, tree-wide)** at each file
where it recurs, rather than re-argued.

---

## Explicitly cited (six)

### `Base.lagda.md` (698 lines) → `Tower.lagda.md` (320 lines) +
### `Stability.lagda.md`, `Framing.lagda.md`, `Pentagon.lagda.md`

The `Bb.VirtualGraphs.CHANGELOG.md` cites `Base` only for its "pin-K
absorption route" into `Tower`. That route — `module tower`
(`Base.lagda.md:345-401`), `module mixed`
(`Base.lagda.md:413-449`), and `module unital` with `collapse⁺`/
`collapse⁻` (`Base.lagda.md:461-498`) — is present verbatim in
`Tower.lagda.md:33-116` (`tower⁺`/`tower⁻`/`tower`),
`Tower.lagda.md:126-161` (`mixed`, `associates`, `thunkable`,
`linear`), and `Tower.lagda.md:269-320` (`absorption`, `unital`,
`collapse⁺`/`collapse⁻`).

The CHANGELOG's group A–D′ entry separately names `Cat.Logic.Base` as
a source for `Stability`/`Framing`/`Pentagon`/etc. Since
`Bb.WeakDeductiveSystem.Base` is a near-subset of `Cat.Logic.Base`
(confirmed by `diff -u src/Bb/WeakDeductiveSystem/Base.lagda.md
src/Cat/Logic/Base.lagda.md`), the rest of `Base`'s content is
covered through that channel:

| `Base.lagda.md` | Destination |
| --- | --- |
| `opⱽ`, `opⱽ-invol` (38-46) | `Stability.lagda.md:99-105` |
| `cell⁻`, `cell⁺` (66-70) | `Framing.lagda.md:164-168` |
| `is-invertible⁻`, `is-invertible⁺` + is-prop (82-92) | `Framing.lagda.md:63-67`, `108-112` |
| `is-stable`, `is-stable-is-prop`, `reflect-lc`, `contr-from-stable`, `stable-is-embedding`, `stable-from-hom-sets` (132-164) | `Stability.lagda.md:62-91` + `Framing.lagda.md:176-181` |
| `inj⁺`/`inj⁻`, `composite⁺`/`composite⁻`, `is-composable⁺`/`⁻` + is-prop (179-214) | `Framing.lagda.md:74-88`, `114-127` |
| `op-stable` (275-282) | `Stability.lagda.md:112-118` |
| `op-invertible⁻`/`⁺` type-level facts (265-269) | `Framing.lagda.md:202-208` |
| `module pentagon⁺`, full proof (510-698) | `Pentagon.lagda.md:30-228` (verbatim, confirmed by direct comparison) |

Gaps, all instances of the record-bundling gap above: `record
is-invertible` (94-104), `record is-composable` (221-231), `record
is-deductive-system` (236-255), `record deductive-system`/`opᴰ`/
`opᴰ-invol` (313-333), the combined `op-invertible`/`op-composable`/
`op-axioms` transports (271-273, 289-306).

**Verdict: FULLY VENDORED** for the cited pin-K route; **COVERED BY
OVERLAP with Cat.Logic** (via the group A–D′ vendoring) for the rest,
minus the tree-wide record-bundling gap.

### `Gist/NeutralUnit.lagda.md` (138 lines) → `Interchange.lagda.md`,
### `neutral-unit` module (252-307)

Every identifier present verbatim: `is-interchanging`
(`NeutralUnit.lagda.md:38-41` → `Interchange.lagda.md:41-43`),
`⨾-agree`, `unitl⁺`, `unitr⁻`, `twists-agree`, `ι`, `ι-twist⁻`,
`ι-twist⁺`, `ι-either`, `ι-unitl⁺`, `ι-unitr⁺`, `ι-unitl⁻`,
`ι-unitr⁻` (`NeutralUnit.lagda.md:63-116` → `Interchange.lagda.md:267-301`,
identical proof terms).

**Verdict: FULLY VENDORED.**

### `Gist/TwistFidelity.lagda.md` (101 lines) → `Interchange.lagda.md`,
### `tortile` module (320-363)

`inverse⁻`, `inverse⁺`, `inverse⁻-collapses`, `inverse⁺-collapses`,
`natural⁻`, `natural⁺`, `natural⁻-is-unitl`, `natural⁺-is-unitr`,
`twist-interchange`, `twist-interchange-collapses`
(`TwistFidelity.lagda.md:56-101` → `Interchange.lagda.md:334-363`,
identical proof terms).

**Verdict: FULLY VENDORED.**

### `Gist/AssociatesCountermodel.lagda.md` (318 lines) →
### `Bool/Readers.lagda.md`, `projection`+`four-reader` modules (54-256)

`projection` module — `rf`/`emb`, `S`, `C⁺`, `C⁻`, `no-associates`,
`no-thunkable`, `no-linear`, `no-invertible⁻`, the framed-carrier
readback check `no-associates-readback`
(`AssociatesCountermodel.lagda.md:63-149` →
`Bool/Readers.lagda.md:56-117`, present with the flat-parameter
carrier and `framed-interchange` in place of the archived `framed`
record). `four-reader` module — `M`, `π₁`/`π₂`/`κ₁`/`κ₂`, `rf`,
`model`, `S`, `C⁺`, `C⁻`, `tier⁻`, `tier⁺`, `no-associates`,
`centre⁻-thunkable`, `centre⁺-linear`, `no-thunkable-twist`,
`no-thunkable-κ`, `no-linear-centre⁻`, `no-linear-κ`
(`AssociatesCountermodel.lagda.md:160-318` →
`Bool/Readers.lagda.md:129-256`, identical proof terms).

Gap: `D : is-deductive-system model`
(`AssociatesCountermodel.lagda.md:265-271`) — the record-bundling gap.

**Verdict: FULLY VENDORED**, minus the record-bundling gap.

### `Gist/FramedCut.lagda.md` (277 lines) → `Groupoid/Path.lagda.md`,
### `path` module (39-277)

Every identifier present verbatim: `emb`, `emb-equiv`, `PG`,
`term-contr`, `coterm-contr`, `recentre`, `curry≃`, `reflect-equiv`,
`slot≃`, `slot-swap≃`, `coact-π-equiv`, `act-π-equiv`, `PG-stable`,
`PG-composable⁻`, `PG-composable⁺`, `PG-unital⁻`, `PG-unital⁺`,
`cell-fiber⁻`, `cell-fiber⁺`, `pin⁻-axiom`, `pin⁺-axiom`, `pin⁻`,
`pin⁺`, `twist⁺-centre`, `twist⁻-centre`, `twist⁺-unique`,
`twist⁻-unique`, `cancels`, `trivial⁻`, `trivial⁺`, `module
cancelled`, `neutral⁻`, `neutral⁻-absorb`, `neutral⁻-unitr`,
`neutral⁺`, `neutral⁺-absorb`, `neutral⁺-unitl`, `twist-is-neutral⁻`,
`twist-is-neutral⁺` (`FramedCut.lagda.md:36-256` →
`Groupoid/Path.lagda.md:39-238`, identical proof terms). Plus a new
`one-twist` module (`Groupoid/Path.lagda.md:247-277`) not in the
source, sourced from `Bb.OneTwist.Models`' path model per the
CHANGELOG.

Gap: `PG-composable`, `PG-unital`, `PG-deductive`, `PG-system`
(`FramedCut.lagda.md:117-133`) — the record-bundling gap.

**Verdict: FULLY VENDORED**, minus the record-bundling gap.

### `Gist/FramedGroup.lagda.md` (373 lines) → `Group/Abelian.lagda.md`,
### `framed` module (78-333) + `one-twist` module (369-421)

Every identifier present verbatim: `unitr`, `invr`, `cancel-l`,
`cancel-r`, `univalent→prop`, `transmit-injective`, `stable`, `cut⁻`,
`cut⁺`, `composable⁻`, `composable⁺`, `coact-π-injective`,
`act-π-injective`, `unital⁻`, `unital⁺`, `pin⁻`, `pin⁺`, `cancels→`,
`→cancels`, `cuts-agree→`, `→cuts-agree`, `both→`,
`unit⁻-is-inverse`, `unit⁺-is-inverse`, `ι⁻`, `ι⁺` and the cubic
lemmas, `ι⁻-unit⁺→square`, `cancels→ι⁻-unit⁺`, `absorber⁻-is-inverse`,
`absorber⁻-is-twist⁺`, `string`, `string-rep`, `cut⁻-is-twisted`,
`cut⁺-is-twisted`, `string-twists`, `cut[_]`, `self-consistent`,
`self-consistent→cancels`, `cancels→self-consistent`
(`FramedGroup.lagda.md:40-373` → `Group/Abelian.lagda.md:41-361`,
identical proof terms). Plus a new `one-twist` module
(`Group/Abelian.lagda.md:369-421`) from `Bb.OneTwist.Models`' group
model per the CHANGELOG.

Gap: `deductive`, `system`
(`FramedGroup.lagda.md:186-197`) — the record-bundling gap.

**Verdict: FULLY VENDORED**, minus the record-bundling gap.

---

## Not explicitly cited (ten)

### `Type.lagda.md` (171 lines) → `Type.lagda.md` (44 lines, the
### axiom-free core) + `Framing.lagda.md` (twist-dependent vocabulary)
### + `Stability.lagda.md` (representability)

`diff -u src/Bb/WeakDeductiveSystem/Type.lagda.md
src/Cat/Logic/Type.lagda.md` shows the only semantic addition in
`Cat.Logic.Type` is the `readback` field the (D′) cut introduced;
everything else is prose and a framing-register renaming
(`pin`/`K`→`cancel`/`centre`). The carrier core — `ob`, `hom`,
`term`, `coterm`, `argument`, `conclusion`, `judgment`, `reflect`
(`Type.lagda.md:20-53`, `72-76`) — is present verbatim in
`VirtualGraphs/Type.lagda.md:21-42`. `twist⁺`/`twist⁻` are no longer
record fields; they became explicit parameters threaded through every
downstream module (the tree's stated "minimal carrier" design), so
`var`/`covar`/`axiom` (`Type.lagda.md:103-112`) live in
`Framing.lagda.md:47-48,99-100,139-141` and `coact-π`/`act-π`/
`coact`/`act` (`Type.lagda.md:121-132`) in `Framing.lagda.md:50-54,
102-106`. `is-representable`/`normal`/`hom≃total-representable`
(`Type.lagda.md:150-171`) are in `Stability.lagda.md:32-53`. The
named wrappers `argue`/`intro`/`elim` (`Type.lagda.md:138-146`) are
not restated as named functions — the pairing/projection they wrap
is used inline throughout — a naming-level, not content, gap.

**Verdict: COVERED BY OVERLAP with Cat.Logic** (group X /
group A-D′ vendoring).

### `Graph.lagda.md` (140 lines) → `Graph.lagda.md` (140 lines)

`diff -u` against `Cat.Logic.Graph.lagda.md` shows only module-path
renames — zero semantic difference. Every identifier confirmed
present in `VirtualGraphs/Graph.lagda.md`: `graph⁺`/`graph⁻`
(`Graph.lagda.md:30-38`) → `rxgraph` +  `graphs` module
(`VG/Graph.lagda.md:29-34,57-59`); `term-is-cofan`,
`coterm-is-fan`, `var-is-cofan-center`, `covar-is-fan-center`,
`univalence-shared` (`Graph.lagda.md:52-70`) →
`VG/Graph.lagda.md:70-83`; `op-graph⁺`/`op-graph⁻`
(`Graph.lagda.md:80-84`) → `op-rxgraph` (`VG/Graph.lagda.md:43-46`,
merged since `graph⁺`/`graph⁻` merged into one `rxgraph`
constructor); `two-sided` module — `base`, `base-vtx`, `base-edge`,
`base-rx-is-axiom`, `bipush`, `judgment-fam`
(`Graph.lagda.md:96-124`) → `VG/Graph.lagda.md:103-121`; `term-fam`/
`coterm-fam` (`Graph.lagda.md:135-139`) → `VG/Graph.lagda.md:135-138`.

**Verdict: COVERED BY OVERLAP with Cat.Logic** (group X vendoring,
"`Graph` and `Display` are group X, from `Cat.Logic.Graph` and
`Cat.Logic.Display`" — `Bb/VirtualGraphs/CHANGELOG.md:84-86`).

### `Display.lagda.md` (181 lines) → `Display.lagda.md` (188 lines)

`diff -u` against `Cat.Logic.Display.lagda.md` shows only the
pin/K→cancel refactor (same content, `absorb⁻`/`absorb⁺` derived
from one `cancel` hypothesis instead of two `pin`+`K`) plus
module-path renames. Every identifier confirmed present in
`VirtualGraphs/Display.lagda.md`: `framed` module — `absorb⁻`,
`absorb⁺`, `term-lens`, `coterm-lens`, both `disp-univalent`
(`Display.lagda.md:35-70`) → `VG/Display.lagda.md:37-77`; `coslice`,
`cuts` module — `coslice-fibration`, `F`, `push-is-cut`,
`lift-is-witness`, `coslice-univalent`
(`Display.lagda.md:80-114`) → `VG/Display.lagda.md:91-116`;
`bipush-axiom`, `judgment-lens`, `judgment-disp-univalent`
(`Display.lagda.md:122-132`) → `VG/Display.lagda.md:124-135`;
`push-is-composite⁺`/`⁻`, `cospan-from-cuts`, `cuts-from-cospan`
(`Display.lagda.md:141-162`) → `VG/Display.lagda.md:144-165`;
`bipush-comp` (`Display.lagda.md:174-181`) → `VG/Display.lagda.md:181-188`.

**Verdict: COVERED BY OVERLAP with Cat.Logic** (group X vendoring).

### `Gist/FramedInterchange.lagda.md` (296 lines) →
### `Interchange.lagda.md`, `framed-interchange` module (54-241)

`diff -u` against `Cat.Logic.Gist.FramedInterchange.lagda.md` shows
zero semantic difference beyond the module header — the file is
byte-identical content otherwise. The `Bb.VirtualGraphs.CHANGELOG.md`
names `Cat.Logic.Gist.FramedInterchange`'s `framed` record as the
source dissolved into `Interchange`'s frame theory
(`CHANGELOG.md:109-112`). Every identifier confirmed present
verbatim, proof terms identical: `_⨾⁺_`/`_⨾⁻_`, `reflect-⨾⁺`/`⁻`,
`coact-covar`, `act-var`, `unitr⁺`, `unitl⁻`, `frame-⨾⁺`, `frame-⨾⁻`,
`interchange→involutive`, `⨾⁻-is-act`, `⨾⁺-is-coact`, `read⁺`,
`read⁻`, `mixed-assoc`, `two-sided→involutive`, `act-⨾⁻`, `assoc⁻`,
`module cancellation` (`factor`, `twist⁺-absorbs`,
`cancel⁺-from-cancellable`), `readable`, `readable→unitl⁻`,
`readable-unique`, `twist⁻-readable`
(`FramedInterchange.lagda.md:96-296` → `Interchange.lagda.md:64-241`).

Gap: the `framed` record itself
(`FramedInterchange.lagda.md:25-88`) is not restated as a record —
its fields (`ob`/`hom`/`reflect`/`twist⁺`/`twist⁻`/`readback`/`cut⁺`/
`cut⁻`) became the explicit module telescope of `framed-interchange`
(`Interchange.lagda.md:54-62`). Architectural relocation, not a loss.

**Verdict: COVERED BY OVERLAP with Cat.Logic**
(`Cat.Logic.Gist.FramedInterchange`, vendored into `Interchange`).

### `Gist/BalancedBase.lagda.md` (173 lines) → `Readback.lagda.md`,
### `hand⁺`/`hand⁻`/`contr-cut⁻`/`residues` modules (29-151)

`diff -u` against `Cat.Logic.Gist.BalancedBase.lagda.md` shows only
prose and module-path changes. The `rehearsal.cuts` module content
— `⨾⁺-is-coact`, `unitr⁺`, `⨾⁻-is-act`, `unitl⁻`, `composite⁻-twist`,
`stable-from-contr-cut⁻`, `K⁻-from-unitr⁻`, `K⁺-from-unitl⁺`,
`pin⁻-from-crossing`, `pin⁺-from-crossing`
(`BalancedBase.lagda.md:64-173`) is present verbatim in
`Readback.lagda.md:29-150` (`hand⁺`, `hand⁻`, `contr-cut⁻`,
`residues` modules — same names except `K⁻-from-unitr⁻` etc. moved
into the `residues` module unchanged).

Gap: the `bgraph` record and `opᴮ`/`opᴮ-invol`
(`BalancedBase.lagda.md:31-50`) — `bgraph` bundled `graph`+`readback`
into one record; this is now obsolete by construction, since
`readback` is threaded as an explicit parameter (`R :
framing.readback-of ...`) rather than wrapped in a carrier record.
Architectural relocation, consistent with the record-bundling gap.

**Verdict: COVERED BY OVERLAP with Cat.Logic**
(`Cat.Logic.Gist.BalancedBase`, vendored into the group A–D′ theory,
specifically `Readback`).

### `Gist/BalancedProfile.lagda.md` (263 lines) → `Balanced.lagda.md`,
### `at-strength` module (103-132) + `Bool/Readers.lagda.md`,
### `attempt₁`/`attempt₂` modules (268-384)

`diff -u` against `Cat.Logic.Gist.BalancedProfile.lagda.md` shows
only prose, module-path renames, and the `readback` field added to
the two carrier models (new content, not a WDS omission).
`module profile.at-strength` — `centre⁻-twist⁺`, `centre⁺-twist⁻`,
`cancel⁻`, `cancel⁺`, `unitl⁺`, `unitr⁻`, `S`, `associates-at-twists`
(`BalancedProfile.lagda.md:54-93`) is present verbatim in
`Balanced.lagda.md:103-132` (`at-strength` module — identical names,
identical proof terms). `module attempt₁`
(`BalancedProfile.lagda.md:106-172`) and `module attempt₂`
(`BalancedProfile.lagda.md:186-251`) are present verbatim in
`Bool/Readers.lagda.md:268-329` and `330-384` respectively (identical
carriers, identical `no-cut⁻`/`no-cut⁺` refutations).

**Verdict: COVERED BY OVERLAP with Cat.Logic**
(`Cat.Logic.Gist.BalancedProfile`, vendored into `Balanced` for the
general theory and into `Bool.Readers` for the two carrier models,
per `CHANGELOG.md:44`).

### `Gist/ReflectFiber.lagda.md` (324 lines) → `Engine.lagda.md`,
### `chosen`/`composable`/`engine` modules (41-324)

`diff -u` against `Cat.Logic.Gist.ReflectFiber.lagda.md` shows only
prose and module-path changes. Every identifier present verbatim:
the inlined carrier vocabulary — `var`, `covar`, `coact-π`, `act-π`,
`coact`, `act`, `composite⁻`, `composite⁺`
(`ReflectFiber.lagda.md:37-113`) → `Engine.lagda.md:44-78`; `module
composable` — `_⨾⁻_`/`_⨾⁺_`, `reflect-⨾⁻`/`⁺`, `coact-π-⨾⁻`,
`act-π-⨾⁺`, `coact-⨾⁻`, `act-⨾⁺` (`ReflectFiber.lagda.md:123-159`) →
`Engine.lagda.md:89-125`; `module engine` — `unit⁻`/`unit⁺`,
`unit⁻-absorb`/`⁺-absorb`, `unit⁻-unique`/`⁺-unique`, `coact-unit`,
`act-unit`, `composite⁻-unitr`, `composite⁺-unitl`,
`reflect-fiber-contr⁻`/`⁺`, `reflect-lc`, `reflect-embedding`,
`ap-reflect-equiv`, `ap-reflect-embedding`, `composite⁻-assoc`,
`assoc⁻`, `composite⁺-assoc`, `assoc⁺`, `unitr⁻`, `unitl⁺`
(`ReflectFiber.lagda.md:168-302`) → `Engine.lagda.md:136-251`
(identical proof terms).

**Verdict: COVERED BY OVERLAP with Cat.Logic**
(`Cat.Logic.Gist.ReflectFiber`, vendored entire into `Engine`, per
`CHANGELOG.md:15-16`).

### `Gist/RxDict.lagda.md` (351 lines) → `Engine.lagda.md`, `dict` +
### involution modules (261-416)

`diff -u` against `Cat.Logic.Gist.RxDict.lagda.md` shows only prose
and module-path changes. Every identifier present verbatim: the
`logic` module's dictionary — `term-is-cofan`, `coterm-is-fan`,
`var-is-center`, `covar-is-center`, `term-op`, `coterm-op`
(`RxDict.lagda.md:122-144`) → `Engine.lagda.md:269-285`;
`act-fiberwise`, `coact-fiberwise`, `act-axiom`, `coact-axiom`
(`RxDict.lagda.md:160-178`) → `Engine.lagda.md:294-304`; `module
hand⁻`/`hand⁺` with `coslice`/`slice`, `coslice-fibration`/
`slice-fibration`, `F`, `push-is-comp`, `lift-is-witness`,
`pull-is-comp` (`RxDict.lagda.md:199-274`) →
`Engine.lagda.md:316-370`; the involution facts `act-op`, `coact-op`,
`swap-arg`, `swap-arg⁻`, `swap-judgment`, `swap-invol`,
`reflect-op`, `composite-op` (`RxDict.lagda.md:299-336`) →
`Engine.lagda.md:390-416`.

Minor gap: `graph-op` (`RxDict.lagda.md:288-289`, `Lᵒ.graph ≡
rx.op L.graph`) is not restated by name in `Engine.lagda.md`, though
the underlying fact is available via the imported `op-rxgraph`
(`Graph.lagda.md:43-46`) — functionally covered, not spelled out.

**Verdict: COVERED BY OVERLAP with Cat.Logic**
(`Cat.Logic.Gist.RxDict`, vendored entire into `Engine`, per
`CHANGELOG.md:15-16`).

### `Gist/ThunkableSquare.lagda.md` (363 lines) → `Tower.lagda.md`
### (coherence-square section, 226-259) + `Circle/Model.lagda.md`
### (46-199) + `Circle/Thunkable.lagda.md` (39-124)

`diff -u` against `Cat.Logic.Gist.ThunkableSquare.lagda.md` shows
only the `readback` field addition to the circle model (new content)
and minor telescope-explicitization, no removed content.
`module coherence` — `compat`, `coherent`, `thunkable-is-prop`,
`compat-over-sets` (`ThunkableSquare.lagda.md:69-96`) is present
verbatim (same names, same proof terms) in the general theory at
`Tower.lagda.md:236-258` (the "coherence square of a thunkability
witness" section). `module circle` — `rf`, `model`, `stable`, `C⁺`,
`C⁻`, `tier⁻`, `tier⁺` (`ThunkableSquare.lagda.md:108-249`) → present
verbatim in `Circle/Model.lagda.md:46-199`. The two-witness argument
— `T₀`, `shift`, `T₁`, `thunkable-not-prop`, `associates-not-prop`,
`assoc⁺-base`, `T₀-coherent`, `rot-natural`, `shift-coherent`,
`T₁-coherent`, `coherent-not-prop`
(`ThunkableSquare.lagda.md:262-348`) → present verbatim in
`Circle/Thunkable.lagda.md:44-124`.

Gap: `D : is-deductive-system model`
(`ThunkableSquare.lagda.md:244-249`) — the record-bundling gap.

**Verdict: COVERED BY OVERLAP with Cat.Logic**
(`Cat.Logic.Gist.ThunkableSquare`, vendored into the general theory
for `compat`/`coherent` and into `Circle.Model`/`Circle.Thunkable`
for the circle carrier and witness rows, per `CHANGELOG.md:33-36`),
minus the record-bundling gap.

### `Gist/ReadbackTorsor.lagda.md` (70 lines) → `Circle/Torsor.lagda.md`
### (36-67)

`diff -u` against `Cat.Logic.Gist.ReadbackTorsor.lagda.md` shows only
module-path renames — zero semantic difference. Every identifier
present verbatim: `rb₀`, `rb₁`, `readback-not-prop`, `torsor`
(`ReadbackTorsor.lagda.md:40-70`) → `Circle/Torsor.lagda.md:37-67`
(identical proof terms, restated against `readback-of` instead of
the inlined `eval (reflect f) ≡ f` — same type, definitionally).

**Verdict: FULLY VENDORED** — `Cat.Logic.Gist.ReadbackTorsor`
vendored entire into `Circle.Torsor`, per `CHANGELOG.md:37-38`, and
the WDS↔Cat.Logic diff is empty of content.

---

## Live-dependency check

The task's literal command:

```
rg -n "open import Bb\.WeakDeductiveSystem|import Bb\.WeakDeductiveSystem" --type agda src/ 2>/dev/null | grep -v "^src/Bb/WeakDeductiveSystem/"
```

returns **zero output**. This is not evidence of zero dependents: `rg
--type agda` covers only `*.agda`/`*.lagda`, and every file in this
repository uses the `*.lagda.md` extension, which that type filter
excludes entirely. Per the standing rule against negative-search
claims from a truncated search, the command was re-run without the
type filter, restricted to genuine import lines
(`^\s*(open )?import Bb\.WeakDeductiveSystem`):

```
src/Test/SpikeMediationWild.lagda.md:52,53
src/Test/SpikeSelfMediation.lagda.md:43,44
src/Test/SpikeNaturalTier.lagda.md:53,54,55,56
src/Test/SpikeNaturalTruncation.lagda.md:62,63
src/Test/SpikeEdgeCoherence.lagda.md:43,44
src/Test/SpikeNaturalModuli.lagda.md:48,49
src/Test/SpikeCandidateGenerator.lagda.md:50,51
src/Test/SpikeFramedShape.lagda.md:48,49
src/Test/SpikeGluingCharacteristic.lagda.md:46
src/Test/SpikeGradeSelector.lagda.md:48,49
src/Bb/index.lagda.md:168-183 (sixteen imports)
```

Fifteen import lines across nine `Test/Spike*.lagda.md` files —
expected and known; `Test.*` is gate-exempt per the namespace table
in the root `CLAUDE.md`. The other sixteen are `src/Bb/index.lagda.md`
importing every module of the tree, which is the archive's own
required umbrella index (`src/Bb/CLAUDE.md`, "One index over the
namespace") — not an external live dependency, and itself inside the
`Bb.*` archive namespace, not `Cat.*`/`Core.*`/`Data.*`/`HData.*`/
`Lib.*`.

A broader unrestricted search for the bare string
`WeakDeductiveSystem` (`rg -n "WeakDeductiveSystem" src/`) turns up
additional hits, all prose, not code: `src/Bb/OneTwist/Models.lagda.md`
mentions `Gist.FramedCut`/`Gist.FramedGroup` in its opening prose
(lines 3-4) but contains no `import` statement naming
`Bb.WeakDeductiveSystem` anywhere in the file — confirmed by direct
read and by the restricted-pattern search above returning no hit for
it. The remaining hits are README/CHANGELOG/TODO/gloss prose in
`Bb/VgCategoryShape`, `Bb/NaiveVirtualGraph`, `Bb/OneTwist`,
`Bb/CatsWithExplicitInterchange`, `Cat/Logic/{TODO,gloss,lemmata}.md`,
and `docs/gloss.md` — provenance narration, not `open import`.

**Conclusion: no live code (`Cat.*`, `Core.*`, `Data.*`, `HData.*`,
`Lib.*`) and no other `Bb.*` tree imports `Bb.WeakDeductiveSystem`.**
The only import-level dependents are `Test/Spike*.lagda.md` files
(gate-exempt, expected) and the archive's own `Bb/index.lagda.md`
(expected, itself archival).

## `Bb/index.lagda.md`

Still imports the tree in full: sixteen `import
Bb.WeakDeductiveSystem.*` lines at `src/Bb/index.lagda.md:168-183`,
one per module. Retiring the tree (were that ever proposed) would
require removing this block; nothing else in the umbrella index
depends on it.

---

## Summary verdict

Every one of the sixteen `.lagda.md` files in
`src/Bb/WeakDeductiveSystem/` has its content present in
`Bb.VirtualGraphs`, either through the CHANGELOG's explicit six-file
citation (all six: **FULLY VENDORED**) or through content overlap
with the same-named `Cat.Logic`/`Cat.Logic.Gist` module that
`Bb.WeakDeductiveSystem` is the pre-cut ancestor of, and which the
CHANGELOG documents vendoring "entire" into `Bb.VirtualGraphs` under
its own citation line (the other ten: nine **COVERED BY OVERLAP with
Cat.Logic**, one — `ReadbackTorsor` — close enough to its `Cat.Logic`
twin, with a byte-for-byte-empty content diff, to call **FULLY
VENDORED** outright). No file is genuinely unvendored. No file
shows a gap beyond the one systematic, deliberate architectural
omission repeated tree-wide: the four record-bundling constructions
(`is-invertible`, `is-composable`, `is-deductive-system`,
`deductive-system`, with `opᴰ`/`opᴰ-invol`/the combined `op-axioms`/
`op-composable`) are never restated as records anywhere in
`Bb.VirtualGraphs`; every theorem those records would bundle is
present individually. One minor naming-level (not content) gap:
`RxDict`'s `graph-op` fact is not restated by name in `Engine`,
though the equivalent fact (`op-rxgraph`) is imported and available.

The `Bb.VirtualGraphs.CHANGELOG.md`'s six-file citation for this tree
is real but narrow — it names only the modules that have no live
`Cat.Logic` successor to carry them in via the tree's other, larger
Cat.Logic-sourced vendoring pass. Read alongside that larger pass,
the CHANGELOG's account of this tree's coverage is accurate and
complete, not overstated.

No live code depends on `Bb.WeakDeductiveSystem` outside its own
tree, `Test/`, and the archive's own umbrella index. The tree remains
imported in full by `Bb/index.lagda.md` (sixteen lines,
`src/Bb/index.lagda.md:168-183`).
