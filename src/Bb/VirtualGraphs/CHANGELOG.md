# Changelog — Bb.VirtualGraphs

Every alteration and addition to this tree after it entered the
archive. **Newest entry first.** The tree is frozen green, so an
entry names the checker run that says so.

---

## 2026-08-05 — stability, as prose, follows the identifier

**Sixteen files, `verified`.** The naming pass two entries below
renamed the identifier (`is-stable` → `reflect-is-embedding`,
`Stability` → `Embedding`); this entry catches up the prose that
still said "stability"/"stable" as an informal description of the
same condition. `Cancellation`, `Display`, `Engine`, `Diagonal`,
`Embedding`, `Framing`, `Interchange`, `Pentagon`, `Readback`,
`Tower`, `Bool.Readers`, `Bool.Klein`, `Circle.Model`,
`Circle.Polarity`, `Circle.Thunkable`, `Circle.Shift`, and
`Group.Abelian` are reworded: "stability" becomes "the embedding
condition," "stable" as an adjective becomes a plain statement that
reflection is (or yields) an embedding, per sentence. Local
bindings named `stable` (a witness of `reflect-is-embedding` at a
model, e.g. `Diagonal.pinned.stable`, `Circle.Model.circle.stable`,
`Group.Abelian.framed.stable`) are untouched — informal local
names, not the audited identifier. Generic "twist" as an ordinary
descriptive word is untouched throughout the tree: unlike
"stability," it does not import a specific established concept the
corpus fails to earn, so purging it was not warranted by the same
reasoning.

**State, `verified`.** `gtimeout 280 just check-tree
src/Bb/VirtualGraphs`: 30 of 30 modules typecheck. `just lint
changed`: all checks passed.

---

## 2026-08-05 — the negative pentagon, through the opposite

**Three modules, `verified`.** The pentagon now holds for both
hands. The negative one is the positive theorem read at `opⱽ G`,
not a second path argument.

`Embedding.lagda.md` gains `reflect-lc-fiber`. Two representations
`u v` of one judgment name a path of edges twice — cancel
`reflect` across `u .snd ∙ sym (v .snd)`, or project the fiber's
own `S α u v` — and the lemma identifies the two. `tower⁺` and
`tower⁻` build their associators along those two routes
respectively, so this is what lets either be read as the other.

`Tower.lagda.md` gains `module op-tower`, over the negative hand's
own telescope: `corx`, the embedding condition, the negative cut.
It instantiates `tower⁺` at `opⱽ G` through `op-embedding` and
`duality.op-composable⁺`, and proves two correspondences —
`op-⨾⁺`, that the opposite's positive cut is the negative cut with
its factors exchanged, definitionally; and `op-assoc⁺ f g h :
op.assoc⁺ h g f ≡ sym (assoc⁻ f g h)`. A positive-hand
construction over `tower⁺` transports to the negative hand along
these two.

`Pentagon.lagda.md` gains `module pentagon⁻`, mirroring
`pentagon⁺`'s telescope over `tower⁻`. The proof reads
`pentagon⁺` at `opⱽ G` with the four factors reversed, rewrites
each of the five sides by `op-assoc⁺`, then turns the identity
around with `sym-distr` and reassociates the right leg.
`Core.Groupoid` is a new import there, for `sym-distr` alone.

**State, `verified`.** `gtimeout 300 just check` on
`Bb.VirtualGraphs.Embedding`, `.Tower`, and `.Pentagon`: exit 0
each. `gtimeout 900 just check-tree src/Bb/VirtualGraphs`: 30 of
30 modules typecheck. `just check Bb.index`: exit 0.

---

## 2026-08-05 — a naming pass, against the audit at
`outputs/virtual-graphs-naming-audit.md`

**Renames, `verified`.** Five names conflicted with established
category-theory usage badly enough that a reader taking them at
face value would assume theorems the corpus does not earn. All
five are corrected, source-wide within this tree.

- `twist⁻`/`twist⁺` → `rx`/`corx`, everywhere. Neither carries a
  ribbon-twist or naturality claim; `rx` continues
  `Bb.VgCategoryShape`'s own name for the same role.
- `Balanced.lagda.md` → `Cancellation.lagda.md` (module
  `Bb.VirtualGraphs.Balanced` → `.Cancellation`, internal `module
  balanced` → `module cancellation`). The tree has no tensor and no
  braiding, so "balanced monoidal category" was never statable
  here, and `pair⁺`/`pair⁻` refute the fragment that could be
  stated.
- `is-invertible⁻`/`is-invertible⁺` → `is-absorbing⁻`/
  `is-absorbing⁺`, matching the `absorb⁻`/`absorb⁺` lemmas already
  downstream. The tier gives one-sided absorption, never a
  two-sided inverse.
- `Stability.lagda.md` → `Embedding.lagda.md` (module
  `Bb.VirtualGraphs.Stability` → `.Embedding`), `is-stable` →
  `reflect-is-embedding`, and every derived name along with it
  (`op-embedding`, `embedding-from-injective`,
  `embedding-from-hom-sets`, `embedding-from-contr-cut⁻`,
  `contr-from-embedding`, `reflect-is-embedding-unfolds`). The
  predicate is definitionally `is-embedding reflect`; the old name
  borrowed the least related sense of the single most overloaded
  adjective available.
- `is-interchanging` → `cuts-agree`, `full-interchange` →
  `full-cuts-agree`, `judgment-interchange` → `judgment-cuts-agree`,
  `interchange→involutive` → `cuts-agree→involutive`. None of these
  states the 2-categorical interchange law; all state that the two
  hands' compositions agree. `Aligned.lagda.md`'s own bare
  `interchange` theorem is renamed `hands-agree`, kept distinct from
  `Interchange`'s judgment-level `cuts-agree` to avoid a scope
  clash between the two.
- `Aligned.lagda.md` → `Diagonal.lagda.md` (module
  `Bb.VirtualGraphs.Aligned` → `.Diagonal`, internal `module
  aligned` → `module diagonal`). The old name stated the hypothesis
  (readback aligned with the chosen edge); the new one states what
  distinguishes the module — the diagonal framing `rx = corx`, the
  condition under which the two-hand theory collapses to one
  category. `Diagonal.lagda.md`'s opening paragraph now says so
  outright.

One correctness bug surfaced during the pass, independent of
naming philosophy: `Groupoid/Path.lagda.md` and
`Group/Abelian.lagda.md` both named each cut for the twist it
mediates with, inverting this tree's own rule (`Framing.lagda.md`:
the positive cut mediates with the negative twist). Both are
corrected — `Group/Abelian.lagda.md`'s fix also required swapping
`cut⁻-is-twisted`/`cut⁺-is-twisted`, which had baked in the old,
inverted correspondence.

"Invertibility" and "invertible" as descriptive prose (not just the
renamed identifiers) are swept to "absorption"/"absorbing"
throughout, for the same reason as the identifier rename. The
opening paragraphs of `Cancellation`, `Diagonal`, `Circle.Model`,
`Polarity`, `Presentation`, `Bool.Readers`, `Bool.Heap`, and this
tree's own `README.md` are reworded to drop "balanced" and
"aligned" as descriptive words, not only as identifiers. Prose use
of "stability"/"stable" and generic "twist" as informal descriptive
words (distinct from the renamed identifiers) is not swept in this
pass — it is widespread enough to be its own undertaking, and is
left as an open question rather than decided silently.

**State, `verified`.** `gtimeout 280 just check-tree
src/Bb/VirtualGraphs`: 30 of 30 modules typecheck, run repeatedly
through the pass and finally after it landed.

---

## 2026-08-04 — a TODO.md, and the Aligned prose names its destination

**Documents.** `Aligned.lagda.md`'s opening paragraph stated the
diagonal-framing construction and its theorems but never named
what they add up to. Added one sentence: interchange collapses the
two hands to one composition, so the graph carries an ordinary
category. `TODO.md` is new, four open items general enough to
outlive the live definition's current shape — a literature pass on
one-sided unitality, and three literature-vendoring tasks. This
tree is the one exception to the namespace's no-open-item-list
rule (`src/Bb/CLAUDE.md`), since it is the live consolidation
target rather than a frozen stratum.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.Aligned`: exit 0.

---

## 2026-08-04 — the parity origins share one reflection

**Bool.Heap, `verified`.** `Bb.VgCategoryShape.Parity`'s
`same-reflection` (`Parity.lagda.md:183-187`) compared
`heap false .reflect` against `heap true .reflect`, two separately
bundled record instances. Here the redundancy the old lemma closed
never opens: `HB` is the one graph both `at false` and `at true`
align, so what `same-reflection` proved by `refl` is definitional,
not a separate theorem. The module prose now says so, at the
aligned-telescope section.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.Bool.Heap`: exit 0.

---

## 2026-08-04 — the engine, the unit shape, and the models

**Sixteen modules, `verified`.** The chosen-edge theory and the
committed-source model modules landed, closing the
committed-source consolidation. The source ↔ module mapping:

- `Engine` (group H): `Cat.Logic.Gist.ReflectFiber` entire
  (vocabulary, composability with the distribution laws, the
  fiber-contractibility engine, per-hand associativity and unit
  laws) and `Cat.Logic.Gist.RxDict` entire (the reflexive-graph
  dictionary, both hand fibrations, the involution suite), their
  shared inline carrier dissolved into `(G) (idn)`.
- `UnitShape`: the `Bb.NaiveVirtualGraph` unit-identification
  analysis — `Gist.StabilityShape` entire (the datum is a path in a
  hom type; propositionality is a truncation condition, for one
  hand and for the both-hands fiber) and `Gist.SelfUnit`'s
  self-referential datum with its path-groupoid collapse.
- `Word.Carrier`, `Word.Model`, `Word.Defect`, `Word.Polarity`:
  `Cat.Logic.Gist.BalancedWord` (descriptor machinery; the `BW`
  instance, stability, cuts, tiers, winding grade, measurement
  rows), `Cat.Logic.Gist.AssociatesDefect` entire, and the word
  rows of `PolarityHLevel`/`PolarityTwist`/`PolarityCollapse` —
  `Word.Polarity` splits the polarity rows out of §6's
  `Word.Model`.
- `Circle.Model`, `Circle.Thunkable`, `Circle.Polarity`,
  `Circle.Torsor`, `Circle.Shift` (`--cubical`, an import island):
  `Cat.Logic.Gist.ThunkableSquare`'s circle carrier and witness
  rows, `PolarityHLevel`'s circle rows,
  `Cat.Logic.Gist.ReadbackTorsor` entire,
  `Cat.Logic.Gist.ReadbackShift` entire (the retuning rows read as
  one carrier with two readback witnesses).
- `Bool.Klein`: `Bb.OneTwist.Cancel`'s countermodel, run through
  `Extraction`. `Bool.Heap`: `Bb.VgCategoryShape.Parity`, run
  through `Aligned` at each origin. `Bool.Readers`:
  `Bb.WeakDeductiveSystem.Gist.AssociatesCountermodel`'s projection
  and four-reader models plus `Cat.Logic.Gist.BalancedProfile`'s
  `attempt₁`/`attempt₂`.
- `Groupoid.Path`: `Bb.WeakDeductiveSystem.Gist.FramedCut` entire
  plus `Bb.OneTwist.Models`' path model as the one-twist instance.
- `Group.Abelian`: `Bb.WeakDeductiveSystem.Gist.FramedGroup` entire
  (including `univalent→prop` via `rxgraph`) plus
  `Bb.OneTwist.Models`' group model as the one-twist instance.

Skipped as `Test.*`-only, per the committed-source rule: `Monoid`
(SpikePinningMonoid), `Bool.Endo`, `Bool.Sleeve`,
`Word.Mediation`/`Census`/`Recognition`,
`Circle.Natural`/`Mediation`/`Recognition`. Deferred within the
Engine stage, catalogued in the plan §4.12: the remaining
`Bb.NaiveVirtualGraph` rows beyond `UnitShape` (`UnitCanonical`,
`CrossedUnit`, `AbsorbObstruction`, `DeductiveSystem`'s route
suite, `StableFiber`, `ReflexiveVG`, `PerHandUnit`, the
`JudgmentLens`/`TwoSided` displayed-carrier rows). Thirty modules
in the tree.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.<Mod>`: exit 0 for each of the sixteen. No lemma
omitted anywhere. `Bb.index` gained the sixteen imports;
`just check Bb.index`: exit 0. No `--erased-cubical` module imports
the circle island.

**Documents.** `README.md` updated to the thirty-module shape.

---

## 2026-08-04 — the presentation and the reflexive-graph dictionary

**Three modules, `verified`.** `Presentation` is group P, from
`Cat.Logic.Gist.OperatorCarrier` entire: the `presentation` record
dissolved into a flat twelve-parameter telescope, the carrier and
readback as constructions, all four tier fibers inhabited with
forced edges, the `residue` and its hom-set discharge, the balanced
layer satisfying every law (`presented`, with `op-cross` on the
nose), the graph round trip closing outright on the minimal carrier
with `readback-square` as the readback leg's whole obligation, the
operator dictionary, and the presentation round trip (`round`).
`Graph` and `Display` are group X, from `Cat.Logic.Graph` and
`Cat.Logic.Display`: the framing as two reflexive graphs on one
graph, the fan-calculus dictionary, the two-sided base, the argument
families as univalent lenses, the coslice fibration with push the
cut and lift the witness, the cospan reading of interchange, and
`bipush-comp`. Both import the live `Core.Rx.*` — the tree's one
live dependency beyond `Core` basics and the same one
`Bb.WeakDeductiveSystem.Graph`/`.Display` carry. Fourteen modules in
the tree.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.Presentation` / `.Graph` / `.Display`: exit 0 each.
`Bb.index` gained the three imports.

**Documents.** `README.md` rewritten to the fourteen-module shape:
the module map, the consolidation provenance, and the `Core.Rx.*`
live-dependency note.

Next: the model modules (`Word.*`, `Circle.*`, `Bool.*`,
`Groupoid.Path`, `Group.Abelian`), per the extended plan §6.

---

## 2026-08-04 — interchange, the extraction, and the aligned edge

**Three modules, `verified`.** `Interchange` dissolves
`Cat.Logic.Gist.FramedInterchange`'s `framed` record into the frame
theory over readback and two contractible cuts (frame laws,
involutivity forcings, mixed associativity via readback, the
cancellation reduction, the `readable` suite), and adds the
interchange-hypothesis results of
`Bb.WeakDeductiveSystem.Gist.NeutralUnit` and the tortile
transcription of `.Gist.TwistFidelity` over the tower with the pin/K
hypotheses. `Extraction` is group O, from `Bb.OneTwist.Base` and the
general part of `.Cancel`: the negative tier's centre defines the
positive twist, its unit laws come free, and the term-side
cancellation is equivalent to centre agreement. `Aligned` is group
V, from `Bb.VgCategoryShape` entire minus its model: the h-category
theory record-free — readback-route left-cancellability, the unit
package pinning `rx` to the extracted unit, all four unit laws,
interchange and stability as theorems, per-hand associativity, and
the contractibility of the neutral-idempotent type. Eleven modules
in the tree.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.Interchange` / `.Extraction` / `.Aligned`: exit 0
each. `Bb.index` gained the three imports; `just check Bb.index`:
exit 0.

Next: `Presentation` (group P), then `Graph`/`Display` (group X);
the model modules wait for their own pass.

---

## 2026-08-04 — the general theory, groups A through D′

**Seven modules, `verified`.** The committed-source consolidation
landed the general theory in dependency order: `Stability` (group A:
representability, stability, the carrier opposite), `Framing` (group
B split as `framing⁻`/`framing⁺`/`framing` along which twist each
definition reads, with the duality suite), `Tower` (group C:
`tower⁺` over `twist⁻`+S+C⁺ alone, `tower⁻` dually, `tower` with the
mixed word, `associates` and closures, the coherence square,
`collapse⁺/⁻` with the crossed pairing explicit, plus the
`absorption`/`unital` pin-K route), `Pentagon` (over `tower⁺` only),
`Polarity` (definitions, generation, unit-law converses), `Readback`
(group D: hands, near unit laws, residues, stability from the
contractible negative cut), `Balanced` (group D′: centres,
cancellations, far laws, `at-strength`, the polarity collapse).
Sources: `Cat.Logic.Type`/`Base`, `Cat.Logic.Gist.BalancedBase`/
`BalancedProfile`/`ThunkableSquare` (general part)/`PolarityHLevel`/
`PolarityTwist`/`PolarityCollapse`, and
`Bb.WeakDeductiveSystem.Base` for the pin-K route. Eight modules in
the tree.

**State, `verified`.** `gtimeout 300 just check <Mod>`: exit 0 for
each of the seven, in order, after each landing. `Bb.index` gained
the seven imports.

Next: `Interchange`, `Presentation`, `Engine`, `Graph`/`Display`,
`Extraction`, `Aligned`, then the model modules, per the extended
plan (`outputs/.plans/virtual-graphs-vendor.md` §6).

---

## 2026-08-04 — the tree opened with the carrier

**The port, `verified`.** `Type` arrived from `Test.NewDs.Carrier`,
mathematical content unchanged. The module name and the opening
prose changed, nothing else. One module in the tree. `README.md` and
this file opened to the common format of `src/Bb/CLAUDE.md`.
`Bb.index` gained the tree's import.

**State, `verified`.** `just check Bb.VirtualGraphs.Type`: exit 0.
`just check Bb.index`: exit 0.

Next: the tree receives the consolidated virtual-graph results, per
the plan at `outputs/.plans/virtual-graphs-vendor.md`.
