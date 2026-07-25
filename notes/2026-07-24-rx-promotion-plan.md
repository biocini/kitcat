# Plan — 2026-07-24 — the Rx promotion and the Logic frontend

**Superseded by `docs/composite-rx-refactor/`**, the plan of record.
Retained as the arc's working record. Where the two disagree, the
document set is right: it carries corrected censuses, the rulings
taken since (D2, N1, N2), and reproduction commands for every
measurement. The corrections that would otherwise mislead are
applied below in place.

Promote the reflexive-graph suite into `Core`, discipline the Core
Kan/path machinery against it, elaborate the virtual-graph and
deductive-system machinery on top as a frontend, then rebuild `Cat`.

Evidence status is marked per item. Machine-checked claims name their
certificate module. `2026-07-24-kan-composite-rx-triangulation.md`
carries the survey this plan rests on, the name-level censuses behind
its counts, and the material it does not schedule.

Certificates: `Test.RxTier1` (the backend fits below `Core.Kan`),
`Test.RxVirtual` (virtual-graph and push/pull fit below `Core.Kan`;
the unital boundary), `Test.RxBundle` (bundled versus indexed
inference), `Test.KanIdentities` (the eight Kan/Rx identities).

## Architecture

Dependencies run one way. `Core.Rx` is the backend; `Cat.Logic` is the
frontend. The frontend states its constructions in its own
vocabulary — `ob`, `hom`, `term`, `coterm`, `argument`, `judgment` —
and defines them outright where that reads better than a renaming.

What makes the layering work is not restraint about definitions but
definitional agreement: a virtual graph *is* a reflexive graph with
extra structure, so `term x` and `rx.cofan graph x` elaborate to the
same normal form, `is-composable` and the two fibration conditions
elaborate to the same normal form, and every reflexive-graph theorem
applies to a virtual graph with no bridge and no transport. The
domain vocabulary is free because it costs nothing.

The discipline is therefore about theory, not names.

**Definitions: free, but they must land on the nose.** Write them in
domain terms. The requirement is that a frontend construction reduce
to its backend counterpart definitionally. One that agrees only
propositionally forces a bridge between two constructions, which is
what the library avoids on principle and what this layering exists to
make unnecessary.

**Lemmas: never re-derive what the backend proves.** When the logic
layer needs a fact about fans, cofans, displays, fibrations,
univalence, or the path-object closure, it uses the `Core.Rx` theorem
directly. `is-composable` is `is-cov-fibration` paired with
`is-ctrv-fibration`, so `fibration-is-prop` *is* its propositionality
proof; there is no second proof to write. The same holds for the
agreement of the two variances, the closure calculus over displays,
and the identity-system characterisation.

Two habits follow. Reaching for a lemma: look in `Core.Rx` first.
Writing a definition: confirm it reduces to the `Core.Rx` form, since
that is what keeps the first habit available.

```
Core.Type · Core.Data.Sigma · Core.Base
  ├─ Core.Rx.Type            records
  ├─ Core.Rx.Base            fan/cofan · is-univalent · disp · total
  │                          component · fibrations · to-id · product
  │                          cotensor · comprehension · discrete · hom
  ├─ Core.Kan                theorems stated in Rx vocabulary
  ├─ Core.Transport.*        SinglP-contr IS the fibration proof
  ├─ Core.Equiv · HLevel · IdSys
  ├─ Core.Rx.Transport       to-edge · coproduct · tensor · image
  ├─ Core.Rx.Properties      po · closure calculus · fibration-is-prop
  ├─ Core.Rx.Lens · .Poly · .Fibration
  ├─ Core.Rx.Univalent       (--cubical)
  └─ Cat.Logic.*             virtual-graph · deductive-system · duploids
     └─ Cat.*                rebuilt
```

The cut line is not arbitrary. Reflexive-graph *structure* needs no
Kan operation — no `hcom`, no `transp`, pure interval and Σ — while
the *theory* needs a Kan primitive. Which primitive is the sharper
fact: `is-contr→is-prop` is provable from `transp` alone
(`primTransp (λ i → c .paths x i ≡ y) i0 (c .paths y)`), and only the
composition calculus needs `hcom`, so the strata are three, not two.
The cut falls where it does because `Core.Kan` bundles `transp` with
`hcom`, not because the theory needs a composition. The promotion
makes the library say so.

## Stage 0 — preparation

**0.1** Move `Singl-contr` (from `Core.Transport.Base`),
`Singl-contr-cofan` (from `Core.Groupoid`), and
`prop-inhabited→is-contr` (from `Core.Transport.Properties`) into
`Core.Base`. All three are pure — VERIFIED in `Test.RxTier1`, which
defines them with imports restricted to `Core.Type`, `Core.Base`,
`Core.Data.Sigma`. Today `Cat.Graph.Refl.Properties` imports the first
two from unrelated modules.
*Acceptance:* whole-`Core` check unchanged; `Core.Kan.Total-sys-contr`
becomes `Singl-contr (sys-composite φ s)` — VERIFIED in
`Test.KanIdentities` as `refl`.

**0.2** Lift `fibration-is-prop` out of
`Cat/Graph/Refl/Univalent.lagda.md:70`, where it is `private` and on
`--cubical`. It uses only `Π-is-prop` and `is-contr-is-prop`, nothing
from `ua`. It is the `is-composable` propositionality proof, and leaving
it there would force `deductive-system` onto full cubical.

**0.3** Fix the mis-attributed import at
`Core/Path/Coherence.lagda.md:20` — `is-contr→is-set` and
`total-contr-unique` are `Core.Kan`'s, not `Core.Transport.Base`'s.
Under `-Werror` that warning is fatal independently of the module's
nine holes.

**0.4** Guidelines policy — landed. `docs/guidelines/CLAUDE.md` bans
live-tree references. Consequent chore: 24 sites — 17 `file:line`
citations (`module-anatomy` 10, `definitions-and-proofs` 3, `naming` 2,
`records` 1, `profiling` 1) and 7 dot-paths (`module-anatomy` 3,
`definitions-and-proofs`, `elaboration`, `profiling`,
`prose-and-comments` 1 each) — plus `docs/guidelines/README.md`, which
advertises the banned practice. Abstract them; do not rename through
them. **Do this before Stage 1**, or the sweep and the rename collide
in the same files.

## Stage 1 — backend: `Core.Rx`

VERIFIED (`Test.RxTier1`): a Tier-1 layer — `reflexive-graph`,
`reflexive-graphᴰ`, `fan`/`cofan` with centres, `is-univalent`,
`is-univalent-op`, `op`, `disp`/`total`/`total-op`/`component`,
`is-cov-fibration`/`is-ctrv-fibration` with `push`/`lift`/`pull`/
`colift`, `to-id`, `product`, `cotensor`, `comprehension`,
`binary-product`, `constant`, `discrete`, `codiscrete`, `hom`,
`vfam`/`efam`/`diag`, `is-path-objects`, `is-displayed-univalent` —
compiles on `Core.Type` + `Core.Base` + `Core.Data.Sigma` alone.

**1.1 Rename.** Two external Agda importers (the certificates,
covered by `just mv`); textual references,
three of them in documents the reference sweep does not reach.

**1.2 Split at the cut.** Migrating into `Core.Rx.Transport`:
`rx.to-edge` and `coproduct` (need `transport`), `rx.tensor` (needs
`coproduct`), `rx.univalence.concat`/`inv` (need `_∙_`), `image` and
`is-univalent-family` (need `_≃_`/`aut`). Everything else stays below
`Core.Kan` — including `rx.univalence.to-id`, which needs only
`ap fst`.

**1.3 Amend `2026-07-24-refl-inference-policy.md`** for the migrated
names; it lists `rx.to-edge` by its current home. The guidelines are
*abstracted* under 0.4 rather than renamed.

*Acceptance:* `Core.Kan` imports `Core.Rx.Base` with no cycle;
whole-library check unchanged.

*Open (D1):* whether `Cat.Graph.Refl.Classify` and
`Cat.Graph.Refl.Simplex` promote with the machinery or stay outside
`Core` — they are instances (`U`-small classifiers, augmented
simplices, lists) and pull in `Core.Data.Trunc`, `Core.Data.Bool`,
`Core.Data.Fin.Monotone.*`.

## Stage 2 — Core disciplined by Rx

**2.1 `Core.Composite.SysP` as a displayed graph.** A family
`P : A → Type v` is an `rx.disp (discrete A)` with
`edge x y p a b = PathP (λ i → P (p i)) a b`; `transp` witnesses
`is-cov-fibration`; `SysP.fillerP` is `cov-fibration.lift`. Restore
`LiftP-is-contr`, dropped from the reference port — `SysP` kept
`syslift-center` and lost the contractibility. The proof is
`SinglP-contr`. VERIFIED in `Test.KanIdentities`: `SysLift p a` is the
displayed fan on the nose, and the fibration witness checks.

Highest leverage in this stage: it makes `Core.Kan` and
`Core.Transport` one development, and it is the Core-level worked
instance of the frontend's push/pull.

**2.2 Fan vocabulary in `Core.Kan`.** `Total-sys φ s` becomes
`rx.fan (discrete A) (hcom φ s)` — VERIFIED as `refl`. The uniqueness
lemmas restate as `is-prop` of that fan.

**2.3 Dead-surface sweep in `Core.Kan`.** ~120 lines, no live
consumers: `HSys` (textually identical to `PartialsP`), `sys-path`,
`SysExt`, `sys-lid`, `hc`, `kext`, `TotalP`, `ap-comp-dep`,
`path→square`, `square-sym-h`, `square-sym-v`, `hcom-unique` (46 ms
alone), `hcom-lid-unique`, `com-unique`, `com-lid-unique`,
`hcom-cong`. Move `Chain` to `Core.Path`. Collapse
`sys-composite` — a bare alias for `hcom`, where the plumbing speaks
`hcom` — and
decide `Sys` versus `PartialsP`, which are the same type (VERIFIED).

Staying, contrary to a first reading: `Sys`, `sys-base`,
`sys-filler`, `sys-composite` are used by `Core.Composite` and
`Core.Transport.J`; `conn` by four modules; `contr-face` by
`Core.Coherence.Paths`; `Total-sys` through `Total-sys-contr`'s type.

**2.4 Three representability proofs to one.** `Core.Groupoid.emb` and
`Core.Groupoid.Virtual.repr.emb` are one ternary operation under
different curryings — VERIFIED in `Test.KanIdentities` as `refl`;
`Core.Path.Composition.Repr` is a third copy. Two full `iso→equiv`
proofs (`emb-equiv` ≈60 lines, `repr.emb-equiv` ≈50) for one
operation, and `Core.Groupoid.Virtual` already carries
`yon-unbiased = repr`, an alias with no consumers. Delete two, keep
one instance. Do not invent a general form — that is `Cat.Logic`'s
`hom≃total-representable`.

*Acceptance:* `just profile Core.Kan` within or below the measured
1,025–1,072 ms band;
whole-library check unchanged.

**2.5 Displaced composition, partial.** Twenty names across `Core.Kan`
and `Core.Path.Base`.

Deletable now: `comp-pathp` alone. The six names this note first
listed alongside it — `comp-pathp₂-commutes`, `-unitl`, `-over`,
`comp-pathp₁-fill`, `-over`, `pathp-ends` — all have live
`Cat.Depreciated` consumers, and that tree typechecks (59/59 under
`src/Cat`), so deleting them breaks the build. "Live" in the census
excluded `Cat.Depreciated`; it is not a deletion licence while the
deprecated tree is the porting reference.

Held until `Cat.Depreciated` retires in Stage 4: the other nineteen —
under a contract, not a bare hold. Eighteen have no `Core` consumer
at all, so each must answer before Stage 4 whether it has a
theoretical placement in the disciplined `Core`: reformulated over
`SysP` in its principled home if so, deleted with the deprecated tree
if not, and carried on tenure never. The contract is stated at
`docs/composite-rx-refactor/stage-2-discipline.md` §2.5.

Surviving root: `comp-pathp₂` alone, via two uses in
`Core.Path.Exchange` — which is itself imported only by
`Test.DoubleLoopTensor`, so whether anything survives is a decision
about that module, not arithmetic. The family is ~430 lines and
≈300 ms of `Core.Kan`'s ~1,050 ms.

The full census is in the triangulation survey; the corrected
per-name table is in `docs/composite-rx-refactor/evidence.md`.

## Stage 3 — frontend: `Cat.Logic`

**3.1 `virtual-graph`, bundled.** A field carrying the reflexive
graph, plus `emb`. Ruled (Lane, 2026-07-24): bundled, with the domain
names re-exported.

Bundling costs inference. VERIFIED in `Test.RxBundle`: a display-keyed
signature recovers the graph when the graph is a parameter and fails
with unsolved metavariables when it is a field, the projection
`vg-bundled.graph ?V` being stuck.
Mitigation: key the frontend off a module parametrized by the virtual
graph, as the backend interface is parametrized by its graph. Cross-
module signatures then name the structure, which is already the ruled
convention for family-keyed signatures.

Re-export minding the clash — opening the backend interface wholesale
re-imports the graph's own fields:

```agda
open reflexive-graph graph public renaming (vtx to ob; edge to hom; rx to idn)
open rx graph public using (cofan; fan; cofan-center; fan-center)
  renaming (cofan to term; fan to coterm; cofan-center to var; fan-center to covar)
```

Note the inversion: terms are the cofan, coterms the fan. The
condition that fans are propositions is therefore the condition on
coterms, and the backend theorem that the two variances coincide is a
cross-hand fact the record would otherwise assert.

**3.2 Retarget `Cat.Logic.Type`** (115 lines). It re-implements four
backend names: `term` is `rx.cofan`, `coterm` is `rx.fan`, `var` is
`cofan-center`, `covar` is `fan-center`. Its `reflect`, `judgment`,
`argument`, `conclusion`, `is-representable = fiber reflect` and
`hom≃total-representable` are legitimate frontend additions. Cheap
only while the module is small.

**3.3 `is-deductive-system`, fields in dependency order.**

| tier | statement | is-prop | cost |
| --- | --- | --- | --- |
| `is-composable` | both fibration conditions at the term and coterm displays | 0.2 | free |
| `is-unital` | emb-action, per hand: two equivalences and idempotence | O1 | real work |
| `is-stable` | contractibility of the flank-restriction fiber | `is-contr-is-prop` | free |

The order is forced. The unit coherences are associator-shaped, so
they mention the composition operation, which is the composability
tier's projected fiber centre.

Boundary, VERIFIED in `Test.RxVirtual`: push and pull are definable
from `emb` alone, but packaging terms and coterms as displayed
*reflexive* graphs — which is what buys `total`, `component`, and
`total-path-object` — requires the unit laws, since the displayed
reflexivity field is exactly `emb (rx x) w u x (rx x) ≡ u`, per hand.
The backend closure calculus comes online on the unital side only.

**3.4 O1.** Not discharged by `2025-06-03-coherent-unit-gist.md`:
`idem-equiv→contr-idn` takes `has-lunit-coh` and `has-runit-coh` as
hypotheses, while O1 requires propositionality over the graph and
composability tier only. Work is (i) transposition to the emb-action
forms — the gist's `is-iso` is stated over the composition-action,
which the unit tier excludes on stability-circularity grounds,
(ii) derivation of the coherences from per-hand associativity plus
`idem` (CONJECTURED — inspection-level), (iii) the round trips for
`is-coherent-unit ≃ is-idem-equiv`, of which the gist has both maps
and neither composite. VERIFIED: `Core.Kan.cone` is the gist's `ι` on
the nose, so the fiber-centre construction needs no new Kan machinery.

**3.5 `is-deductive-system-is-prop`** — `Σ-is-prop` twice over 0.2,
O1, and `is-contr-is-prop`. Available helpers: `is-contr-is-prop` and
`is-prop-is-prop` (`Core.Transport.Properties`), `Π-is-prop`,
`Σ-is-prop`, `is-prop-equiv` (`Core.HLevel.Base`), `is-equiv-is-prop`
(`Core.Equiv.Properties`).

**3.6 `deductive-system`** bundle.

**3.7 `Cat.Logic.Univalent`** on `--cubical`, by the segmentation
rule: the record's propositionality collapses identity of deductive
systems to identity of virtual graphs, and the reflexive-graph half
needs `ua` (`Cat.Graph.Refl.Univalent` today).

Then the roadmap-0–7 content: the two-handed calculus, the
associahedron towers, mediation, duploids.

## Stage 4 — rebuild `Cat`

The deprecated tree (49 modules, 15,545 lines) ported onto the
deductive system. Its retirement releases the five remaining displaced-
composition names held back in Stage 2.

## Stage 5 — Core coherence

`Core/Coherence/Paths.lagda.md` (4 holes) and
`Core/Path/Coherence.lagda.md` (9 holes) currently fail. Both attack
Mac Lane coherence by explicit cube-filling, from two routes —
`HComposite` contractibility and the `E₃` representable fiber. The
deductive-system route is paths in contractible iterated fibers.
`Core.Coherence.Base` already isolates the right engine
(`coh-project`, `coh-project₃`, `coh-project-glued`) and typechecks.

Core cannot import the frontend, so Core takes the *shape*, not the
import: coherence stated over the backend's contractibility calculus
at the discrete instance, with the frontend's general theorem as the
validated template. That accepts duplicated proof for a single shape.
The alternative — descending `emb` into the backend so Core imports
the general result — is open (see below).

Collapse the displaced-composition residue — `comp-pathp₁`,
`comp-pathp₂`, `comp-pathp₂-assoc`, `comp-pathp₂-map` — onto `SysP`
here, once the shape is fixed.

## Open decisions

- **D1** — Stage 1 scope: do the classifier and simplex instances
  promote with the machinery, stay in `Cat`, or move to `Lib`?
- **D2** — RULED (Lane, 2026-07-24): the backend. The library
  develops the latent virtual-graph theory of the cubical machinery,
  part of `Core.Composite`'s meaning, so `emb` and its
  representability theory descend and Stage 5 imports the general
  result. Stage 2.4 accordingly mints the general form rather than
  keeping a preferred duplicate.
- **D3** — `emb` field shape: curried, matching what Core has, or
  uncurried through the judgment type, matching the frontend's current
  draft. Uncurried makes representability a one-liner and the double
  domain-collapse direct. Affects 3.1.
- **D4** — is O1 in scope for this arc, or does 3.5 ship with the unit
  tier's propositionality stated as an obligation?
- **D5** — does anything in the deprecated tree survive rather than
  being ported? Weakens the Stage-2 deferral if so.
- **R1** (carried) — the lax variant's name, needed at the monoidal
  re-stratification.

## Evidence

VERIFIED, by certificate module: `Test.RxTier1`, `Test.RxVirtual`,
`Test.RxBundle`, `Test.KanIdentities`. The claims each carries are
named at the sites above; `Core.Kan.cone` against the gist's `ι` is a
typing checked in session, not yet a certificate — it lands with the
O1 item.

Measured 2026-07-24: 137 of 139 `Core` modules typecheck, the two
failures being the coherence modules; **59 of 59 under `src/Cat`
typecheck, `Cat.Depreciated` included** — 49 modules, 15,545 lines,
and green, which is why the deletion schedule holds what it holds;
`Core.Kan` elaborates cold in 1,025–1,072 ms across runs (treat ±50 ms
as noise) with the displaced-composition family at ≈300 ms;
`Cat.Graph.Refl` has two external Agda importers, `Test.KanIdentities`
and `Test.RxBundle` (the certificates), plus textual references in
`bin/profile`, `docs/guidelines/`, and these notes.

CONJECTURED, flagged in place: that the unit coherences follow from
per-hand associativity plus idempotence; that the h-level development
restates over the backend.
