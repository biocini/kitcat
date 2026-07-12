# Gloss — the theorem ledger

A ledger of results proven in and about this development. Each
entry: statement, where it is proven, status, date. Statuses:

- ✅ machine-checked, committed (module cited)
- 🧪 machine-checked evidence module in `Gloss/` (tracked, in
  `All`; self-contained modulo Core; Cat.* definitions frozen at
  the cited commit)
- 📐 established by rigorous argument (countermodel or hand-checked
  path algebra), not mechanized
- ⚠️ partially conjectured — the honest boundary is stated

Keep entries precise and dated. When a 📐 entry gets mechanized,
upgrade it and cite the module. When a ⚠️ boundary moves, say so.

## 1. The representable core (hcategory)

**T1 — Representability presents a category.** The five axioms
(`compose-contr`, `interchange`, `post-eval`, `unit-eqvl`,
`unit-eqvr`) over `hcategory-structure` derive every unit and
associativity law: `_⨾_`, `unitl`, `unitr`, `absorb-l/r`, `idem`,
`emb-idn-absorb`, `emb-image-contr`, `unit-is-prop`,
`is-representable-prop`.
✅ `Cat.Codep.Base` (2026-07-09/10).

**T2 — Coupling provenance.** Idempotency and composition
extraction are derivable from `compose-contr` + `interchange` +
`post-eval` alone, never touching the unit equivalences
(hypothesis-explicit lemmas `*-from-coupling`; the signatures are
the minimality theorems).
✅ `Cat.Codep.Base` (2026-07-09).

**T3 — The eval axiom is self-mirror.** `pre f (idn y)` and
`post f (idn x)` are the same doubly-centered term; the eval field
is its own mirror (bias = chirality, not asymmetry).
✅ `Cat.Codep.Base` (regression witness), `Cat.Codep.Op`
(2026-07-10).

## 2. The coherence tower

**T4 — Unit-free pentagon.** `assoc` and the full Mac Lane
pentagon are derived from `compose-contr`/`emb-comp`/`·-comp`
alone — no unit axiom, no `interchange`. (The associativity
firewall: no unit/coupling axiom can disturb it.)
✅ `Cat.Codep.Coherence` (2026-07-09/10).

**T5 — The three coherence cells.** `absorb-lcoh`, `absorb-rcoh`
(post-eval inner form), and the self-dual `couple-D₀` are
independent of the five axioms: twisting
`interchange' = interchange ∙ τ` by a pointwise loop family
vanishing at the `(idn,idn,idn,idn)` instance preserves all five
axioms and breaks the cells. Carrier for a nontrivial τ: the S²
path groupoid (`π₂(S²) = ℤ`). Pairwise the cells sit at disjoint
interchange loci, so none implies another.
📐 twist argument + carrier sketch (2026-07-10/11); the cells are
fields in ✅ `Cat.Codep.Coherent`.

**T6 — θ-core is a theorem of the cells.** From the three cells,
`θ-core : ap (pre e) (post-eval e) ≡ interchange e e e e ∙
ap (post e) (post-eval e)` is derivable by path algebra
(`θ-core = sym i ∙ L`).
✅ `Cat.Codep.Coherent` (2026-07-11).

**T7 — The identity-argument gauge collapse.** `gauge-r :
absorb-r (idn) ≡ post-eval (idn)` and its mirror `gauge-l` are
derivable from the three cells via the free naturality square
(`homotopy-natural absorb-r (post-eval e)`) plus `couple-D₀` and
`absorb-lcoh`; hence the whole cluster
`{absorb-l e, absorb-r e, post-eval e}` (all of type `D₀ ≡ idn`)
collapses to a single path. No fourth cell.
✅ `Cat.Codep.Coherent` (2026-07-11). History (🧪
`Gloss.TriangleFace23` isolates the bridge): first blocked and
misattributed to T11's countermodel; the gauge is π₁-level and
derivable — the S²/π₃ obstruction lives one dimension up.

**T8 — The Mac Lane triangle.** Weak triangle from the five axioms
alone; full triangle (`ap (_⨾ g) (unitr f) ≡ assoc f (idn) g ∙
ap (f ⨾_) (unitl g)`) from the overlay, with `gauge-r` closing
`face₂₃`; the mirror triangle is the one-line op-instantiation
`triangle-full-tower (op C) (op-coherent A2)`.
✅ `Cat.Codep.Triangle` (2026-07-11).

## 3. Duality

**T9 — The parity theorem.** Under `op` (hom reversal + context
swap): `pre^op = post` and `post^op = pre` DEFINITIONALLY;
`post-eval^op` is literally the base field; `unit-eqvl/r` swap;
`interchange^op = sym ∘ mirror`; `compose-contr^op` transports
along one funext'd interchange. Every mirror axiom is derivable
from the base fields. With the Route-B center,
`f ⨾^op g = g ⨾ f` and `op-comp-eq` hold by `refl`.
✅ `Cat.Codep.Op` (2026-07-10, Route-B 2026-07-11).

**T10 — Strict self-duality of the category core.**
`op-invol : op (op C) ≡ C` as a record path for the 5-field
`hcategory` (copattern components; `is-prop→PathP` only on
`compose-contr`).
✅ `Cat.Codep.Op` (2026-07-10).

**T11 — TEL-independence.** The 3-cell `TEL : bridge-l^B ∙
bridge-r^A ≡ qmove` (the op-invol component for any coherence
cell carried as a field) is independent of the eight fields:
a coherent twist shifting the `absorb-lcoh` field by
`κ ∈ π₃(S²) = ℤ` (a π₀-component change of the 2-cell field)
leaves the base-only transport `qmove` fixed and κ-displaces the
cell-carrying bridge.
📐 countermodel over the S² path groupoid, dimension count
verified (2026-07-11). The `ap(ap E)`-transfer analysis confirms
no derivation route exists (faithful transfer, residue located).
🧪 `Gloss.EightFieldWall` (the Gate-3 `-- WALL:` block; also the
Route-B/discharge verifications).

**T12 — The op-involution regress ("coherence of the dualizing
involution forces truncation of the hom ∞-groupoid").** For wild
homs, no finite tower `(5 fields + cells + TEL-fields to depth k)`
admits a strict op-involution record path: each level's op-invol
component is a `(k+2)`-cell with the bridge/transport asymmetry,
refuted through `π_{k+2}` of a single carrier (S² has nonzero
homotopy in infinitely many degrees). Hom-`n`-truncation would
terminate the tower at `n+1` — the incompatibility is exactly the
wild-homs commitment.
📐⚠️ level 1 is T11 (established); levels `k ≥ 2` are
mechanism-conjectured (the asymmetry provably persists; the
explicit `θ_k` not ground out). Consequence shipped: the coherence
overlay dualizes covariantly (`op-coherent`), with deliberately no
`op-coherent-invol`. NOVELTY CANDIDATE: anticipated in spirit by
the duality-involutions/dagger-higher-categories literature and by
homotopy-fixed-point obstruction theory, but we know no published
statement in this record-level wild form — citation research
pending before any novelty claim in prose.

**T13 — The prop-pinning trichotomy.** No prop-valued predicate on
`hcategory-axioms` derives the coherence cells: every candidate is
(i) τ-blind (all representability props — `emb` is an equivalence
in path-groupoid carriers, so every `fiber emb T` is contractible
in honest and twisted structures alike), (ii)
truncation-impotent (a separating prop exists —
`∥ interchange e⁴ ≡ ι₀ ∥` — but cannot eliminate into the
non-prop cell), or (iii) model-false (`is-contr` of a wild
path/Π-space). Slogan: a proposition cannot canonically select an
element of a wild path-space.
📐⚠️ (i) is airtight (rests on the 🧪 `Gloss.PathGroupoid`
instance); (ii)/(iii) established (🧪 `Gloss.PropPinning`); the
exhaustiveness step is morally complete but not
formalization-grade (2026-07-11).

## 4. Identifications (what the cells ARE)

**T14 — Interchange splits at the substrate.** interchange-1 (the
bimodule interchange on a single composite, `(f ⟩ F) · g ≡
f ⟩ (F · g)`) is definitional — the two actions touch disjoint
context slots. interchange-2 (the record's field, coupling two
embeddings) is, at the tautological filling, exactly the base
category's 4-fold associator on `a ⨾ f ⨾ g ⨾ b`; τ is the wild
base's associator freedom. The two-sided-representability route to
deriving it (extractions of `compose-contr-R/L` agreeing) is
circular.
📐 direct computation + circularity trace (2026-07-11, faithful-
stratum memo).

**T15 — Kelly identification.** The three cells are the
wild-categorical residue of Kelly's unit-coherence theorem: the
left/right action-unit triangles and the centre `λ_I = ρ_I` cell
of a bimodule (couple-D₀ is the op-fixed centre cell — hence
self-dual). Kelly's derivation is a cancellation argument
foreclosed by untruncated homs. Regularity does not pin them:
faithfulness is a property of `emb` (twist-invariant, h-level 1);
the cells are twist-variant (h-level 2).
📐⚠️ (2026-07-11, bimodule memo); the Kelly source-identification is
CONJECTURED until `resources/kelly-mac-lane-coherence` is vendored.

**T16 — The Melliès convergence.** kitcat's `op`/`op-invol` is the
involution `†` of Melliès' "involutive 2-category" reading of Cat;
`op-coherent`'s θ-bridge structure is the chiral-functor filler
`F̃` (invertible, not identity). At the category core the chirality
presentation is optional (T10 = the strict-chirality warm-up); at
the coherence level it is forced (T12 forbids the strict filler).
The tautological chirality `(C, op C)` is fully definitional
BECAUSE of Route-B (`op-comp-eq = refl` ⇒ `star-comp = refl`).
📐 design-level identification against the paper
(2026-07-11, chirality memo); backed by
`resources/mellies-dialogue-chiralities` (PROVISIONAL).

**T17 — Binary-ancestor calibration.** The one-sided ancestor
(`repr : hom ↪ endo-operators`) is the `fam := unit` filling of the
two-sided theory; its known limits are measured costs at that
parameter point — in particular interchange's TYPE degenerates
(interchange is the fam-action's presence), and unit-uniqueness
needs the fam action.
📐 (2026-07-11, faithful-stratum memo).

## 5. Model and instance facts

**T18 — Path groupoids are hcategories with emb an equivalence.**
Over any type `A`: `hom x y := x ≡ y`, `emb f ((w,a),(v,b)) :=
pcom (sym a) f b` discharges all five axioms, and `emb` is a full
equivalence (the context is a product of contractible singletons),
so `compose-contr` is `eqv-fibers`.
🧪 `Gloss.PathGroupoid` (2026-07-10).

**T19 — Prop-hom instances trivialize the cells.** Over
propositional homs, all three overlay cells (and the gauges)
discharge in one line each.
✅ `Cat.Codep.Coherent` (`prop-homs`), walking-arrow instance
(2026-07-11).

**T20 — Conservation of the pentagon plumbing.** Binary
right-nested fiber witnesses are a measured optimum at this
record: pcom-native endpoints cost +5 atoms (whisker faces +2
each); catr-bridges on binary endpoints are impossible (distinct
hcom terms). The tower's witnesses are born by iterated lifting;
ternary-first governs born-ternary compositions.
🧪 `Gloss.PcomConservation` (2026-07-10).

## Standing results from earlier strata (pre-2026-07-10)

- **Squaring effect** (ternary idempotency ⇒ `e² = 1`;
  `K(ℤ/2,1)` counterexample to unit uniqueness) — 📐, historical
  (Cat.Virtual era; motivated the yon-eval/yon-idpt resolution).
- **Monoidal `absorb-coh` independence** (π₀-separation
  countermodel; balanced difference, NOT 2-torsion) — 📐
  (2026-07-0x, `Cat.Monoidal.Coherence` keeps the field).
- **`fiber-pathp` is false in general** (S¹ counterexample) — 📐;
  never use as a lemma.

## Maintenance

Add an entry when a result is proven (or a countermodel
established); upgrade 📐 → ✅ when mechanized; record refutations
and misattributions honestly (see T7's history — walls cited
against the wrong theorem cost time). This file carries the facts.

Every 🧪 marker must name its `Gloss.*` certificate, and every
Gloss module must be named by an entry here — the ledger and the
Gloss namespace are maintained as one unit. Promotion criteria and
the freeze ritual live in CLAUDE.md ("Test → Gloss promotion"):
ledger-linked, not mechanized elsewhere, arc closed; frozen at a
named commit; append-mostly.

Every 📐 source-identification entry names its backing
`resources/<slug>/` entry and is marked ⚠️/CONJECTURED until that
entry exists — the external mirror of the 🧪↔`Gloss.*` bijection.
(T16 → `resources/mellies-dialogue-chiralities`; T15's Kelly
identification stays ⚠️/CONJECTURED until a
`resources/kelly-mac-lane-coherence` entry is vendored.)
