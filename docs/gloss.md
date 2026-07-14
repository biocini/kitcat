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

## 1. The representable core (category)

**T1 — Representability presents a category.** The five axioms
(`compose-contr`, `interchange`, `post-eval`, `unit-eqvl`,
`unit-eqvr`) over `category-structure` derive every unit and
associativity law: `_⨾_`, `unitl`, `unitr`, `absorb-l/r`, `idem`,
`emb-idn-absorb`, `emb-image-contr`, `unit-is-prop`,
`is-representable-prop`.
✅ `Cat.Type` (2026-07-09/10).

**T2 — Coupling provenance.** Idempotency and composition
extraction are derivable from `compose-contr` + `interchange` +
`post-eval` alone, never touching the unit equivalences
(hypothesis-explicit lemmas `*-from-coupling`; the signatures are
the minimality theorems).
✅ `Cat.Type` (2026-07-09).

**T3 — The eval axiom is self-mirror.** `pre f (idn y)` and
`post f (idn x)` are the same doubly-centered term; the eval field
is its own mirror (bias = chirality, not asymmetry).
✅ `Cat.Type` (regression witness), `Cat.Codep.Op`
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
`category` (copattern components; `is-prop→PathP` only on
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
🧪 `Gloss.EightFieldWall` (the irreducible-obligation display in
"The double-opposite obstruction"; also the definitional-center
opposite-axioms/discharge verifications).

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
`category-axioms` derives the coherence cells: every candidate is
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
self-dual). Kelly's derivations are naturality-plus-cancellation
arguments — three distinct moves, per the audited source: the
K-stripping principle (Thm 7 only), direct iso-cancellation
(Thm 6), and the naturality of c (Thms 8–10) — foreclosed by
untruncated homs. Regularity does not pin them: faithfulness is a
property of `emb` (twist-invariant, h-level 1); the cells are
twist-variant (h-level 2).
📐 (2026-07-11, bimodule memo; ⚠️ lifted 2026-07-13 under the
audit-keyed rule — `resources/kelly-maclane-conditions` vendored
and statement-audited 46/46, the source-identification now
SOURCE-CHECKED at its anchors; the wild-foreclosure claim remains
📐, kitcat's own argument).

**T16 — The Melliès convergence.** kitcat's `op`/`op-invol` is
Melliès' `(−)op` involution in his "involutive 2-category" reading
of Cat;
`op-coherent`'s θ-bridge structure is the chiral-functor filler
`F̃` (invertible, not identity). At the category core the chirality
presentation is optional (T10 = the strict-chirality warm-up); at
the coherence level it is forced (T12 forbids the strict filler).
The tautological chirality `(C, op C)` is fully definitional
BECAUSE of Route-B (`op-comp-eq = refl` ⇒ `star-comp = refl`).
📐 design-level identification against the paper
(2026-07-11, chirality memo); backed by
`resources/mellies-dialogue-chiralities`, whose statement audit
covers the identification (the involutive-2-category reading and
Theorem 3 verified at their anchors, 2026-07-13; the audit also
corrected this entry's notation — the source writes `(−)op`, not
`†`).

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

**T21 — extract-agree is independent of the faithful stratum.**
Over the three-layer faithful stratum (Petrakis fam/cofam
substrate; Π-integral codep-structure; representability overlay),
the `extract-agree` field
(`compose-contr f g .center .fst ≡ f ⨾ᵇ g`) is not derivable from
the remaining fields: the collapsed-context countermodel
(`ob = ⊤`, `hom = Bool`, `⨾ᵇ = xor`, `fam = cofam = ⊤`,
`res = Bool`, `emb = const`) fills every other field while
extract-agree fails at `(false, true)`. The refutation survives
any future base unit/associativity laws for `⨾ᵇ` ((Bool, xor,
false) is a group) and kills derivations at all levels (everything
at `0ℓ`, so a polymorphic derivation would specialize). The
⨾ᵇ-level composition law `F · (g ⨾ᵇ h) ≡ (F · g) · h` is
derivable extract-agree-free and emb-free (`·-comp-base`); only
⨾-functoriality costs the bridge. The honest boundary, in three
clauses: (i) the machine-checked kill covers the admissible weaker
space — in the model `emb` is an equivalence, so every
fiber-representability strengthening holds (`all-repr`,
`idn-repr-holds`), the fam side is pointed (`fam-pt`), and
untruncated ◃/▹ orbit surjectivity holds (`orbit-surj`,
`orbit-surj-cofam`) — and the weakening class {extract-agree;
emb-hom `emb (f ⨾ᵇ g) ≡ emb f · g`; extract-agree-emb
`emb (f ⨾ g) ≡ emb (f ⨾ᵇ g)`} is equivalent over `compose-contr`,
so the one countermodel refutes all three (`no-EH`/`no-EE`).
(ii) Base-style DECODING structures — a `ctr` with its evaluation
equations — are outside the refuted space BY DESIGN: they derive
the bridge because they ARE the bridge in a different wrapper;
that is `Cat.Type`'s own route (`pre-comp`), not a gap in
the kill. (iii) The bimodule-faithfulness /
two-sided-representability candidate class (action-faithfulness;
the itc2/ccL two-sidedness imports) fails in the model and is
excluded only by argument plus the two walled derivation routes —
its countermodel-grade upgrade is registered, designed, unbuilt.
Consequence: the faithful stratum's abstract propositional-strata
count is three BY THEOREM.
🧪 `Gloss.ExtractAgreeIndependence` (2026-07-13).

## 6. The faithful stratum

The three-layer stratum — Petrakis fam/cofam substrate, Π-integral
codep-structure, representability overlay — from the
faithful-stratum arc. Prior entries: T14/T17 (identifications),
T21 (extract-agree independence, with the records' definition).

**T22 — The tautological filling recovers the representable core
definitionally.** Every category tautologically fills the
three-layer faithful stratum (T21's records):
`fam y = Σ v , hom y v`, `cofam x = Σ w , hom w x`, actions by
`pre`/`post`, `⨾ᵇ := ⨾` (the extracted center — no raw data
survives at the instance),
`res γ = hom (γ .fst .fst) (γ .snd .fst)`. The filling is
definitional at every operation: res-invariance is accepted as the
identity function, the four codep laws as `refl` (their PathP
families are definitionally constant), `extract-agree` as `refl`,
the stratum's fixed-endpoint action recovers the frozen Base
action `_·_` by `refl` (`killcheck-dot`), and interchange-1 is
definitional
(`killcheck-itc1`). Function-valued res-invariance is load-bearing
for the operation-level recovery: the path-valued form recovers
the action only propositionally, since `transport refl` is not
definitionally the identity. At the filling, two of the abstract
stratum's three propositional strata (T21) definitionalize —
res-invariance and extract-agree; the interchange stratum remains
propositional.
🧪 `Gloss.TautologicalFilling` (2026-07-13).

**T23 — Agreement ⟺ interchange-2 over the two-sided stratum;
both walled from the fields.** Over the abstract faithful stratum
with two-sided representability (the right field `compose-contr`
plus a hypothesis-explicit left contractibility `ccL`),
extraction-agreement (`f ⨾ g ≡ f ⨾L g`) and interchange-2
(`emb f · g ≡ f ⟩ emb g`) are inter-derivable — one `pcom` upward,
a one-fiber transport downward — so the two-sided route to
interchange is exactly circular (the constructive sharpening of
T14's circularity trace). Neither side was derived from the
stratum + ccL alone: both pre-registered routes wall at the same
pointwise bridge,
`res-inv-r g … (emb f …) ≡ res-inv-l f … (emb g …)` at `res γ`,
frozen as verbatim refl-probe residues. The representability
fields are twist-blind (`is-contr` is propositional,
`cc-τ-blind`), and the stratum's field inventory has no slot of
interchange's type, so a T5-style twist has nothing to deform. At
the tautological filling the interchange-2 statement is
term-for-term the base category's `interchange` (`itc2-taut`,
machine-checked in T22's certificate): the coherence cells are
intrinsic to wild two-sidedness, not artifacts of the
representable presentation. The wall's `⨾ᵇ`-shaped twin is
independent by theorem (T21); consistent with the T13 trichotomy.
🧪 `Gloss.InterchangeCircularity` (2026-07-13).

**T24 — Conservation of the pentagon engine over the abstract
stratum.** The pentagon engine transplants from
`Cat.Codep.Coherence` to the abstract faithful stratum at +0 extra
bridge steps per face, with res-invariance an opaque field:
`·-comp` closes in two links (a dependent line moving the
extraction gap along `extract-agree`; a `codep₂-r` PathP applied
over the same `fam₂` track), after which the assoc tower,
`reindex-face`/`face₂₃` (reindex family), and
`whisker-face`/`face₁₂` (whisker family) transplant unmodified —
the face proofs are the baseline proofs textually, so the count is
exact, not estimated. The res-invariance cost is confined to
`·-comp`'s interior; the engine is right-action-only. Unchecked
residue: face₄₅ (same reindex family) and face₃₅ untested —
face₃₅'s Coherence lift is `ctr`-dependent, which does not exist
at the stratum, so it plausibly gates on the interchange bridge
(T23); face₁₄'s `homotopy-natural` bridge out of scope.
📐 machine-checked in the tracked spike
`Test.CodepFaithful-20260713-140913 @ dde1f57` (module A3), not
frozen; transplant identity verified line-for-line in the accuracy
review (2026-07-13). The Test/ citation is Lane's granted
exception to the promotion-trigger rule (2026-07-13): the spike is
retained at any future Test/ sweep while this entry stands.

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
entry's **statement audit covers the cited identification** —
fidelity verified against the source, not merely present on disk;
an unaudited entry lifts nothing, and a Lane veto of the entry
re-imposes ⚠️. This is the external mirror of the 🧪↔`Gloss.*`
bijection. (Both lifts to date ran under this rule: T16 on the
chiralities audit, 2026-07-13 morning; T15 on the Kelly audit,
2026-07-13 evening — no ⚠️ source-identifications remain.)
