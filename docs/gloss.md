# Gloss: the theorem ledger

A ledger of results proven in and about this development. Each
entry: statement, where it is proven, status, date. Statuses:

- ✅ machine-checked, committed (module cited)
- 🧪 machine-checked evidence module in `Gloss/` (self-contained
  modulo Core, `Cat.*` definitions frozen at the cited commit)
- 📐 established by rigorous argument (countermodel or hand-checked
  path algebra), not mechanized
- ⚠️ partially conjectured, with the honest boundary stated

Keep entries precise and dated. When a 📐 entry gets mechanized,
upgrade it and cite the module. When a ⚠️ boundary moves, say so.

## 1. The representable core (category)

**T1: Representability presents a category.** The five axioms
(`compose-contr`, `interchange`, `post-eval`, `unit-eqvl`,
`unit-eqvr`) over `category-structure` derive every unit and
associativity law. Derived: `_⨾_`, `unitl`, `unitr`, `absorb-l/r`,
`idem`, `emb-idn-absorb`, `emb-image-contr`, `unit-is-prop`,
`is-representable-prop`.

✅ `Cat.Type` (2026-07-09/10).

**T2: Coupling provenance.** Idempotency and composition
extraction are derivable from `compose-contr` + `interchange` +
`post-eval` alone, never touching the unit equivalences
(hypothesis-explicit lemmas `*-from-coupling`, whose signatures are
the minimality theorems).

✅ `Cat.Type` (2026-07-09).

**T3: The eval axiom is self-mirror.** `pre f (idn y)` and
`post f (idn x)` are the same doubly-centered term. The eval field
is its own mirror (bias = chirality, not asymmetry).

✅ `Cat.Type` (regression witness), `Cat.Codep.Op`
(2026-07-10).

## 2. The coherence tower

**T4: Unit-free pentagon.** `assoc` and the full Mac Lane
pentagon derive from `compose-contr`/`emb-comp`/`·-comp` alone: no
unit axiom, no `interchange`. (The associativity firewall: no
unit/coupling axiom can disturb it.)

✅ `Cat.Codep.Coherence` (2026-07-09/10).

**T5: The three coherence cells.** `absorb-lcoh`, `absorb-rcoh`
(post-eval inner form), and the self-dual `couple-D₀` are
independent of the five axioms. Twisting
`interchange' = interchange ∙ τ` by a pointwise loop family that
vanishes at the `(idn,idn,idn,idn)` instance preserves all five
axioms and breaks the cells. Carrier for a nontrivial τ: the S²
path groupoid (`π₂(S²) = ℤ`). Pairwise the cells sit at disjoint
interchange loci, so none implies another.

📐 twist argument + carrier sketch (2026-07-10/11). The cells are
fields in ✅ `Cat.Codep.Coherent`.

**T6: θ-core is a theorem of the cells.** From the three cells,
`θ-core : ap (pre e) (post-eval e) ≡ interchange e e e e ∙
ap (post e) (post-eval e)` is derivable by path algebra
(`θ-core = sym i ∙ L`).

✅ `Cat.Codep.Coherent` (2026-07-11).

**T7: The identity-argument gauge collapse.** `gauge-r :
absorb-r (idn) ≡ post-eval (idn)` and its mirror `gauge-l` are
derivable from the three cells via the free naturality square
(`homotopy-natural absorb-r (post-eval e)`) plus `couple-D₀` and
`absorb-lcoh`. Hence the whole cluster
`{absorb-l e, absorb-r e, post-eval e}` (all of type `D₀ ≡ idn`)
collapses to a single path. No fourth cell.

✅ `Cat.Codep.Coherent` (2026-07-11). History (🧪
`Gloss.TriangleFace23` isolates the bridge): first blocked and
misattributed to T11's countermodel. The gauge is π₁-level and
derivable. The S²/π₃ obstruction lives one dimension up.

**T8: The Mac Lane triangle.** Weak triangle from the five axioms
alone. Full triangle (`ap (_⨾ g) (unitr f) ≡ assoc f (idn) g ∙
ap (f ⨾_) (unitl g)`) from the overlay, with `gauge-r` closing
`face₂₃`. The mirror triangle is the one-line op-instantiation
`triangle-full-tower (op C) (op-coherent A2)`.

✅ `Cat.Codep.Triangle` (2026-07-11).

## 3. Duality

**T9: The parity theorem.** Under `op` (hom reversal + context
swap): `pre^op = post` and `post^op = pre` DEFINITIONALLY.
`post-eval^op` is literally the base field. `unit-eqvl/r` swap.
`interchange^op = sym ∘ mirror`. `compose-contr^op` transports
along one funext'd interchange.

Every mirror axiom is derivable
from the base fields. With the Route-B center,
`f ⨾^op g = g ⨾ f` and `op-comp-eq` hold by `refl`.

✅ `Cat.Codep.Op` (2026-07-10, Route-B 2026-07-11).

**T10: Strict self-duality of the category core.**
`op-invol : op (op C) ≡ C` as a record path for the 5-field
`category` (copattern components, `is-prop→PathP` only on
`compose-contr`).

✅ `Cat.Codep.Op` (2026-07-10).

**T11: TEL-independence.** The 3-cell `TEL : bridge-l^B ∙
bridge-r^A ≡ qmove` (the op-invol component for any coherence
cell carried as a field) is independent of the eight fields. A
coherent twist shifts the `absorb-lcoh` field by
`κ ∈ π₃(S²) = ℤ` (a π₀-component change of the 2-cell field). It
leaves the base-only transport `qmove` fixed and κ-displaces the
cell-carrying bridge.

📐 countermodel over the S² path groupoid, dimension count
verified (2026-07-11). The `ap(ap E)`-transfer analysis confirms
no derivation route exists (faithful transfer, residue located).

🧪 `Gloss.EightFieldWall` (the irreducible-obligation display in
"The double-opposite obstruction", and the definitional-center
opposite-axioms/discharge verifications).

**T12: The op-involution regress ("coherence of the dualizing
involution forces truncation of the hom ∞-groupoid").** For wild
homs, no finite tower `(5 fields + cells + TEL-fields to depth k)`
admits a strict op-involution record path. Each level's op-invol
component is a `(k+2)`-cell with the bridge/transport asymmetry.
`π_{k+2}` of a single carrier refutes it (S² has nonzero homotopy
in infinitely many degrees). Hom-`n`-truncation would
terminate the tower at `n+1`. The incompatibility is exactly the
wild-homs commitment.

📐⚠️ level 1 is T11 (established). Levels `k ≥ 2` are
mechanism-conjectured (the asymmetry provably persists, the
explicit `θ_k` not ground out). Consequence shipped: the coherence
overlay dualizes covariantly (`op-coherent`), with deliberately no
`op-coherent-invol`.

NOVELTY CANDIDATE: anticipated in spirit by
the duality-involutions/dagger-higher-categories literature and by
homotopy-fixed-point obstruction theory. We know no published
statement in this record-level wild form. Citation research
pending before any novelty claim in prose.

**T13: The prop-pinning trichotomy.** No prop-valued predicate on
`category-axioms` derives the coherence cells. Every candidate
falls in one of three classes:

- (i) τ-blind: all representability props. `emb` is an equivalence
  in path-groupoid carriers, so every `fiber emb T` is contractible
  in honest and twisted structures alike.
- (ii) truncation-impotent: a separating prop exists
  (`∥ interchange e⁴ ≡ ι₀ ∥`) but cannot eliminate into the
  non-prop cell.
- (iii) model-false: `is-contr` of a wild path/Π-space.

Slogan: a proposition cannot canonically select an element of a
wild path-space.

📐⚠️ (i) is airtight (rests on the 🧪 `Gloss.PathGroupoid`
instance). (ii)/(iii) established (🧪 `Gloss.PropPinning`). The
exhaustiveness step is morally complete but not
formalization-grade (2026-07-11).

## 4. Identifications (what the cells ARE)

**T14: Interchange splits at the substrate.** `interchange-1` (the
bimodule interchange on a single composite, `(f ⟩ F) · g ≡
f ⟩ (F · g)`) is definitional: the two actions touch disjoint
context slots. `interchange-2` (the record's field, coupling two
embeddings) is, at the tautological filling, exactly the base
category's 4-fold associator on `a ⨾ f ⨾ g ⨾ b`. τ is the wild
base's associator freedom. The two-sided-representability route to
deriving it (extractions of `compose-contr-R/L` agreeing) is
circular.

📐 direct computation + circularity trace (2026-07-11,
faithful-stratum memo).

**T15: Kelly identification.** The three cells are the
wild-categorical residue of Kelly's unit-coherence theorem. The cells
are the left/right action-unit triangles and the center `λ_I = ρ_I` cell
of a bimodule (couple-D₀ is the op-fixed center cell, hence
self-dual). Kelly's derivations are naturality-plus-cancellation
arguments. The audited source shows three distinct moves: the
K-stripping principle (Thm 7 only), direct iso-cancellation
(Thm 6), and the naturality of c (Thms 8–10). Untruncated homs
foreclose all three. Regularity does not pin them: faithfulness is
a property of `emb` (twist-invariant, h-level 1). The cells are twist-variant
(h-level 2).

📐 (2026-07-11, bimodule memo). ⚠️ lifted 2026-07-13 under the
audit-keyed rule: `resources/kelly-maclane-conditions` vendored
and statement-audited 46/46, the source-identification now
SOURCE-CHECKED at its anchors. The wild-foreclosure claim remains

📐, kitcat's own argument.

**T16: The Melliès convergence.** kitcat's `op`/`op-invol` is
Melliès' `(−)op` involution in his "involutive 2-category" reading
of Cat. `op-coherent`'s θ-bridge structure is the chiral-functor
filler `F̃` (invertible, not identity). At the category core the
chirality presentation is optional (T10 = the strict-chirality
warm-up). The coherence level forces it (T12 forbids the strict
filler). The tautological chirality `(C, op C)` is fully
definitional BECAUSE of Route-B
(`op-comp-eq = refl` ⇒ `star-comp = refl`).

📐 design-level identification against the paper (2026-07-11,
chirality memo), backed by `resources/mellies-dialogue-chiralities`,
whose statement audit covers the identification. The
involutive-2-category reading and Theorem 3 verified at their
anchors, 2026-07-13. The audit also corrected this entry's
notation: the source writes `(−)op`, not `†`.

**T17: Binary-ancestor calibration.** The one-sided ancestor
(`repr : hom ↪ endo-operators`) is the `fam := unit` filling of the
two-sided theory. Its known limits are measured costs at that
parameter point: interchange's TYPE degenerates (interchange is
the fam-action's presence), and unit-uniqueness needs the fam
action.

📐 (2026-07-11, faithful-stratum memo).

## 5. Model and instance facts

**T18: Path groupoids are hcategories with emb an equivalence.**
Over any type `A`: `hom x y := x ≡ y`, `emb f ((w,a),(v,b)) :=
pcom (sym a) f b` discharges all five axioms, and `emb` is a full
equivalence (the context is a product of contractible singletons),
so `compose-contr` is `eqv-fibers`.

🧪 `Gloss.PathGroupoid` (2026-07-10).

**T19: Prop-hom instances trivialize the cells.** Over
propositional homs, all three overlay cells (and the gauges)
discharge in one line each.

✅ `Cat.Codep.Coherent` (`prop-homs`), walking-arrow instance
(2026-07-11).

**T20: Conservation of the pentagon plumbing.** Binary
right-nested fiber witnesses are a measured optimum at this
record. Endpoints in pcom-native form cost +5 atoms (whisker faces +2
each), and catr-bridges on binary endpoints are impossible
(distinct hcom terms). Iterated lifting bears the tower's
witnesses. Ternary-first governs born-ternary compositions.

🧪 `Gloss.PcomConservation` (2026-07-10).

**T21: extract-agree is independent of the faithful stratum.**
Over the three-layer faithful stratum (Petrakis fam/cofam
substrate, Π-integral codep-structure, representability overlay),
the `extract-agree` field
(`compose-contr f g .center .fst ≡ f ⨾ᵇ g`) is not derivable from
the remaining fields. The collapsed-context countermodel
(`ob = ⊤`, `hom = Bool`, `⨾ᵇ = xor`, `fam = cofam = ⊤`,
`res = Bool`, `emb = const`) fills every other field while
extract-agree fails at `(false, true)`. The refutation survives
any future base unit/associativity laws for `⨾ᵇ` ((Bool, xor,
false) is a group). It kills derivations at all levels (everything
at `0ℓ`, so a polymorphic derivation would specialize). The
⨾ᵇ-level composition law `F · (g ⨾ᵇ h) ≡ (F · g) · h` is
derivable extract-agree-free and emb-free (`·-comp-base`). Only
⨾-functoriality costs the bridge.

The honest boundary, in three
clauses:

- (i) The machine-checked kill covers the admissible weaker space.
  In the model `emb` is an equivalence, so every
  fiber-representability strengthening holds (`all-repr`,
  `idn-repr-holds`), the fam side is pointed (`fam-pt`), and
  untruncated ◃/▹ orbit surjectivity holds (`orbit-surj`,
  `orbit-surj-cofam`). The weakening class {extract-agree, emb-hom
  `emb (f ⨾ᵇ g) ≡ emb f · g`, extract-agree-emb
  `emb (f ⨾ g) ≡ emb (f ⨾ᵇ g)`} is equivalent over
  `compose-contr`, so the one countermodel refutes all three
  (`no-EH`/`no-EE`).
- (ii) Base-style DECODING structures (a `ctr` with its evaluation
  equations) are outside the refuted space BY DESIGN. They derive
  the bridge because they ARE the bridge in a different wrapper.
  That is `Cat.Type`'s own route (`pre-comp`), not a gap in the
  kill.
- (iii) The bimodule-faithfulness / two-sided-representability
  candidate class (action-faithfulness, the itc2/ccL two-sidedness
  imports) fails in the model, and only argument plus the two
  walled derivation routes exclude it. Its countermodel-grade
  upgrade is registered, designed, unbuilt.

Consequence: the faithful stratum's abstract propositional-strata
count is three BY THEOREM.

🧪 `Bb.CatsWithExplicitInterchange.Gist.CodepExtractAgree` (2026-07-13).

## 6. The faithful stratum

The three-layer stratum (Petrakis fam/cofam substrate, Π-integral
codep-structure, representability overlay) from the
faithful-stratum arc. Prior entries: T14/T17 (identifications),
T21 (extract-agree independence, with the records' definition).

**T22: The tautological filling recovers the representable core
definitionally.** Every category tautologically fills the
three-layer faithful stratum (T21's records):
`fam y = Σ v , hom y v`, `cofam x = Σ w , hom w x`, actions by
`pre`/`post`, `⨾ᵇ := ⨾` (the extracted center, no raw data
survives at the instance),
`res γ = hom (γ .fst .fst) (γ .snd .fst)`. The filling is
definitional at every operation. The checker accepts
res-invariance as the identity function, the four codep laws as
`refl` (their PathP families are definitionally constant), and
`extract-agree` as `refl`. The stratum's fixed-endpoint action
recovers the frozen Base action `_·_` by `refl` (`killcheck-dot`),
and interchange-1 is definitional (`killcheck-itc1`).

The
operation-level recovery rests on function-valued res-invariance:
the path-valued form recovers the action only propositionally,
since `transport refl` is not definitionally the identity. At the
filling, two of the abstract stratum's three propositional strata
(T21) definitionalize: res-invariance and extract-agree. The
interchange stratum remains propositional.

🧪 `Gloss.TautologicalFilling` (2026-07-13).

**T23: Agreement ⟺ interchange-2 over the two-sided stratum;
both walled from the fields.** Over the abstract faithful stratum
with two-sided representability (the right field `compose-contr`
plus a hypothesis-explicit left contractibility `ccL`),
extraction-agreement (`f ⨾ g ≡ f ⨾L g`) and `interchange-2`
(`emb f · g ≡ f ⟩ emb g`) are inter-derivable. One `pcom` upward,
a one-fiber transport downward. The two-sided route to interchange
is therefore exactly circular (the constructive sharpening of
T14's circularity trace).

Neither side admitted a derivation from
the stratum + ccL alone: both pre-registered routes wall at the
same pointwise bridge,
`res-inv-r g … (emb f …) ≡ res-inv-l f … (emb g …)` at `res γ`,
frozen as verbatim refl-probe residues. The representability
fields are twist-blind (`is-contr` is propositional,
`cc-τ-blind`). The stratum's field inventory has no slot of
interchange's type, so a T5-style twist has nothing to deform. At
the tautological filling the `interchange-2` statement is
term-for-term the base category's `interchange` (`itc2-taut`,
machine-checked in T22's certificate). The coherence cells are
intrinsic to wild two-sidedness, not artifacts of the
representable presentation. The wall's `⨾ᵇ`-shaped twin is
independent by theorem (T21), consistent with the T13 trichotomy.

🧪 `Gloss.InterchangeCircularity` (2026-07-13).

**T24: Conservation of the pentagon engine over the abstract
stratum.** The pentagon engine transplants from
`Cat.Codep.Coherence` to the abstract faithful stratum at +0 extra
bridge steps per face, with res-invariance an opaque field.
`·-comp` closes in two links: a dependent line moving the
extraction gap along `extract-agree`, and a `codep₂-r` PathP
applied over the same `fam₂` track. After that the assoc tower,
`reindex-face`/`face₂₃` (reindex family), and
`whisker-face`/`face₁₂` (whisker family) transplant unmodified.
The face proofs are the baseline proofs textually, so the count is
exact, not estimated. The res-invariance cost stays inside
`·-comp`'s interior. The engine is right-action-only.

Unchecked residue: face₄₅ (same reindex family) and face₃₅ untested.
`face₃₅`'s Coherence lift is `ctr`-dependent, which does not exist
at the stratum, so it plausibly gates on the interchange bridge
(T23). `face₁₄`'s `homotopy-natural` bridge is out of scope.

📐 machine-checked in the tracked spike
`Test.CodepFaithful-20260713-140913 @ dde1f57` (module A3), not
frozen. Transplant identity verified line-for-line in the accuracy
review (2026-07-13). The Test/ citation is Lane's granted
exception to the promotion-trigger rule (2026-07-13): any future
Test/ sweep retains the spike while this entry stands.

## 7. The framed deductive-system theory

Entries in this section are machine-checked in the working tree
and not yet commit-pinned. Each ✅ upgrades when the tree lands.
The theory is documented in `docs/deductive-systems/`.

**T25: Propositionality of every tier and of the package.** Each
of `is-stable`, `is-invertible⁻`/`is-invertible⁺`/`is-invertible`
is a proposition outright. `is-composable` is one over the
stability that indexes it. `is-deductive-system` is a proposition,
its composability component filled by a path over the moving
stability. Hence `deductive-system` splits as one structure field
and one property field, and `opᴰ` is an involution. `opⱽ-invol`
and `op-eval` are `refl`, and `opᴰ-invol` is `refl` on the carrier
with the axioms component by propositionality.

✅ `Cat.Logic.Base` (2026-07-25).

**T26: The framing is two reflexive graphs.** A twist is a
reflexivity datum, so a virtual graph carries two reflexive-graph
structures on one underlying graph. Fans and cofans name no
reflexivity, so the term and coterm families come from either
graph. The *centers* split: `var` is the cofan center of the
negative graph and `covar` the fan center of the positive one, so
the axiom pairs one from each.

Univalence is framing-blind
(`univalence-shared` is `refl`), and the opposite is the swap of
the two graphs composed with `rx.op` (`op-graph⁺`, `op-graph⁻`,
both `refl`). The two-sided base is
`rx.binary-product (rx.op graph⁻) graph⁺`, whose reflexive edge
**is** the framing: at a diagonal vertex, the axiom rule as one
edge.

✅ `Cat.Logic.Graph` (2026-07-25), every claim `refl`.

**T27: Each family is a lens over the graph of the twist it does
not hold, and each cut is a fibration.** A lens states its unitor
at its base's reflexive edge, and each action sits at the twist
its own axiom half does not carry: `term-lens` is oplax covariant
over `graph⁻`, `coterm-lens` lax contravariant over `graph⁺`, each
unitor that side's cancellation. Both displays are univalent with
no condition on the base, the families being discrete.

The coslice
display takes its displayed reflexivity from the cancellation
alone. Its covariant lifting condition is exactly stability
(uniqueness) plus the coterm cut (existence). `push` is the
composition and `lift` the head-rewriting witness, both on the
nose. The absorptions consume no tier and sit over the pins and
the cancellation alone.

✅ `Cat.Logic.Display`, `Cat.Logic.Base` (`absorption`)
(2026-07-25).

**T28: Stability is an embedding condition.** `is-stable` is
`reflect` having propositional fibers at every pair of objects
(`stable-is-embedding` is `refl`). Over hom-sets the judgments
form sets, so the tier reduces to injectivity of transmission, the
edge surrounded by one twist of each sign
(`stable-from-hom-sets`).

✅ `Cat.Logic.Base` (2026-07-25). Discharges the shape of the
truncated-regime obligation in
`notes/2026-07-22-deductive-system-design.md` (O4).

**T29: Interchange is a cospan coherence.** Over the two-sided
base each composite judgment is the transport with one leg held at
its twist, applied to one factor's reflection. The two land in the
fiber at the outer pair from distinct vertices with legs pointing
the same way. Agreement of the two cuts is agreement of that
cospan's two pushforwards, both directions.

The two-sided
transport composes, but onto a base edge taking one hand's
composition on one coordinate and the other's on the other. No
single composition therefore makes the lens functorial. What a
mediation buys, read here, is that functoriality.

✅ `Cat.Logic.Display` (`push-is-composite⁻`/`⁺`,
`cospan-from-cuts`, `cuts-from-cospan`, `bipush-comp`)
(2026-07-25).

📐 that no display of `judgment` can carry the agreement as an
edge. A displayed edge relates data over the two ends of one base
edge, and the reflections compared sit at distinct vertices. A
base making them diagonal would make composability reflexive. The
argument, not a formalized impossibility.

**T30: Framing collapse is weaker than mediation.** The derivation
of `twists-agree` uses a left and a right unit for *one*
composition, so it goes through on either missing unit law alone,
with no interchange: `collapse⁺`, `collapse⁻`. Since a mediation
supplies those laws, each hypothesis is weaker as a statement than
interchange. Two collapses separate: the twists becoming one edge,
and the compositions becoming one operation. Interchange gives
both. A missing unit law gives only the first.

✅ `Cat.Logic.Base` (2026-07-25). Corrects the "nothing between"
reading in `docs/deductive-systems/mediation.md`.

⚠️ whether the two collapses are separable is OPEN. In the group
model of T31 they are equivalent, and the reason localizes the
search. There `reflect` is an associative product, so the cuts
differ only by the junction's twist. A separating model needs a
`reflect` not of that form.

**T31: The framed package on wild fans, with both boundaries
arithmetic.** An abelian group read as a one-object virtual graph,
framed by an arbitrary *pair* of its elements, satisfies every
tier. A fan there is the whole group, so the underlying graph is a
path object only when the group is a proposition
(`univalent→prop`). This is the first framed model off that
boundary. The
framing is free, and two conditions become equations in the group.
The cancellation is `t⁻ · t⁺ ≡ e`, and agreement of the two cuts
is `t⁻ ≡ t⁺`, so the two cuts differ by exactly the framing's own
discrepancy. Holding both forces each element to be its own
inverse.

✅ `Bb.WeakDeductiveSystem.Gist.FramedGroup` (2026-07-25). Retired to the
archive 2026-07-28: the free-framing models live in
`Bb.WeakDeductiveSystem.Gist`, beside the path-groupoid witness
`Bb.WeakDeductiveSystem.Gist.FramedCut`.

**T32: Stability is a theorem of the contractible negative cut.**
`axioms→stable : is-deductive-system → is-stable`. The negative
composite at the twist is a reflection (`composite⁻-twist`), so the
cut's contractible fiber transports to every image fiber of
`reflect`. `image-fibers-contr→is-embedding`
(`Core.Function.Embedding`) then closes the embedding. Stability is
not a field of the package.

✅ `Cat.Logic.Base` (`axioms→stable`,
`contr-cut⁻.stable-from-contr-cut⁻`) (2026-07-28).

**T33: The cancellations are theorems of the tiers.** Each tier's
centre reads back as the other twist: `centre⁻-twist⁺` and
`centre⁺-twist⁻`. Both cancellations (`cancel⁻`, `cancel⁺`) and
both twist absorptions (`absorb⁻`, `absorb⁺`) follow from the two
invertibility tiers alone.

✅ `Cat.Logic.Base` (`tower.balanced`) (2026-07-28). The certified
spike is `Cat.Logic.Gist.BalancedProfile`.

**T34: The four unit laws.** Each hand is two-sided unital with its
own twist as unit. `unitr⁺` and `unitl⁻` hold in `tower` with no
tier, from readback and each hand's cut. Under the two invertibility
tiers, `tower.balanced` adds `unitl⁺` and `unitr⁻`. Two unital
magmoids on one graph, offset by the double twist.

✅ `Cat.Logic.Base` (`tower`, `tower.balanced`) (2026-07-28).

**T35: The associativity profile is the pre-duploid triple.** The
deductive-system axioms (`is-deductive-system`) prove exactly
`assoc⁺`, `assoc⁻`, and `mixed-assoc`, and no more: the generic
`associates` property (associativity of a length-3 path regardless
of the middle edge's polarity) is independent, refuted by two finite
countermodels. The projection model (constant reflection over
`Bool`, both hands projections) satisfies the towers and the
readback record of `Bb.WeakDeductiveSystem.Gist.FramedInterchange`,
computes `associates f g h` to `h ≡ f`, and has no thunkable or
linear edge, refuting both `associates` and the invertibility tier
at once. The four-reader model (`Bool × Bool`) is a full
`is-deductive-system` whose tier centres are its only
thunkable/linear edges, refuting `associates` for every middle edge
without refuting invertibility.

✅ `Bb.WeakDeductiveSystem.Gist.AssociatesCountermodel` (2026-07-27,
`just check` re-run clean 2026-07-28). The profile is Munch-Maccagnoni's
Definition 1 (pre-duploid): three associativity laws fixed to a
polarity pattern on the middle two objects, `(••)`, `(◦◦)`, `(•◦)`,
matching `assoc⁺`, `assoc⁻`, `mixed-assoc` respectively — SOURCE-CHECKED
against `resources/munch-maccagnoni-duploids` (Definition 1, l.180 —
that entry's certification was withdrawn 2026-07-28, but its
Definition 1 digest is among those an independent read confirmed
faithful) and cross-checked
against `resources/mmmm-classical-notions`'s independent transcription
of the same triple (§2, l.1552-1562; `Statements verified: 7/7
CONFIRMED`, 2026-07-28). The transcription reverses composition order:
the sources compose applicatively, kitcat diagrammatically, so
`(h • g) ◦ f = h • (g ◦ f)` over `A -f→ N -g→ P -h→ B` becomes
`(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)`, which is `mixed-assoc`. Whether the
generic-`associates` refutation itself has a counterpart in either
source is not addressed by either paper's statement audit and is not
claimed here — this identification covers only the associativity
profile, not a broader duploid-source theorem.

## Standing results from earlier strata (pre-2026-07-10)

- **Squaring effect** (ternary idempotency ⇒ `e² = 1`, with the
  `K(ℤ/2,1)` counterexample to unit uniqueness): 📐, historical
  (Cat.Virtual era, motivated the yon-eval/yon-idpt resolution).
- **Monoidal `absorb-coh` independence** (π₀-separation
  countermodel, balanced difference, NOT 2-torsion): 📐
  (2026-07-0x, `Cat.Monoidal.Coherence` keeps the field).
- **`fiber-pathp` is false in general** (S¹ counterexample): 📐.
  Never use it as a lemma.

## Maintenance

Add an entry when a result is proven (or a countermodel
established). Upgrade 📐 → ✅ when mechanized. Record refutations
and misattributions honestly (see T7's history: walls cited
against the wrong theorem cost time). This file carries the facts.

Every 🧪 marker must name its `Gloss.*` certificate, and an entry
here must name every Gloss module. The ledger and the Gloss
namespace are one maintained unit. Promotion criteria and the
freeze ritual live in CLAUDE.md ("Test → Gloss promotion"):
ledger-linked, not mechanized elsewhere, arc closed, frozen at a
named commit, append-mostly.

Every 📐 source-identification entry names its backing
`resources/<slug>/` entry and carries ⚠️/CONJECTURED until that
entry's **statement audit covers the cited identification**. Fidelity
is checked against the source, not merely present on disk.
An unaudited entry lifts nothing, and a Lane veto of the entry
re-imposes ⚠️. This is the external mirror of the 🧪↔`Gloss.*`
bijection. (Two lifts to date ran under this rule: T16 on the
chiralities audit, 2026-07-13 morning, and T15 on the Kelly audit,
2026-07-13 evening. T35, 2026-07-28, is the first entry written
straight to SOURCE-CHECKED, since the duploid audit landed before the
ledger entry did — no ⚠️ interval to lift. No ⚠️ source-identifications
remain.)
