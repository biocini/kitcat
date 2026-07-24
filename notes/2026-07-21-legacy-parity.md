# Plan — 2026-07-21 — Legacy parity on the two-field record

The major objective (Lane, 2026-07-21): a comprehensive, correctly
articulated, general-purpose monoidal category theory library,
sufficient to formalize ribbon categories in service of the PL
research work. The refoundation — the two-field `monoidal-axioms₀`
with independent ι⁺/ι⁻ and derived ω — serves that end; it is not
the end itself. The concrete program is **feature parity with
`Cat.Monoidal.Legacy`** on the refounded record. Nothing gets
overfit to the detection instances: the instances certify, the
library modules stay general.

This memo is the pre-registered design for that program: the
per-cell parity audit of every Legacy module (all read in full this
session), the braided design fork with an argued recommendation,
the Twist disposition, and the port order. Rack work is off the
critical path entirely — the braided theory develops first and the
rack type is designed afterwards from what the model teaches
(rulings recorded in `2026-07-21-rack-design.md`).

## Where parity already holds

The new `Cat.Monoidal` covers Legacy's record and `theory₀`
cell-for-cell. The dictionary:

- `⊗₀-interchange♭` (field) ↦ ι⁺/ι⁻ (fields, same ♭ shape);
  `⊗₀-interchange` ↦ `ι⁺-pt`/`ι⁻-pt`.
- `⊗₀-spine-contr` (field) ↦ `⊗₀-pull-contr` (field) with the full
  spine a theorem (`over-interchange.⊗₀-spine-contr`, the
  `Σ-contr-contr`/`spine-tail` assembly) — the axiom shrank.
- `⊗₀-emb-comp-op`/`-coh` (spine projections) ↦
  `over-interchange` derived; `⊗₀-coh→∙` is now `refl` (Legacy
  proved it by `Path.commutes`).
- Every `theory₀` cell is present: the interchange-free chain in
  the new `theory₀` proper, the ι-consuming chain in
  `over-interchange ι` developed once and instantiated at either
  field, the unitors per-ι in `unitors ι` with the agreement types
  as the stated boundary, the representability calculus landed
  through ι⁺ with `image-contr-invariant` certifying indifference.
- Level 1 repeats the pattern: `⊗₁-spine-contr` (field) ↦
  `⊗₁-pull-contr` (field) + `over-interchange₁` derived spine;
  `⊗₁-interchange♭` ↦ `ι⁺₁`/`ι⁻₁`.
- The presentation comparison `axioms₀-compare` (Legacy ≃ Σ M,
  interchange-agree M) and the flank boundary already live in
  `Cat.Monoidal.Properties`.

One deliberate divergence, not a gap: Legacy's unitors are
absolute; the new ones are relative to a field choice, with
`unitr/l-agreement` marking exactly where content begins. Every
port below inherits this split — cells that consumed
`⊗₀-interchange♭` become `over-interchange`-parametrized, cells
that never touched it port verbatim.

## The parity ledger, per definition

### `Legacy.Bifunctor` (819 lines) → `Cat.Monoidal.Bifunctor`

- `⊗₁-hfiber.pull-contr` — its fiber (σ with the pre-side
  characterization) is *definitionally the statement of the new
  `⊗₁-pull-contr` field*. Nothing to prove; the module's
  `p-char`/`q-char` vocabulary, the Kan-lid extension
  (`extend-q`/`extend-θ`), and `push-contr` transcribe into
  `over-interchange₁` (the lid is over the derived
  `⊗₁-emb-comp-coh` there; alternatively `push-contr` projects
  from the derived `⊗₁-spine-contr`).
- Interchange-free, port verbatim: `⊗₁-cast-path`/`⁻¹`,
  `⊗₁-comp-eq-ev`/`-pre`, `⊗₁-pre-distr`, `⊗₁-pre-comp`,
  `⊗₁-preserves-⨾` (its glue consumes only the pull side and
  `⊗₁-emb-⨾`), `⊗₁-wit-contr`, `_●₁_`, `_↝̂_`, `↝̂-fill`,
  `⊗₁-wit-σ[_,_]`/`⊗₁-wit-σ`/`⊗₁-wit-unique`, `assoc-σ●₁`,
  `assoc●₁`, `⊗₁-wit-∙`, `⊗₁-assoc`, `_↝₁_`, `↝₁-repr`,
  `ap-⊗₁-emb-lc`, `⊗₁-hom≃total-representable`, and the whole
  `⊗₁-repr-*` calculus once image-contraction exists.
- Per-ι (land in an `over-interchange₁`-style section):
  `⊗₁-comp-eq-post`, `⊗₁-pre-is-post`, `⊗₁-absorb-l/r`,
  `⊗₁-idn-▴`/`▾₁-idn`, `⊗₁-emb-idn-absorb`, `⊗₁-post-distr`,
  `_○₁_`, `unitr-σ●₁`/`unitl-σ●₁`, `⊗₁-unitr`/`⊗₁-unitl`.
- `unitl-ap` — the one computation. It consumes `unitl-σ●₀`
  (per-ι) and ends on `⊗₀-coh→∙`; with `⊗₀-coh→∙ ≐ refl` in the
  new record its last leaf drops. `⊗₁-emb-image-contr` then lands
  through ι⁺ as at grade 0, with the `is-contr-is-prop`
  invariance line beside it.
- Naming: the new bundle already opens a module named `theory₁`
  (the spine). The ported derived calculus needs its own module
  name inside `Cat.Monoidal.Bifunctor` — settle at landing,
  kebab-case per the convention.
- Displaced-boundary addendum (flagged, not required for parity):
  whether the two fields' displaced unitors agree over the
  grade-0 agreements — the displaced flank boundary — is new
  Properties material with no Legacy counterpart.

### `Legacy.Coherence` (1221 lines) → `Cat.Monoidal.Coherence`

- **Pentagon: entirely interchange-free.** `pentagon●₀`, the
  `nrm-slide₀/₁` straighteners, `assoc●₀-nrm`/`assoc●₁-nrm`,
  `⊗₀-pentagon`, `pentagon●₁`, `⊗₁-pentagon` consume only the
  pull side, the sealed assoc lines, and the wit calculus. Ports
  mechanically once Bifunctor lands.
- **Interchange-coherence block: per-ι.** `ι-mult-r₀/l₀` (the
  3-coherence hypothesis types), `●₀-coh`,
  `⊗₀-interchange-natural` (free naturality via the prop fiber),
  and the displaced `ι-mult-r₁/l₁`, `●₁-coh`,
  `⊗₁-interchange-natural` all mention the interchange only
  through the ♭ field — restate over an arbitrary
  `(ι♭ : U → V → A ▿₀ B ≡ A ▵₀ B)` (with its displaced mate at
  grade 1) and instantiate at either field. Naturality stays free.
- **Triangle: per-ι.** `triangle₀`/`triangle₁` ride the unitor
  σ-lines, the absorptions, and `is-coh₀/₁` — all
  field-relative. Ports inside the parametrized section.
- **`is-monoidal-2-coherent` — the one genuine design point.**
  Its `is-coh₀` compares `▾₀-idn` against `⊗₀-emb-idn-absorb`,
  both ι-consuming. Demanding it at both fields simultaneously
  would trivialize ω at unit flanks (the `twist-reduces-to-omega`
  argument — see Twist below), so the record CANNOT be stated
  over both fields at once without collapsing the very freedom
  the two-field record exists to keep. Recommended shape: the
  coherence extension is **indexed by the interchange choice** —
  a record family over `(ι₀, ι₁)` in the shapes the record's
  fields already have, instantiated at ι⁺ or ι⁻ separately; an
  instance answers for whichever chirality it certifies, and
  whether the two instantiations cohere is Properties material
  (connected to the flank boundary). RULING WANTED before the
  record mints.

### `Legacy.Indiscrete` (127 lines) → `Cat.Monoidal.Indiscrete`

Two halves. The monoidal builder ports now: every morphism-grade
obligation is a center in a contractible family — ι⁺₁ AND ι⁻₁
both discharge from `hom-contr` identically, `⊗₁-spine-contr`'s
Σ-of-contractibles becomes the `⊗₁-pull-contr` shape (smaller).
The braided builders (`indiscrete-braided`,
`indiscrete-braided-coherent`) wait for Braid/Hexagon and port
with them.

### `Legacy.Iso` (111 lines) → `Cat.Monoidal.Iso`

`⊗-associator` + naturality is free of the field;
`⊗-unitor-l/r` + naturality are per-ι (parametrize the module,
or instantiate at the designated field with the agreement types
covering the other — same decision as the unitors themselves,
which the record already made: per-ι). `braided-iso` follows
Braid. Consumes `Cat.Iso`'s `path→iso` and `hom-pathp→square`
(both exist).

### `Legacy.Braid` (171) + `Legacy.Hexagon` (1796) — the redesign

What transcribes untouched (the 07-20 field-shape ruling): the
flank swap is the primitive — `⊗₀-flank-swap♭ : A ▵₀ B ≡ B ▿₀ A`
at witness arguments, its displaced mate at `⊗₁-wit`s, both
grades in one record; invertibility free; the braid assembled,
never primitive.

What the two-field record forces open: Legacy's braid is
`⊗₀-interchange♭ U V ∙ ⊗₀-flank-swap♭ U V` — composed after THE
interchange. With two fields the derived braid theory is
developed once over an arbitrary interchange (a module
parameter, never an index — no braid's type mentions ι, and the
♭ arguments are propositional witnesses, which cannot carry an
invariant) and instantiated at either field.

The invariants of the design (Lane, 2026-07-21, confirmed):
the braid is always just a path between tensored objects —
`⊗₀-braid x y : x ⊗₀ y ≡ y ⊗₀ x` at the object grade, the
hom-grade braid a `PathP` of derived tensors over that line;
invertibility is `sym`, free, with the cancellation
`sym braid ∙ braid ≡ refl` plain path algebra; the other-handed
*crossing* is `sym (⊗₀-braid y x)`, and nothing identifies it
with the forward braid — that identification is the symmetric
axiom, exiled. Twist data is derived object-level structure
(ω, read by winding as for S¹), never a field.

Across the field choice, the two assembled braids share their
crossing and differ by ω pre-composed — ω being a full twist
(even class), they are the two **framed resolutions** of one
crossing, kinked versus flat, the framing arriving as a derived
comparison. That comparison is the double-braiding/framing
defect the balanced layer later reads `ω-trace` against —
theorem-shaped, never stored. The swap stays the one honest
datum.

Recommended form:

1. `braided (M₀ : monoidal-axioms₀ C)`-side record carrying
   exactly the two swap fields (grades 0/1), as Legacy's does —
   no interchange composed in, no new axiom.
2. `braid-theory` developed **over an arbitrary interchange**
   (the `over-interchange` discipline): `⊗₀-braid♭[ι]`, the
   sealed `braid-σ●₀[ι]`, `braid●₀`, `⊗₀-braid`, and the grade-1
   mirrors, instantiated at either field. Naturality stays the
   type, for free.
3. Hexagons (`braided-coherent`): the fields are stated on the
   derived braid, so they inherit the ι-index — the same shape
   question as `is-monoidal-2-coherent`, same recommendation:
   an ι-indexed family, instantiated per chirality; cross-
   chirality coherence is Properties material tied to ω.
   RULING WANTED together with the Coherence one (they should
   answer the same way).
4. The hexagon derivation machinery (`hexagon-r₀/l₀`, the
   μ/ρ same-`fst` links, the displaced hexagon-r₁/l₁ towers)
   transcribes inside the parametrized theory — its only
   interchange consumption is through the braid and the sealed
   σ-lines, which the parametrization carries.
5. The Ω² instance: `DoubleLoopTensor` extends with the
   Eckmann–Hilton flank swap (`Core.Path.Exchange` supplies the
   cells) — the instance that proves the swap field's shape and
   gives the hexagons homotopical content. Minted WITH the
   record per the standing discipline; general statements only.

H2 (braiding a composite past one object) remains neither field
nor theorem, exactly as in Legacy — unchanged status, first
consumer of the `ι-mult` hypotheses stays the swap-half
comparison.

### `Legacy.Twist` (240 lines) — absorbed, one theorem transcribes

The countermodel's role is internalized by the refoundation: the
two-field record IS "an interchange and its loop-family twin"
with no relating axiom, the flank boundary states the derived/
contentful line, and CircleTensor is a live countermodel (two
genuinely distinct fields, machine-checked). The `Mω` builder and
`twist-monoidal` are superseded — `pin⁻`/`unpin` and the record
itself construct the same data.

What survives: the `reduce` algebra behind
`twist-reduces-to-omega`. Transcribed to the new record (where
ι⁺ plays ι⁻ ∙ ω with ω derived), it becomes a boundary theorem in
`Cat.Monoidal.Properties`:

    absorb-coh at ι⁻ → absorb-coh at ι⁺
      → happly (ω-pt I x) (I , r) ≡ refl

— the absorb-coh-level converse companion to
`flank-vanish→agreement`, sharpening decision question (a) from
the other side. The new `theory₀.absorb-coh` module (lhs/rhs
per-ι) already states the two sides. Port the algebra
(`ev-comp-op-eq`, `comp-eq-post-eq`, the α/ζ/β conjugation,
`conj-cancel` close) against the derived ω. DISPOSITION TO
CONFIRM with Lane: retire `Mω`/`twist-monoidal` without
replacement, land `reduce` as the Properties theorem.

### `Legacy.Properties` (772 lines) → additions to `Cat.Monoidal.Properties`

- `⊗₀-interchange♭-from` / `⊗₁-interchange♭-from` (the
  pointwise→♭ J-tower closures): parametrized by the raw
  embeddings, never touch the record — port verbatim.
- The swap-half comparison (`swap-half₀`/`swap-half₁`, the
  eight-link bridge, `hexagon-l≃swap-half` at both grades):
  braided-layer material; every consumed cell (`ι-mult`
  hypotheses, `braid-σ●` lines, `⊗₀/⊗₁-interchange-natural`,
  the interchange conjugators) exists in the parametrized ports
  above, so the comparison transcribes inside the same ι-index.
  Ports with Braid/Hexagon.

## The circle contrapositive — decided

`Test.CircleUnitorTwist` (landed with this memo, `--cubical
--safe`, cold ~1s): the derived unitor discrepancy
`sym (⊗₀-unitr[ι⁺] base) ∙ ⊗₀-unitr[ι⁻] base` **winds −1** — the
unitor σ-lines unfold (`opaque unfolding`) and the whole fiber
apparatus normalizes, `θ-winding = refl` at `negsuc Z`. The
right-unitor chain spends the deformation exactly once.
Corollaries in the module: `unitr-disagreement` (the agreement
type is refuted by the winding through Int discreteness) and
`flank-not-vanish` (`ω-vanish-l` refuted through
`routes-differ`) — the instance-level contrapositive of
`flank-vanish→unitr-agreement`. Consequence for decision question
(a): the circle is CONSISTENT with the converse (agreement forcing
vanishing) and provides no counterexample; both boundary
statements fail together, by the same rotation. A refutation of
the converse would need agreeing unitors over genuinely distinct
fields, which this instance cannot supply. For the braided design:
the unitor/twist relationship is one-consumption-per-absorption,
matching the flank-boundary analysis.

## Balancing entry points (noted, not designed here)

`ω-trace` stays the extracted balancing candidate; the two
derived braid chiralities give the braiding/double-braiding
reading of ω; the balanced/twist layer and the dialogue arc
consume these later (LB program phases 2–3). S²/Hopf stays the
off-path evidence tier. None of this shapes the parity ports.

## Port order and state

1. `Cat.Monoidal.Bifunctor` — LANDED (first-attempt typecheck,
   cold ≈1.8 s): pull-side hfiber = the field, cast paths, the
   free unit chain, `⊗₁-preserves-⨾`, the ι-consuming cells in
   `over-interchange-bifunctor` (push side by the derived spine,
   post chain, absorptions, `_○₁_`, image contraction with
   `unitl-ap` closing definitionally where Legacy spent
   `⊗₀-coh→∙`), the representability and witness calculi,
   `⊗₁-assoc`, and `unitors₁`.
2. `Cat.Monoidal.Coherence` — interchange-coherence block
   (`interchange-coherence ι♭ ι♭₁`: `ι-mult` hypothesis types,
   `●₀/●₁-coh`, both naturality cells) and the full pentagon
   (`pentagon●₀/₀/●₁/₁`) LANDED (cold ≈4.7 s; the pentagon's hom
   quartet is φ/ψ/χ/ξ — the record's derived ω owns the name
   Legacy left free). The 2-coherent record and triangle wait on
   open ruling 1.
3. `Cat.Monoidal.Indiscrete` — monoidal builder LANDED (ι⁺₁ and
   ι⁻₁ both discharge from `hom-contr`); braided builders wait
   for Braid/Hexagon.
4. `Cat.Monoidal.Iso` — LANDED: associator free, unitor
   isomorphisms in the parametrized `unitor-iso`; braiding half
   waits for Braid.
5. `Cat.Monoidal.Braid` + `.Hexagon` per the argued design, with
   the Ω² instance; then Indiscrete's braided builders, Iso's
   braiding half. Waits on open ruling 1 and the design
   confirmation.
6. `Cat.Monoidal.Properties` — pointwise→♭ closures LANDED
   (verbatim, carrier-level); the absorb-coh boundary theorem
   waits on open ruling 2; the swap-half comparison ports with
   Braid.

All landed modules: `just lint changed` clean; downstream
(`Test.DoubleLoopTensor`, `Test.CircleUnitorTwist`) re-checked
clean. `All.lagda.md` untouched per the chores batch beyond
removing the deleted stub's stale comment line.

Discipline throughout: `--safe --erased-cubical` for `Cat.*`;
first-attempt-typecheck standards; `just lint changed` per
landing; All.lagda.md stays in the deferred-chores batch.

## Rulings (settled, Lane 2026-07-21)

1. **ι-indexing of the coherence extensions**: RULED — the
   extensions index by the interchange choice, reified as the
   resolution vocabulary (below), instantiated per field;
   cross-choice coherence is Properties material.
2. **Twist disposition**: RULED — `Mω`/`twist-monoidal` retire
   without replacement; the `reduce` algebra lands as the
   absorb-coh boundary theorem in Properties.
3. **The reified choice** (methodological, Lane): the interchange
   choice becomes a first-class graded record —
   `⊗₀-resolution C I ⊗₀-emb` (one field, the ♭-form
   interchange; pointwise shadow derived) and `⊗₁-resolution`
   displaced over it — with canonical inhabitants `res⁺`/`res⁻`
   in `monoidal-axioms₀` and `res⁺₁`/`res⁻₁` in
   `monoidal-axioms₁`. The axioms' field lists are UNTOUCHED
   (record-freeze respected); the record's derived-theory modules
   and all downstream parametrized sections take resolutions in
   place of raw pointwise pairs. The three-tier discipline
   (interchange-free / generic-over-a-resolution /
   propositional-landed-with-invariance, plus the independence
   criterion: route pairs enter as fields only when neither route
   derives from the other) is recorded in the record header and
   here. Names minted this session await sign-off per convention.

## The mechanical remainder — GATED

**Gate (Lane, 2026-07-21): the interchange inquiry
(`2026-07-21-interchange-inquiry.md`) rules first.** The
choice-free-core question reformulates the monoidal axioms suite
itself, so nothing below executes until that investigation's
GO/NO-GO: on NO-GO the steps run unchanged; on GO the same
transcription targets re-package onto the settled core+resolution
form — the material is generic-over-choice throughout, so the
steps survive re-plumbed, but their exact signatures wait for the
ruling.

Within that gate, the steps are transcription against sources
read in full and rulings settled above — executable across
sessions with no design forks. Each step: land, typecheck
standalone, re-check downstream consumers, `just lint changed`,
note cold profile. `All.lagda.md` stays in the deferred-chores
batch throughout.

- **Step 0 — the resolution sweep.** In `Cat.Monoidal`: mint
  `⊗₀-resolution`/`⊗₁-resolution` beside the tensor vocabulary;
  add `res⁺`/`res⁻` (axioms₀) and `res⁺₁`/`res⁻₁` (axioms₁);
  reparametrize `theory₀.over-interchange`, `theory₀.unitors`,
  `theory₀.absorb-coh`, `theory₁.over-interchange₁` over
  resolutions; restate the agreement types at `res⁺`/`res⁻`; add
  the discipline paragraph to the header. Sweep call sites:
  `Properties` (`pin⁺`/`pin⁻`, the flank boundary's module
  applications), `Bifunctor` (`over-interchange-bifunctor`,
  `unitors₁`, the ι⁺ landing), `Coherence`
  (`interchange-coherence` takes the resolution pair directly),
  `Iso` (`unitor-iso`), `Test/DoubleLoopTensor`,
  `Test/CircleUnitorTwist`. Verification: re-check all nine
  affected modules.
- **Step 1 — 2-coherence + triangle** (`Cat.Monoidal.Coherence`):
  `is-monoidal-2-coherent` indexed by the resolution pair
  (fields `is-coh₀`/`is-coh₁` transcribed from Legacy:50-71);
  `triangle₀`/`triangle₁` transcribed (Legacy:391-541, 850-1221)
  inside the resolution-parametrized section, the associator face
  consuming the indexed record.
- **Step 2 — the absorb-coh boundary theorem**
  (`Cat.Monoidal.Properties`): transcribe Legacy.Twist's
  `ev-comp-op-eq`/`comp-eq-post-eq`/`absorb-*-eq`/`reduce`
  (Legacy.Twist:154-239) against the derived ω — statement:
  absorb-coh at `res⁻` and at `res⁺` together force
  `happly (ω-pt I x) (I , r) ≡ refl`.
- **Step 3 — Braid** (`Cat.Monoidal.Braid`): the `braided`
  record over the bundle with exactly Legacy's two swap fields
  (Legacy.Braid:55-107, statements unchanged — the 07-20
  field-shape ruling transcribes); `braid-theory` parametrized by
  the resolution pair, derived braid `R.ι♭ ∙ swap♭`, sealed
  `braid-σ●₀`, both grades (Legacy.Braid:120-171). The design
  invariants are recorded above (braid = bare path, `sym` =
  inverse, handedness = `sym` at swapped arguments, the two
  instantiations = framed resolutions differing by ω).
- **Step 4 — Hexagon** (`Cat.Monoidal.Hexagon`):
  `braided-coherent` indexed by the resolution pair, hexagon
  fields on the derived braid at that resolution (Legacy.Hexagon
  record :73-138); `hexagon-theory` — straighteners, both fiber
  hexagons with the μ/ρ same-`fst` links, both displaced towers —
  transcribed within the parametrized section
  (Legacy.Hexagon:143-1796). H2 stays neither field nor theorem,
  exactly as in Legacy — not a fork.
- **Step 5 — braided builders + braided-iso**: Indiscrete's
  `indiscrete-braided`/`indiscrete-braided-coherent`
  (Legacy.Indiscrete:90-127, per-resolution hexagon inputs);
  Iso's `braided-iso` (Legacy.Iso:94-111). These are the parity
  instances of the braided records, as they were in Legacy.
- **Step 6 — swap-half comparison** (`Cat.Monoidal.Properties`):
  `swap-half₀`/`swap-half₁` and both equivalences
  (Legacy.Properties:116-772), inside the resolution index,
  consuming Coherence's `ι-mult` hypotheses and
  `interchange-natural` cells.

Explicitly OUT of the mechanical remainder (queued post-parity,
not gating): the Ω²-carrier braided instance (behind the generic
path-groupoid `axioms₁` builder the 07-21 checkpoint names), the
displaced flank boundary, and the resolution-torsor theorem —
though the torsor observation feeds the inquiry's S1/S5 directly.
