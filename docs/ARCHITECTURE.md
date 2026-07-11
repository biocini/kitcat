# Kitcat Cat.* Architecture

The Cat.* namespace has four strata organized by dependency.
Stratum 0 defines the foundation category records. Stratum 1
builds core theory on the canonical `Cat.Type` record. Stratum 2
develops monoidal categories over the same record. Stratum 3
gives a representable presentation that abstracts over both.

## Strata

### Stratum 0 — Foundation records

Categories via ternary composition.

```
Cat.Type ─── canonical: four axioms
    │        (compose-contr, interchange, yon-eval, unit)
    └── Cat.Virtual ─── generalization: prop-classifier gates composition
```

**Cat.Type** is the canonical record. Categories are presented
via a ternary `emb`: `compose-contr` bundles the composite and
its characterizing equation into a contractible `fiber emb
target`, `interchange` links the noy and yon views pointwise, and
`yon-eval` gives `yon f x idn ≡ f`. All standard categorical
structure (unit laws, associativity) derives from these. Stratum
1 and the monoidal stratum build on it.

**Cat.Virtual** generalizes composition with a propositional
classifier on composable pairs: `compose-classified` gives a
contractible composite fiber only when the classifier holds, and
the combinator `⟨ f , g , c ⟩` is derived as the noy-side target.
The former separate `Cat.Classified` development is folded in
here.

### Stratum 1 — Core theory (on Cat.Type)

```
Cat.Type
    ├── Cat.Base ─────── universal properties, functors, adjunctions, isos
    │   └── Cat.Iso ──── path→iso bridge (idtoiso, hom-PathP≃square)
    ├── Cat.Coherence ── pentagon (from base), triangle (from 2-coherent)
    ├── Cat.Groupoid ─── path groupoid instance
    ├── Cat.Covariant ── covariant families (C → Type)
    ├── Cat.Yoneda ───── Yoneda lemma (via Covariant)
    └── Cat.Rezk ─────── Rezk completion HIT (--cubical)
```

**Cat.Base** develops universal properties as contractible
fibers, plus functors, natural transformations, adjunctions, and
the canonical isomorphism `_≅_` (with biinvertibility).
**Cat.Iso** (library-wide) builds on it: `idtoiso` sends an
object path to an isomorphism (J into `iso-refl`), and
`hom-PathP≃square` characterizes dependent paths between
morphisms as commuting squares — via `transport-equiv`, staying
`--erased-cubical` (no univalence).

### Stratum 2 — Monoidal categories (on Cat.Type)

A native two-tier monoidal development over the `category`
record: object-tier structure read off a ternary tensor
`tensor-emb`, plus a morphism-tier action on 2-cells. The
coherences mirror Cat.Coherence's emb-level proofs with the two
Unit object indices erased — never by delooping onto a Unit
category.

```
Cat.Monoidal ─── record: ternary tensor + unit, two-tier
    ├── Cat.Monoidal.Coherence ── pentagon + Mac Lane triangle (native)
    ├── Cat.Monoidal.Bifunctor ── morphism tier: bifunctoriality, naturality
    ├── Cat.Monoidal.Iso ──────── associator/unitors as _≅_ + nat squares
    ├── Cat.Monoidal.Braid ────── braided scaffolding: ⊗-braid, ⊗-braiding
    ├── Cat.Monoidal.Hexagon ──── E₂ hexagon-emb field + ⊗-hexagon (H1)
    ├── Cat.Monoidal.Indiscrete ─ builder: object data + ⊤-homs → monoidal
    └── Cat.Monoidal.Twist ────── absorb-coh independence core
```

**Cat.Monoidal** presents the tensor natively:
`tensor-emb : ob → ob → ob → ob` with unit,
`tensor-compose-contr`, `tensor-interchange`, `tensor-yon-eval`,
and a morphism-tier `htensor-emb` action on three parallel
2-cells. Gives `_⊗_`, the associator, the unitors, and unit
uniqueness.

**Coherence** derives the pentagon from the base axioms and the
full Mac Lane triangle from a `monoidal-2-coherent` record
(supplying the `absorb-coh` field), mirroring Cat.Coherence.

**Bifunctor** is the morphism-derived layer: `_⊗ₕ_`
bifunctoriality, the field-free identity `⊗ₕ-idem`, and
associator/unitor naturality as PathP over the object-tier paths.

**Iso** presents the associator and unitors as honest `_≅_`
isomorphisms with classical naturality squares, via Cat.Iso.

**Braid** is the free scaffolding of a braided structure: a
single field `tensor-flank-swap` (the half interchange does not
supply), from which the object braiding `⊗-braid : x⊗y ≡ y⊗x`,
its invertibility, and the isomorphism `⊗-braiding` all derive by
the same contractible-fiber projection as `⊗-assoc`.

**Hexagon** is the irreducible E₂ layer: a `braided-coherent`
record with the `hexagon-emb` field — a genuine axiom, since the
hexagon is a cross-target 2-path that `is-contr→is-set` cannot
force — and the derived object `⊗-hexagon` (H1). The field enters
only as a witness-move that vanishes on projection, so the object
hexagon is honest. The second hexagon (H2) is open.

**Indiscrete / Twist** are the machinery for the `absorb-coh`
independence result: `indiscrete-monoidal` builds a full
`monoidal C` from object-tier data over contractible homs, and
`twist-reduces-to-omega` shows a unit-supported interchange twist
forces `ω(I,x,I,r) ≡ refl` — the algebraic core of the
π₀-separation countermodel (the concrete `S¹ × ℤ/2` carrier is a
deferred `--cubical` island).

### Stratum 3 — Representable codependent categories

A trilayer presentation abstracting over both `Cat.Type` and
`Cat.Monoidal`. A category is `hom` + `idn` + a representable
embedding `emb` into `composite` morphisms + five axioms
(`compose-contr` for composition; `interchange`, `post-eval`,
`unit-eqvl`, `unit-eqvr` for the anchor). All lax-substitution
structure and the Mac Lane pentagon are derived generically.

```
Cat.Codep ─── aggregator (Base + Coherence + Coherent + Op + Triangle)
    ├── Cat.Codep.Base ────── structure/axioms(5)/bundle records;
    │                         all derived laws consolidated (coupling + unit)
    ├── Cat.Codep.Coherence ─ assoc-tower + pentagon-fibers + pentagon
    ├── Cat.Codep.Coherent ── 3-cell overlay + θ-core + gauges + op-coherent
    ├── Cat.Codep.Op ──────── op-structure/op-axioms(Route-B)/op + op-invol
    ├── Cat.Codep.Triangle ── Mac Lane weak + full triangle (face₂₃ via
    │                         gauge-r); op-dual mirror via op-coherent
    └── Cat.Codep.Instances ─ walking-arrow + type/monoidal triples
```

**Cat.Codep.Base** holds the three records: `hcategory-structure`
(operations `hom`/`idn`/`emb`, the flat carrier `cofam`/`fam`/`ctr`/
`ctx = cofam × fam`/`res`, the two actions `pre`/`post`, + all
axiom-free derived notions), `hcategory-axioms` (the five axioms +
extraction + *every* derived law, over a structure value), and the
`hcategory` bundle (fields `ob`, `structure`, `axioms`,
re-exporting both). The axioms record is complete, so the bundle IS the
category. Splitting the axioms off the operations makes naive
multi-object instances termination-safe. `idn` is the representable
anchor, characterized as a unit by the two unit axioms. Composition
`_⨾_` is extracted from representability.

The former `Cat.Codep.Coupling` and `Cat.Codep.Unit` modules are
absorbed into `hcategory-axioms`: the coupling idempotency block
(`post-comp`, `comp-eq`, `idem`, `pre-comp`) and the whole unit
fragment (`absorb-l`/`absorb-r`, `·-idn`, `unitl`/`unitr`,
`emb-image-contr`, `emb-post`, `unit-is-prop`, `is-representable-prop`)
are now record-internal. What stays standalone above the record are the
three provenance lemmas `post-comp-from-coupling`/`comp-eq-from-coupling`/
`idem-from-coupling`, whose explicit hypothesis lists machine-check that
idempotency never touches the unit axioms.

**Cat.Codep.Coherence** derives `assoc` and the full pentagon purely
from `compose-contr`/`emb-comp`/`·-comp` — no unit law, no
`interchange`. This is the collapsed tower: `assoc-tower` projects
`assoc` from the contractible triple fiber, and `pentagon-tower`/
`pentagon-fibers` carries the quadruple composite, the five faces, and
the named `pentagon` (the former `face₃₅-proof` and standalone
`pentagon` submodules are folded into `pentagon-fibers`). Each face
reads a fiber edge against a canonical lift of `assoc-σ` through
`contr-face`; `face₂₃`/`face₄₅` share the `reindex-face` helper, and
`face₁₂`/`face₃₅`/`face₁₄` share the lift-generic `whisker-face` — no
face is left direct (`face₃₅`'s lift uses the emb-at-center link,
`pre`/`post` being `emb` read at the center). It is the regression
baseline for the planned transfer-principle reformulation.

**Cat.Codep.Coherent** overlays three wild-categorical coherence
cells on the bundle — `absorb-lcoh`, `absorb-rcoh`, `couple-D₀` — in a
record `hcategory-2-coherent (C : hcategory o h)` *over* the bundle,
not in `hcategory-axioms`: the five-field category and its strict
`op-invol` stay the self-dual core. The cells are the identity-flanked
fragments of the base associator (Kelly's unit coherences), independent
of the five axioms since `interchange` is only supplied pointwise. From
them the `θ-core` is derived (not posited), as are the identity-argument
gauges `gauge-r`/`gauge-l`/`gauge-lr` (`absorb-r/absorb-l (idn x) ≡
post-eval (idn x)` and their difference) — the homotopy-naturality of
the absorptions along `post-eval`, whiskered against the θ-core
reconciliations; `gauge-r` is what closes the full Mac Lane `face₂₃`.
`assemble` rebuilds the overlay from a bundle plus the three cells, and
`prop-homs` discharges them one-line each when homs are
propositions. `op-coherent` dualizes
the overlay *covariantly*: two θ-bridges (`bridge-l`/`bridge-r`, each
`ap _ θ`) relay the op record's absorptions onto the base's, and
`couple-D₀ᵒ` conjugates by `sym`. There is deliberately no
`op-coherent-invol` — strict op-involution of the cells is independent
of the fields (S²/π₃ countermodel), so the five-field category is
strictly self-dual while the overlay dualizes only up to the bridges.

**Cat.Codep.Op** builds the opposite hcategory as the polarity
mirror of the post-biased presentation: `op-structure` reverses
`hom`, keeps `idn`, and precomposes `emb` with `swap`, which swaps
`pre ↔ post` definitionally. The parity theorem is that every mirror
axiom is derivable from the base five fields — post-bias is chirality,
not asymmetry. The eval axiom is self-mirror (`op-axioms .post-eval`
is the base's verbatim, since `pre f (idn y)` and `post f (idn x)`
are the same doubly-centered term); `interchange` reverses under
`sym`, and the unit equivalences trade places. `compose-contr` is
Route-B: its fibre center is *definitionally* the base extraction
`A._⨾_ g f` (transported by `swap·` across `op-comp-path`, one
`interchange`), with contractibility discharged by `is-contr→is-prop`
against the `swap·`/`swap·'` retract of the base fibre — so `Aᵒ._⨾_ f g`
reduces to `A._⨾_ g f` and `op-comp-eq` is `refl`. `op` bundles the
mirror, and `op-invol : op (op C) ≡ C` is definitional on
`hom`/`idn`/`emb` and `is-contr`-propositional on the composition
fibers (value-agnostic, so unaffected by the Route-B center). The base
gains the derived `pre-eval` recording the self-mirror coincidence.

**Cat.Codep.Triangle** carries the Mac Lane triangle over the bundle.
The three vertices sit in `compose-contr f g`, right-nested binary
witnesses through the `·-idn` expansion; each face reads a fibre edge
against a named law through `contr-face` and a canonical lift. The
*weak* triangle `ap (_⨾ g) (unitr f) ≡ assoc f (idn y) g ∙ α₂₃` is
complete — `face₁₃` (the free unitr right-whisker) and `face₁₂`
(associativity reindex) close against the base axioms alone, reusing
`assoc-tower`. The *full* triangle — identifying `α₂₃` with the
left-whiskered `unitl g` — is now **complete** in
`triangle-full-tower` (gated on the overlay `A2`). The reconciling cell
`absorb-r (idn y) ≡ post-eval (idn y)` — once thought independent — is
**derivable** as `gauge-r` (`Cat.Codep.Coherent`), so `face₂₃` costs no
fourth cell beyond the three overlay cells. `EU` reads the `unitl`
fibre-witness square back as a path; `happly` distributes
definitionally,
so the paid face collapses pointwise onto pt₂'s `·-idn` route through
`bridge`/`INNER` (the bridge is `gauge-r`).
`Test.TriFace23Probe-20260711` is retained as the historical isolation
of that bridge. The earlier "independent fourth cell" claim was a
misattribution: the `Cat.Codep.Coherent` S²/π₃ independence result is
about op-**involution** of the cell tower (one dimension up), not this
π₁-level gauge. The op-dual (mirror) triangle needs no separate proof —
`mirror-triangle` is the free instantiation of `triangle-full-tower` at
`(op C, op-coherent A2)`, the full triangle being uniform in the
coherent hcategory and `op-coherent` transporting the overlay.

**Cat.Codep.Instances** opens with `walking-arrow` — the interval
category **2** as a direct triple, the simplest example and the
regression guard for the termination class the split defeats (its five
axioms are prop-level; its `emb` is an equivalence). Then the `Type-*`
triple from `Cat.Type.category` (anchor = identity morphism) and the
`Monoidal-*` triple from `Cat.Monoidal.monoidal` over `⊤` (anchor =
tensor unit object); the merged coupling/unit fills are name-identical
to the source category's (`unit-eqvl = C.unit-eqvl`). Each checks that
the generic `assoc`, `pentagon`, and unit fragment specialize.

## Module status

<!-- machine-parseable: bin/docs-drift validates this table -->
| Module | Stratum | Status | Notes |
|--------|---------|--------|-------|
| Cat.Type | 0 | complete | Canonical four-axiom category record |
| Cat.Virtual | 0 | complete | Classifier-gated generalization (former Cat.Classified) |
| Cat.Base | 1 | complete | Universal properties, functors, nat-trans, adjunctions, isos |
| Cat.Iso | 1 | complete | idtoiso + hom-PathP≃square (library-wide, no univalence) |
| Cat.Coherence | 1 | complete | Pentagon from base, triangle from 2-coherent |
| Cat.Groupoid | 1 | complete | Path groupoid instance on arbitrary types |
| Cat.Covariant | 1 | complete | Covariant families, representable family |
| Cat.Yoneda | 1 | complete | Yoneda lemma for covariant families |
| Cat.Rezk | 1 | partial | Encode/section done, retraction missing |
| Cat.Monoidal | 2 | complete | Native two-tier tensor; assoc, unitors, unit uniqueness |
| Cat.Monoidal.Coherence | 2 | complete | Pentagon from base, Mac Lane triangle from monoidal-2-coherent |
| Cat.Monoidal.Bifunctor | 2 | complete | Morphism tier: bifunctoriality, ⊗ₕ-idem, unitor/assoc naturality |
| Cat.Monoidal.Iso | 2 | complete | Associator/unitors as _≅_, classical naturality squares |
| Cat.Monoidal.Braid | 2 | complete | Braided scaffolding: ⊗-braid, invertibility, ⊗-braiding iso |
| Cat.Monoidal.Hexagon | 2 | partial | hexagon-emb field + ⊗-hexagon (H1); H2 open |
| Cat.Monoidal.Indiscrete | 2 | complete | Builder: object data + ⊤-homs → monoidal C |
| Cat.Monoidal.Twist | 2 | complete | absorb-coh independence core (twist-reduces-to-omega) |
| Cat.Codep | 3 | complete | Aggregator: Base + Coherence + Coherent + Op + Triangle |
| Cat.Codep.Base | 3 | complete | trilayer records: structure / axioms (5 fields + all derived laws) / bundle; flat carrier; provenance lemmas standalone |
| Cat.Codep.Coherence | 3 | complete | collapsed tower: assoc-tower + pentagon-fibers + 5 faces (reindex-face for face₂₃/₄₅) + named pentagon; unit-free (compose-contr/emb-comp/·-comp) |
| Cat.Codep.Coherent | 3 | complete | 3-cell overlay (absorb-lcoh/absorb-rcoh/couple-D₀) over the bundle + derived θ-core + derived gauge-r/gauge-l/gauge-lr (identity-argument gauges, homotopy-naturality of absorb along post-eval); assemble, prop-homs, covariant op-coherent (no strict invol) |
| Cat.Codep.Op | 3 | complete | opposite hcategory: op-structure/op-axioms(Route-B center)/op + op-invol; parity theorem, eval self-mirror, op-comp-eq refl |
| Cat.Codep.Triangle | 3 | complete | weak Mac Lane triangle over the bundle (face₁₃ free unitr + face₁₂ assoc) + full triangle in triangle-full-tower (gated on overlay A2): face₂₃ closes via gauge-r (EU square-readback + bridge/INNER, happly distributes definitionally); op-dual mirror = free instantiation at (op C, op-coherent A2) |
| Cat.Codep.Instances | 3 | complete | walking-arrow + type/monoidal triples (5-axiom fills); generic theorems specialize |

## Deferred modules

The following exist but are experimental, blocked, or archived —
not part of the stable API. They are not in the status table
above, and `bin/docs-drift` does not validate them for existence
or holes.

| Module | State | Reason |
|--------|-------|--------|
| Cat.Product | partial | Record complete, projection functors stuck |
| Cat.Displayed | blocked | PathP without hom-sets (see below) |
| Cat.Slice | blocked | PathP without hom-sets (see below) |
| Cat.Virtual.Product | at-risk | Set-valued hom product; may not be fulfillable as stated |
| Cat.Dep | experiment | Un-fleshed-out category-record variant (copy of Cat.Type) |
| Cat.VirtualProposed | research | Pointwise compose-contr, untested |
| Cat.VirtualAlt | archived | In `Stash/Cat/` — noy/yon primitive variant |

## The Displayed/Slice obstruction

Both Cat.Displayed and Cat.Slice (deferred) are blocked on the
same technical issue: filling a PathP in a family
`λ i → hom-type(α i)` without hom-sets.

In Cat.Slice, the morphism type `hom/X` bundles a triangle
`emb fA ≡ target fB k`. The contraction obligation for
`compose-contr/X` requires a PathP whose base path couples the
forward singl (contractible, hence a set) with the emb fiber
(contractible by compose-contr). Extracting the PathP with a
specific base path from the canonical singl-base path requires
emb-codomain to be a set at image points — which amounts to
demanding hom-sets.

In Cat.Displayed, the total category `∫D` has the same coupling:
the compose-contr contraction must produce a PathP over both base
and displayed components simultaneously.

**Resolution paths:**
- `is-monic f` (embedding on post-composition) makes `hom/X`
  propositional, killing the PathP obligations. This suffices for
  Slice but restricts generality.
- Switching `compose-contr` to the extensional
  `fiber emb target` form (as in Cat.VirtualProposed) may
  decouple the components. Untested.
- The obstruction is orthogonal to the Weinberger program
  (Covariant, Yoneda, Cocartesian can proceed via other routes).
  Slice appears only in Beck-Chevalley and base change.

## Research notes

### VirtualAlt — noy/yon primitive (archived in Stash/)

Trades emb primacy for identity uniqueness. Binary idempotency
`yon e x e ≡ e` forces `e ≡ idn` via Kraus chain. But the
pentagon is incomplete from base axioms: face₃₅ needs
`noy-composite-coh` from a `2-coherent` record.

The fundamental tension: no single formulation achieves all three
of (unique identity, full pentagon from base, path groupoids on
arbitrary types) — though the 2026-03-14 hybrid (Cat.Type +
yon-eval + yon-idpt) comes close.

### VirtualProposed — pointwise compose-contr (deferred)

Uses `∀ w a v b → is-contr (fiber ...)` instead of Cat.Type's
function-extensional `emb s ≡ target`. Hypothesis: this
decouples base and displayed components in the Displayed/Slice
obstruction. Not yet tested — no committed module has been ported
to it.

### absorb-coh independence (monoidal)

The full Mac Lane triangle's extra field `absorb-coh`
(`monoidal-2-coherent`) is independent of the base monoidal
axioms — it demands a comparison between `tensor-interchange`
members the base never makes. The obstruction is a π₀
phenomenon (defect `ω(I,x,I,r) − ω(I,I,I,I)`, a balanced
difference that vanishes on connected carriers). The braided
hexagon and the symmetric gate `β²=id` are the π₁ analogues one
level up (unbalanced defects `−ζ` and `2ζ`); the syllepsis is the
π₁ˢ = ℤ/2 (Hopf) rung. Twist / Indiscrete formalize the algebraic
core; the concrete carriers are deferred `--cubical` islands.

## Open frontiers

- **Rezk retraction**: `decode ∘ encode ~ id` for the Rezk
  completion HIT. Approaches: J-induction with HIT interaction,
  generalized Rezk-elimination, seg∙ boundary fix.

- **Displayed resolution**: test Cat.VirtualProposed for the
  PathP decoupling hypothesis, or develop the is-monic
  specialization.

- **Duploid instance for Cat.Virtual**: bipolar classifier
  (join of pos×pos and neg×neg), lifting monad bridge,
  maximal sub-category extraction.

- **Monoidal hexagon H2**: the second hexagon (braiding of
  `x ⊗ y` past `z`). Open whether it derives from H1 by symmetry
  (object-path formulation, `⊗-braid-inv = sym ⊗-braid`) or
  needs a second field `hexagon-emb-2`.

- **VDC noy-presented**: two-sorted virtual double category
  with tight morphisms from Cat.Type and loose morphisms
  presented by noy-families. Composition = function
  composition; all structural laws trivialize.

- **Interchange propositionality**: all Cat.Type fields except
  interchange are propositional. Interchange inherits higher
  homotopy of hom types (S² counterexample via π₃≅ℤ). Open
  whether a richer emb type or Segal condition could absorb it.
