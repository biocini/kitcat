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

A four-field presentation abstracting over both `Cat.Type` and
`Cat.Monoidal`. A category is `hom` + `idn` + a representable
embedding `emb` into `loose` morphisms + one axiom (`compose-contr`,
contractible composition fibers). All lax-substitution structure and
the Mac Lane pentagon are derived generically.

```
Cat.Codep ─── aggregator (Base + Coherence)
    ├── Cat.Codep.Base ────── 4-field record + derived carrier/action
    ├── Cat.Codep.Coherence ─ assoc + 5 pentagon faces + pentagon
    └── Cat.Codep.Instances ─ Type-codep, Monoidal-codep + checks
```

**Cat.Codep.Base** is the record. `idn` is the representable anchor —
the slot the action reads at, posited not characterized: no unit laws
or identity uniqueness are asserted or used. Composition `_⨾_` is
extracted from representability rather than primitive.

**Cat.Codep.Coherence** derives `assoc` and the full pentagon purely
from `compose-contr`/`emb-comp` — no unit law is consumed. The
inner-associator face uses the emb–act link (`act = emb @ idn`).

**Cat.Codep.Instances** derives `Type-codep` from `Cat.Type.category`
(anchor = identity morphism) and `Monoidal-codep` from
`Cat.Monoidal.monoidal` over `⊤` (anchor = tensor unit object), and
checks the generic `assoc`/`pentagon` specialize at both. This is the
noy-side structure through the pentagon; the full four-axiom wiring
(unit equivalence, unitl/unitr, emb-image-contr, unit-is-prop,
interchange/yon-eval) is a next milestone.

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
| Cat.Codep | 3 | complete | Aggregator: Base + Coherence |
| Cat.Codep.Base | 3 | complete | 4-field representable record; carrier/action derived |
| Cat.Codep.Coherence | 3 | complete | assoc + 5 pentagon faces + named pentagon (from compose-contr) |
| Cat.Codep.Instances | 3 | complete | Type-codep, Monoidal-codep; generic assoc/pentagon specialize |

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
