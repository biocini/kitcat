# Kitcat Cat.* Architecture

The Cat.* namespace has three strata organized by dependency.
Stratum 0 defines foundation records. Stratum 1 builds core
theory on Cat.Virtual. Stratum 2 is an independent magmoid-based
layer predating Cat.Virtual.

## Strata

### Stratum 0 — Foundation records

Define the core algebraic structures for categories.

```
Cat.Virtual ─── canonical: emb primitive, four axioms
    │
    ├── Cat.Classified ─── generalization: prop-classifier gates composition
    │
    ├── Cat.VirtualAlt ─── research: noy/yon primitive, emb derived
    │
    └── Cat.VirtualProposed ─── research: pointwise compose-contr variant
```

**Cat.Virtual** is the canonical record. All Stratum 1 theory
imports it. The alternatives explore different primitive/derived
splits and their consequences for identity uniqueness, pentagon
provability, and displayed category constructions.

### Stratum 1 — Core theory (built on Cat.Virtual)

```
Cat.Virtual
    ├── Cat.Base ─────── universal properties, functors, adjunctions
    ├── Cat.Coherence ── pentagon (from base), triangle (from 2-coherent)
    ├── Cat.Groupoid ─── path groupoid instance
    ├── Cat.Covariant ── covariant families (C → Type)
    ├── Cat.Yoneda ───── Yoneda lemma (via Covariant)
    ├── Cat.Product ──── product categories
    ├── Cat.Displayed ── displayed categories (blocked)
    ├── Cat.Slice ────── slice categories (blocked)
    └── Cat.Rezk ─────── Rezk completion HIT (--cubical)
```

### Stratum 2 — Magmoid theory (independent of Cat.Virtual)

An earlier, independent development using binary `yon`-based
composition on a weaker `magmoid` structure (ob + hom + yon +
yon-emb). Not connected to Cat.Virtual by any import. Provides
fine-grained algebraic vocabulary: neutrality, divisibility,
cancellability, thunkability, linearity, mediality.

```
Cat.Data.Magmoid ── base record (magmoid, virtual-graph)
    ├── Cat.Data.Base ─────── composability, associativity, neutrality
    ├── Cat.Data.Map ──────── magmoid functors (yon-natural)
    ├── Cat.Data.Het ──────── adjunctions between magmoid functors
    ├── Cat.Data.Nat ──────── natural transformations
    ├── Cat.Data.Neutral ──── neutral morphisms, loop/coloop, _≐_
    │   └── Cat.Data.Neutral.Eq ── enriched homothety _∻_
    ├── Cat.Data.Unit ─────── unit properties from is-unital
    ├── Cat.Data.Iso ──────── wild isomorphisms
    ├── Cat.Data.Eqv ──────── wild equivalences (is-biinv)
    ├── Cat.Data.Coh ──────── pentagon over associative magmoid
    └── Cat.Data.Prod ─────── product of virtual graphs
```

## Module status

<!-- machine-parseable: bin/docs-drift validates this table -->
| Module | Stratum | Status | Notes |
|--------|---------|--------|-------|
| Cat.Virtual | 0 | complete | Canonical record, four axioms |
| Cat.Classified | 0 | complete | Prop-classifier gates composition |
| Cat.VirtualAlt | 0 | research | noy/yon primitive, unique identity, pentagon incomplete |
| Cat.VirtualProposed | 0 | research | Pointwise compose-contr, untested for Displayed |
| Cat.Base | 1 | complete | Universal properties, functors, nat-trans, adjunctions |
| Cat.Coherence | 1 | complete | Pentagon from base, triangle from 2-coherent |
| Cat.Groupoid | 1 | complete | Path groupoid instance on arbitrary types |
| Cat.Covariant | 1 | complete | Covariant families, representable family |
| Cat.Yoneda | 1 | complete | Yoneda lemma for covariant families |
| Cat.Product | 1 | partial | Record complete, projection functors stuck |
| Cat.Displayed | 1 | blocked | PathP without hom-sets |
| Cat.Slice | 1 | blocked | PathP without hom-sets |
| Cat.Rezk | 1 | partial | Encode/section done, retraction missing |
| Cat.Data.Magmoid | 2 | complete | Base record (magmoid, virtual-graph) |
| Cat.Data.Base | 2 | complete | Composability, neutrality, divisibility |
| Cat.Data.Map | 2 | complete | Magmoid functors with yon-natural |
| Cat.Data.Het | 2 | complete | Adjunctions between magmoid functors |
| Cat.Data.Nat | 2 | complete | Natural transformations |
| Cat.Data.Neutral | 2 | complete | Neutral morphisms, loop/coloop structure |
| Cat.Data.Neutral.Eq | 2 | complete | Enriched homothety, _∻_ with medial |
| Cat.Data.Unit | 2 | complete | Unit properties derived from is-unital |
| Cat.Data.Iso | 2 | complete | Wild isomorphisms |
| Cat.Data.Eqv | 2 | complete | Wild equivalences, is-biinv |
| Cat.Data.Coh | 2 | complete | Pentagon type former over associative magmoid |
| Cat.Data.Prod | 2 | complete | Product of virtual graphs |

## The Displayed/Slice obstruction

Both Cat.Displayed and Cat.Slice are blocked on the same technical
issue: filling a PathP in a family `λ i → hom-type(α i)` without
hom-sets.

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
  (Displayed, Covariant, Yoneda, Cocartesian can proceed via
  other routes). Slice appears only in Beck-Chevalley and base
  change.

## Research variants

### Cat.VirtualAlt — noy/yon primitive

Trades emb primacy for identity uniqueness. Binary idempotency
`yon e x e ≡ e` forces `e ≡ idn` via Kraus chain. But the
pentagon is incomplete from base axioms: face₃₅ needs
`noy-composite-coh` from a `2-coherent` record.

The fundamental tension: no single formulation achieves all three
of (unique identity, full pentagon from base, path groupoids on
arbitrary types) — though the 2026-03-14 hybrid (Cat.Virtual +
yon-eval + yon-idpt) comes close.

### Cat.VirtualProposed — pointwise compose-contr

Uses `∀ w a v b → is-contr (fiber ...)` instead of the
function-extensional `emb s ≡ target`. Hypothesis: this
decouples base and displayed components in the Displayed/Slice
obstruction. Not yet tested — no Stratum 1 module has been
ported to it.

## Open frontiers

- **Rezk retraction**: `decode ∘ encode ~ id` for the Rezk
  completion HIT. Approaches: J-induction with HIT interaction,
  generalized Rezk-elimination, seg∙ boundary fix.

- **Displayed resolution**: test Cat.VirtualProposed for the
  PathP decoupling hypothesis, or develop the is-monic
  specialization.

- **Duploid instance for Classified**: bipolar classifier
  (join of pos×pos and neg×neg), lifting monad bridge,
  maximal sub-category extraction.

- **VDC noy-presented**: two-sorted virtual double category
  with tight morphisms from Cat.Virtual and loose morphisms
  presented by noy-families. Composition = function
  composition; all structural laws trivialize.

- **Interchange propositionality**: all Cat.Virtual fields
  except interchange are propositional. Interchange inherits
  higher homotopy of hom types (S² counterexample via π₃≅ℤ).
  Open whether a richer emb type or Segal condition could
  absorb it.
