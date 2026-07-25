# Architecture

## The namespace layout

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
  ├─ Core.Rx.Lens · .Poly · .Fibration      (but see D7)
  ├─ Core.Rx.Univalent       (--cubical)
  └─ Cat.Logic.*             virtual-graph · deductive-system · duploids
     └─ Cat.*                rebuilt
```

Dependencies run one way: `Core.Rx` is the backend, `Cat.Logic` the
frontend. The frontend states its constructions in domain vocabulary
and defines them outright where that reads better than a renaming;
because a virtual graph is a reflexive graph with extra structure,
those definitions elaborate to their `Core.Rx` counterparts on the
nose. The discipline is about theory rather than names: definitions
are free provided they land definitionally, and no lemma the backend
proves is re-derived in the frontend.

The failure mode it exists to prevent is a second copy of the
reflexive-graph theory growing inside the logic layer — the lens
machinery rebuilt, the closure calculus restated, each with the
idiosyncrasies that accrue while a development reinvents what it
already has, and the whole accretion mistaken for new work.
Definitional agreement is the safeguard against it, not an instance
of it: a construction that coincides on the nose is domain-specific
language for something already covered, and every theorem about the
covered thing applies to it unchanged. Which is why the seam's only
real error is the duplicate that agrees merely up to a path — that
one does force a second theory.

The discipline runs in reverse as well, and Stage 2 is where it
does: the backend speaks the virtual-graph language before the
frontend introduces the theory formally. An implementation already
shaped by the metatheory makes its conformance trivial to exhibit
once the theory is stated, and the development stays available for
study at that point. This is why `Core.Kan`'s restatement (Stage 2)
does not wait on `Cat.Logic` (Stage 3), and why the ternary-action
theory descending into the backend (D2) costs the layering nothing.

## The placement rule and its consequences

Placement is governed by the cycle-driven ruling: machinery sits below
`Core.Kan` unless a cyclic import forces it above.

**The forced-above set**, each with its forcing dependency:

| material | forced by |
| --- | --- |
| every path-object proof | `is-contr→is-prop` (`Core.Kan`) |
| the `po` calculus, `edge-idsys`, `edge≃path` | `Core.IdSys`, `Core.Equiv`, `Core.Transport.Properties` |
| the three `*-structure-is-prop` proofs | `Core.Equiv`, `Core.HLevel.Base` |
| `to-edge`, `coproduct`, `tensor` | `transport` (`Core.Transport.Base`) |
| `univalence.concat`/`inv` | `_∙_` (`Core.Kan`) |
| `image`, `is-univalent-family` | `_≃_`, `aut` (`Core.Equiv`) |
| `fibration-is-prop` | `Π-is-prop`, `is-contr-is-prop` |
| `Rx.Univalent` | `ua` (`--cubical`) |

**The unforced remainder** — pure interval/Σ, no cycle forces it
above `Core.Kan`: the lens records (`oplax-cov-lens`,
`lax-ctrv-lens`, `unbiased-lens`) with their `display`s, both
flattenings (`cov-flatten`, `ctrv-flatten`), `tot-op-lens`/
`tot-op-lens⁻`, the biased→unbiased conversions,
`universal-push`/`universal-pull`, and `fibration-duality`/
`fibration-duality⁻`. Placement of this set is **decision D7**:

- *Layout A (below).* `Core.Rx.Lens` below `Core.Kan` carries the
  records, displays, flattenings, dualities; their path-object and
  is-prop theory joins `Core.Rx.Properties` above. Argument: the
  cycle rule licenses it, and Tier 3 of the
  [standpoint](standpoint.md) — `HComposite` as an unbiased lens,
  stated in `Core.Kan` — is only possible in this layout.
- *Layout B (above).* `Core.Rx.Lens`/`Poly`/`Fibration` keep their
  current topic grouping above `Core.Kan`, records and proofs
  together. Argument: module cohesion; Tier 3 is deferred to Stage 5
  and may never be executed in `Core`.

`Poly` needs no decision: its lens structures consume `to-edge` in
their unitors, so the whole module sits above `Core.Transport`.

**The virtual-graph module** (D2, ruled). The backend gains the
ternary-action theory: the graph-with-action structure and its
term/coterm displays sit below `Core.Kan` (`Test.RxVirtual` certifies
the structure layer), and the `hom≃total-representable` proof sits
above with the rest of the theory. The module's name and seat — and
whether the discrete instance lives beside the general form or with
`Core.Kan` — are decision D10.

**The `rx.univalence` split.** `to-id` and `fan-contr` need only
`ap fst` and `prop-inhabited→is-contr` and stay below; `concat` and
`inv` need `_∙_` and move to `Core.Rx.Transport`. The interface module
splits across the cut — an accepted wrinkle of the stratification, to
be shaped at Stage 1 (a `univalence` module below, extended above).

## Naming

- The promotion target is `Core.Rx` (ruled: the suggestion `Rx` over
  `Graph.Refl`, Lane, 2026-07-24).
- The composability tier is `is-composable` (ruled, Lane,
  2026-07-24), matching the design note and `Test.RxVirtual`'s
  declarations.
- The ternary action is `emb` in the backend and `reflect` in the
  frontend (ruled, Lane, 2026-07-24) — one operation under two
  vocabularies, agreeing definitionally, which is the compatibility
  property in its intended use rather than a duplication to
  reconcile. Neither existing declaration is renamed.
- Compound PascalCase only in top-level module titles; kebab-case
  inside modules.

## Signature conventions

`notes/2026-07-24-refl-inference-policy.md` governs, unchanged by the
rename (Stage 1.3 re-points its examples):

- Structure parameters are implicit exactly when a later argument's
  type recovers them — record-headed (implicit), Π-domain (implicit
  for named families), projection-reached (always explicit: a family
  never determines its base).
- The edge-indexed API names endpoints explicitly; an edge does not
  determine its endpoints over constructed bases (every classifier is
  a `rx.total`; `coproduct`, `comprehension`, `codiscrete` all lose
  one). Endpoints stay implicit only where another argument pins them
  rigidly (`rx`-fields, unitors, `to-edge`).
- Levels lead signatures and are explicit exactly where un-inferable.

The bundled `virtual-graph` (ruled) loses graph inference at
display-keyed use sites — `vg-bundled.graph ?V` is a stuck projection
(measured, `Test.RxBundle`) — so the frontend interface is keyed off a
module parametrized by the structure, and cross-module signatures name
it, which is already the convention for family-keyed signatures.
