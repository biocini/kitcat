# The Composite–Rx refactor

2026-07-24. Status: **proposed**, awaiting rulings on
[decisions](decisions.md) and a focused audit of this document set.

This directory is the plan of record for the refactor. The refactor
promotes the reflexive-graph suite into `Core` and disciplines the
Kan machinery through it from `Core.Composite`'s standpoint. It then
elaborates the virtual-graph/deductive-system frontend and rebuilds
`Cat`. The ruled foundation it builds toward is
`notes/2026-07-22-deductive-system-design.md`.
`notes/2026-07-24-refl-inference-policy.md` carries the signature
conventions. `notes/2025-06-03-coherent-unit-gist.md` is provenance.

## The documents

| Document | Contents |
| --- | --- |
| [standpoint](standpoint.md) | The mathematical reformulation: the three identification tiers, the Exo boundary, the strata |
| [architecture](architecture.md) | The namespace layout, the placement rule and its forced/unforced sets, naming |
| [evidence](evidence.md) | Every measurement and census, with reproduction commands |
| [stage-0-preparation](stage-0-preparation.md) | The moves, the lift, the import fix, the guidelines chore |
| [stage-1-backend](stage-1-backend.md) | The `Core.Rx` promotion: rename, split, acceptance |
| [stage-2-discipline](stage-2-discipline.md) | `Core.Kan`/`Core.Composite` restated, deletions and dedup |
| [stage-3-frontend](stage-3-frontend.md) | `Cat.Logic`: virtual graphs, the deductive-system record |
| [stage-4-cat-rebuild](stage-4-cat-rebuild.md) | Porting `Bb.CatsWithExplicitInterchange` onto the deductive system |
| [stage-5-coherence](stage-5-coherence.md) | The Core coherence refoundation |
| [decisions](decisions.md) | D1–D10, N1–N2, R1, the decision ledger. Rulings land there |
| [unscheduled](unscheduled.md) | `cyl-compose`, the reference questions, carried conjectures |

Certificates (cited throughout by module name): `Test.RxTier1`,
`Test.RxVirtual`, `Test.RxBundle`, `Test.KanIdentities`.

## The vision

One principle organizes the library: **composition is never declared
as structure with laws. It is the projected center of a contractible
space of solutions.** Uniqueness, associativity, and Mac Lane
coherence are paths in contractible (iterated) fibers: never axioms,
never set-level truncations. This is what lets homs stay wild
(`docs/gloss.md` T12) and coherent at once. The principle appears at
three levels, and the refactor's job is to make the module structure
mirror the fact, already true at the refl level, that they are one:

- **Cubically** (`Core.Kan`, `Core.Composite`, the reference
  `Composite.lagda.md`): a composition problem is a first-class
  object (a system/cylinder with base, walls, lid), and the one
  theorem is that its solution space is contractible. `hcom` picks
  the center, `hfil` is the contraction, `J` is transport along it,
  and `transp` is the statement that type families lift
  contractibly.
- **Structurally** (`Cat.Graph.Refl`, promoted to `Core.Rx`, after
  Sterling, *Reflexive Graph Lenses*,
  `resources/sterling-reflexive-graph-lenses`): the vocabulary that
  *states* the principle: fans and cofans with centers, univalence
  as fans-are-propositions, displayed graphs, fibrations as
  contractible lifts, the lens calculus. The backend: nothing
  anywhere in the library re-implements what it encompasses. Ruled
  (D2), it also carries the ternary-action theory: the library
  develops the latent virtual-graph theory of the cubical machinery,
  part of `Core.Composite`'s meaning.
- **Logically** (`Cat.Logic`): a virtual graph is a reflexive graph
  plus `emb`, the ternary representable action. Terms and coterms
  are its two representable displays. A deductive system is a
  virtual graph plus one propositional axiom bundle: `is-composable`
  (both fibration conditions at the term and coterm displays: cut
  admissibility per hand), `is-unital` (per-hand emb-action
  equivalences plus idempotence), `is-stable` (readback as a
  contractible fiber: the NbE contract). Two hands, no general
  composition. Interchange is structure (a mediation), and
  **category = deductive system + one point of Med(D)**.

The arc, in forced order:

1. Promote the backend into `Core` and discipline the Kan machinery
   through it (Stages 0–2).
2. Build the frontend (Stage 3).
3. Rebuild `Cat` on the deductive system, with `Bb.CatsWithExplicitInterchange` as
   the porting reference until then (Stage 4).
4. Only then refound the Core coherence work (Stage 5): in the
   deductive-system shape, with the path groupoid as the canonical
   discrete instance (`pcom` as its `emb`) and `Core.Kan` as the
   worked example of the composability tier.

The telos is the LB certification program
(`resources/mellies-ribbon-tensorial-logic`,
`notes/2026-07-20-lb-certification-program.md`): coherence from
contractibility, machine-checked end to end.

## Governing rules

Rulings, with attribution:

- **Frontend/backend compatibility** (Lane, 2026-07-24). A virtual
  graph is a reflexive graph with extra structure, so the logic
  layer's constructions elaborate to their `Core.Rx` counterparts on
  the nose. The frontend therefore names and defines freely in
  domain vocabulary. What it does not do is re-derive theory the
  backend already proves, since every `Core.Rx` lemma applies to a
  virtual graph without a bridge. Definitions must land
  definitionally: agreement only up to a path would force exactly
  the bridge the layering exists to avoid. The discipline also runs
  in reverse. The backend may speak the virtual-graph language
  before the theory formally arrives, since an implementation
  already shaped by the metatheory makes its eventual conformance
  trivial to exhibit.
- **Cycle-driven stratification** (Lane, 2026-07-24). Machinery
  offloads from `Core.Rx` into Properties-style modules *when cyclic
  imports force it*, not by a-priori topic. Placement above
  `Core.Kan` requires a forcing cycle.
  [architecture](architecture.md) records the forced set and the
  unforced remainder (decision D7).
- **Bundled virtual graph** (Lane, 2026-07-24). `virtual-graph`
  contains its reflexive graph as a field and re-exports the domain
  names (`ob`, `hom`, `term`, `coterm`, …). `Test.RxBundle` measures
  the inference cost, and keying the interface off a module
  parametrized by the structure mitigates it.
- **`is-unital`'s shape** (Lane, 2026-07-24). The design note's
  emb-action, per-hand form is the record's form. The gist's
  `is-coherent-unit` is provenance and comparison material only.
- **The ternary action descends** (Lane, 2026-07-24; decision D2,
  ruled). The backend carries the virtual-graph theory: the library
  develops the cubical machinery's latent virtual-graph theory
  explicitly, part of `Core.Composite`'s meaning. The frontend
  restates it in the sequent vernacular by compatibility.
- **Order** (Lane, 2026-07-24). The restructuring away from
  `Bb.CatsWithExplicitInterchange`'s methods precedes the Core coherence refactor.
- **Reference tree** (Lane, 2026-07-24). `reference/` is notes, not
  expected to typecheck. Repairs involve Lane
  ([unscheduled](unscheduled.md)).

Standing library law that binds every stage: wild homs (never
truncate), the one-construction principle (define displaced cells as
projections, never bridge two constructions), generic lemmas
extracted rather than re-derived in place, `-Werror` green, commit
only on instruction.

Invariant (decision D8, ruled): **`Bb.CatsWithExplicitInterchange` remains green
until Stage 4 retires it, and what `Core` holds on its account
carries a placement contract.** The tree is green today (59/59 under
`src/Cat`) and its greenness is instrumental: it is the porting
reference and the check-against for reformulated constructions,
never a constraint on `Core`'s shape. Material kept in `Core`
because the deprecated tree consumes it must therefore answer, per
name and before Stage 4, whether it has a theoretical placement in
the disciplined `Core`. Reformulate it in its principled home if so.
Delete it with the scaffolding if not
([stage-2-discipline](stage-2-discipline.md) §2.5).

## What the refactor yields

The Kan/path/groupoid cluster is ≈ 3,200 lines today (`Core.Kan`
1,324, `Core.Groupoid` 618, `Core.Groupoid.Virtual` 213,
`Core.Path.Composition` 512, `Core.Composite` 161, plus dead
surface). Under the plan it lands near ≈ 1,600: dead surface −120,
the displaced-composition family −430 at Stage 4, the alias
collapse, and the emb deduplication with three module retirements.
Elaboration is neutral through Stages 0–2 (measured,
[evidence](evidence.md)) and ≈ 300 ms cheaper after Stage 4. The
statement the smaller Core makes is the program's: `transp`
exhibited as the fibration witness over `discrete A`, the same
certified shape as the frontend's `is-composable`. Stage 5's
coherence work and the frontend's associahedron towers therefore
share one contractibility engine.
