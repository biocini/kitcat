# Decisions

The ledger: what each decision blocks, and what has been ruled.
Rulings land here with attribution and date, and the stage items
they touch are restated to match; until then an item carries the
decision tag.

Ruled so far: **D2** (the ternary action's home — the backend),
**N1** (`is-composable`), **N2** (`emb` backend / `reflect` frontend).

## D1 — Stage 1 scope: the instances

Do `Classify` (`U`-small classifiers, `Magma`, homotopy unordered
pairs) and `Simplex` (`AugSpx`, lists) promote with the machinery,
stay in `Cat`, or move to `Lib`? They are instances, not machinery,
have no importers, and pull `Core.Data.Trunc`/`Bool`/`Fin.Monotone.*`
into whatever namespace holds them. Blocks: the tail of Stage 1.1.

## D2 — the ternary action's home — RULED

**Ruled (Lane, 2026-07-24): the backend.** The library develops the
latent virtual-graph theory of the cubical machinery — part of
`Core.Composite`'s meaning — so `emb` and its representability
theory descend into the backend rather than living frontend-only.
Consequences: Stage 2.4 mints the general form in the backend, with
D3 ruled first (it gates the statement's currying); Stage 5 imports
the general result, no duplicated proof; `Cat.Logic` restates the
theory in the sequent vernacular by compatibility. Interacts with D7
(Tier 3 wants the lens record below `Core.Kan`).

## D3 — `emb`'s currying

Curried (matching what Core has) or uncurried through the judgment
type (representability a one-liner; the double domain-collapse
direct). With D2 ruled, this now gates the backend mint: the three
Core copies differ exactly by currying, so the general statement is
written once D3 is. Blocks: Stage 2.4's mint and Stage 3.1's field
list.

## D4 — O1 in scope?

Is O1 (propositionality of the unit tier over graph + composability
only) discharged in this arc, or does 3.5 ship with it stated as an
obligation? Blocks: Stage 3.5's label (✅ vs ⚠️ in the ledger).

## D5 — Depreciated survivors

Does anything in the deprecated tree survive rather than being
ported? A yes weakens the Stage-2 deferral account and shrinks the
Stage-4 release. Blocks: nothing before Stage 4.

## D6 — the `transp` stratum

`is-contr→is-prop` is provable from `transp` alone
([standpoint](standpoint.md)); the strata are three, and the module
cut bundles the upper two in `Core.Kan`. Is the `transp` stratum ever
reified as a module below `Core.Kan`? If yes, the descent set
includes `is-contr→is-prop` and every path-object proof that consumes
only it, and the certificate for the session-checked `primTransp`
term lands. If no, the bundling stands as an explicit choice. Blocks:
nothing in Stages 0–5; forecloses silently if undecided.

## D7 — lens-structure placement

The Kan-free lens set — records, displays, flattenings, dualities,
universality predicates ([architecture](architecture.md)) — below
`Core.Kan` per the cycle-driven rule (Layout A), or above with its
is-prop theory for module cohesion (Layout B). Layout A is the only
one in which Tier 3 can ever be stated in `Core.Kan`, and D2's ruling
strengthens its case — the backend now explicitly carries theory of
this kind. Blocks: Stage 1.2's module boundaries.

## D8 — the Depreciated invariant

Ratify: `Cat.Depreciated` remains green until Stage 4 retires it. It
is green today (59/59 under `src/Cat`) and is the porting reference;
Stage 2's deletion schedule — deletable now = `comp-pathp` alone — is
computed under this invariant. Recommended. Blocks: Stage 2.3/2.5's
deletion lists if declined.

## D9 — `Core.Path.Exchange`

The sole eventual consumer of the displaced-composition family
(two uses of `comp-pathp₂`), itself imported only by
`Test.DoubleLoopTensor` — and its `unitl refl ≐ unitr refl` seal is
the design note's Core-level anticipation of the `is-stable`
cross-hand cell. Promote it (the family keeps a root), retire it (the
family dies whole at Stage 4), or re-derive its whisker–exchange
calculus in the frontend where the design note points. Blocks: the
Stage 4 release's endpoint; Stage 5's residue collapse.

## D10 — the backend virtual-graph module

With D2 ruled, Stage 2.4 mints the graph-with-action structure and
its representability theorem in the backend, and the three emb
modules (`Core.Groupoid`, `Core.Groupoid.Virtual`,
`Core.Path.Composition` — all consumer-free after 0.1) retire. Open:
the new module's name and seat. The structure layer sits below
`Core.Kan` (`Test.RxVirtual`); the `hom≃total-representable` proof
sits above with the theory; and the discrete (path-groupoid)
instance lives either beside the general form or with `Core.Kan`.
Blocks: Stage 2.4's execution.

## N1 — the tier's name — RULED

**Ruled (Lane, 2026-07-24): `is-composable`.** It is what the design
note states throughout and what `Test.RxVirtual` already declares, so
the checked artifacts stand and the prose that drifted to
`is-composite` was amended.

## N2 — the ternary action's name — RULED

**Ruled (Lane, 2026-07-24): `emb` in the backend, `reflect` in the
frontend.** One operation under two vocabularies, agreeing
definitionally — the compatibility property in its intended use, not
a duplication to reconcile. `Cat.Logic.Type`'s existing `reflect`
field and `Test.RxVirtual`'s `emb` both stand; nothing is renamed.

## R1 — the lax variant's name (carried)

The delooped tiers' schema — deductive system minus the stability
tier's normalization, bare unit — needs its name at the monoidal
re-stratification (Stage 4 / design-note step 6).
