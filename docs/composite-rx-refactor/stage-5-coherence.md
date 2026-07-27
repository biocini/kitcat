# Stage 5: Core coherence

The refoundation of the Mac Lane coherence work for the path
groupoid, in the deductive-system shape. Precondition: Stage 4. The
restructuring away from `Cat.Depreciated`'s methods precedes this
refactor (ruled).

## The broken modules

Both committed red, both imported only by the retired
`src/All.lagda.md`:

- `Core.Path.Coherence`: triangle and pentagon by `HComposite`
  contractibility. Nine holes (after 0.3 the import failure is gone
  and the holes are the whole story).
- `Core.Coherence.Paths`: the same targets by the `E₃` representable
  fiber. Four holes, a commented `face₂₃`, a fully commented
  `pentagon`. Holds the only reference to `Core.Kan.contr-face`.

Both attack coherence by explicit cube-filling. The deductive-system
route replaces the cube-filling with coherence as paths in
contractible iterated fibers. Each hand gets its full associahedron
tower, pentagon included, consuming no interchange. `Core.Coherence.Base` already
isolates the right engine (`coh-project`, `coh-project₃`,
`coh-project-glued`) and typechecks.

## The routing

D2 is ruled (the backend, [decisions](decisions.md)). The ternary
action and its representability theory are backend material from
Stage 2.4 on. The coherence work therefore imports the general
result directly. No duplicated proof and no shape-only template.
The path groupoid is the discrete instance of the backend's
virtual-graph theory, and the associahedron route has one
statement, over it.

One consequence for the ordering. Every import this stage needs
lands at Stage 2.4, not in the frontend. The Stage-4 precondition is
therefore what the ruling always said it was. The ad hoc methods
must give way before the coherence refoundation is *sound*. The
precondition is no longer also a technical dependency. The stage
still runs last, and the reason is validation, not availability.

## Residue collapse

Tier 3 of the [standpoint](standpoint.md) (`HComposite` as an
unbiased lens) runs here if at all, once the target shape settles.
It runs only in D7's Layout A, which puts the record below
`Core.Kan`.
The displaced-composition residue left by Stage 4 (at most
`comp-pathp₂`, per decision D9) collapses onto the disciplined
`SysP` at the same time.

## Acceptance

- Triangle and pentagon for the path groupoid machine-checked,
  ledger entries in `docs/gloss.md` moved to ✅.
- `Core.Path.Coherence` and `Core.Coherence.Paths` retired or green:
  no red modules under `src/Core`, `check-tree` at 100%.
- `contr-face`'s fate resolved with its consumer's.
