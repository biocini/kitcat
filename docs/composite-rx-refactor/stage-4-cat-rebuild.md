# Stage 4: rebuild `Cat`

The deprecated tree (49 modules, 15,545 lines, green under invariant
D8) ported onto the deductive system. The porting program is the
design note's mechanical roadmap
(`notes/2026-07-22-deductive-system-design.md`, steps 0–7):

- virtual-graph and the pairing calculus
- the two-handed composable theory with op a strict involution
- the unital tier with absorption and the representability calculus
- the stability tier and its derived theory
- the bundle with morphisms and SIP
- mediation and `category = D + Med-point` with the strict-direction
  conservativity comparison (the F∘G-strict pattern,
  `resources/mellies-dialogue-deformation` §2)
- the monoidal re-stratification onto the lax schema (R1 names it)
- Properties comparisons and the legacy-parity remainder

`Cat.Depreciated.*` is the porting reference throughout
(`Cat.Depreciated.CatData.*` for the magmoid-era material). The tree
retires, unfixed. Whether anything in it survives unported is
decision D5.

## What retirement closes

The placement contract (D8,
[stage-2-discipline](stage-2-discipline.md) §2.5) comes due here:
this is the last moment a consumer exists to check a reformulation
against.

- The contract's two outcomes dispose of each of the nineteen held
  displaced-composition names ([evidence](evidence.md) census):
  reformulated over the disciplined `SysP` in its principled home,
  or deleted with the tree that consumed it. Reaching Stage 4 with a
  name neither reformulated nor deleted is the failure the contract
  exists to prevent. It is how a doomed tree's scaffolding acquires
  tenure in `Core`.
- ≈ 300 ms of `Core.Kan`'s cold elaboration and ≈ 430 lines
  (the family), on top of Stage 2.3's sweep.
- Every other Depreciated-held surface that Stage 2 kept on the
  invariant's account, under the same test.

## Acceptance

- `just check-tree src/Cat` green on the rebuilt tree, the
  deprecated namespace gone.
- The conservativity comparisons of the design note's step 5 hold
  with `⨾` preserved definitionally through the reshape (its stated
  acceptance test).
- The Stage 2.5 contract discharged: every held name reformulated or
  deleted, none carried on tenure. The family reduced to the D9
  residue, `Core.Kan` re-profiled against the band.
