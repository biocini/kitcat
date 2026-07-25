# Stage 4 — rebuild `Cat`

The deprecated tree (49 modules, 15,545 lines, green under invariant
D8) ported onto the deductive system. The porting programme is the
design note's mechanical roadmap
(`notes/2026-07-22-deductive-system-design.md`, steps 0–7):
virtual-graph and the pairing calculus; the two-handed composable
theory with op a strict involution; the unital tier with absorption
and the representability calculus; the stability tier and its derived
theory; the bundle with morphisms and SIP; mediation and
`category = D + Med-point` with the strict-direction conservativity
comparison (the F∘G-strict pattern,
`resources/mellies-dialogue-deformation` §2); the monoidal
re-stratification onto the lax schema (R1 names it); Properties
comparisons and the legacy-parity remainder.

`Cat.Depreciated.*` is the porting reference throughout —
`Cat.Depreciated.CatData.*` for the magmoid-era material — and is
retired, not fixed. Whether anything in it survives unported is
decision D5.

## What retirement releases

- The nineteen held displaced-composition names
  ([evidence](evidence.md) census): the holds cascade —
  `₂-merge-map`, then `₂-merge`, then `₂-assoc` with its feeders
  `₂-unique`/`₂-lcoh`/`₂-rcoh` and theirs `₂-fill`/`₂-rfill`; `₁-ap`
  then `₁`; `₂-map`; `₂-commutes`, `₂-unitl`, `₂-over`, `₁-fill`,
  `₁-over`, `₂-ap`, `pathp-ends`. Residue: `comp-pathp₂` iff
  `Core.Path.Exchange` lives (decision D9).
- ≈ 300 ms of `Core.Kan`'s cold elaboration and ≈ 430 lines
  (the family), on top of Stage 2.3's sweep.
- Every other Depreciated-held surface that Stage 2 kept on the
  invariant's account.

## Acceptance

- `just check-tree src/Cat` green on the rebuilt tree; the deprecated
  namespace gone.
- The conservativity comparisons of the design note's step 5 hold
  with `⨾` preserved definitionally through the reshape (its stated
  acceptance test).
- The Stage 2.5 release executed: the family reduced to the D9
  residue, `Core.Kan` re-profiled against the band.
