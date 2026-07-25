# Unscheduled material

Carried so nothing is lost to supersession; none of it gates a stage.

## `cyl-compose`

The reference's one construction with no in-tree analogue:

```agda
cyl-compose : (φ ψ : I) (t₁ : Cyl φ A) (t₂ : Cyl ψ A)
            → composite φ t₁ ≡ base ψ t₂ → Cyl (φ ∨ ψ) A
cyl-compose φ ψ t₁ t₂ p i (φ = i1) = p (ψ ∧ ~ i)
cyl-compose φ ψ t₁ t₂ p i (ψ = i1) = p (φ ∧ ~ i)
cyl-compose φ ψ t₁ t₂ p i (i = i0) = p (φ ∧ ψ)
```

Composition problems composing: a system on `φ`, a system on `ψ`, and
an identification of the first's composite with the second's base
yield a system on `φ ∨ ψ` — `Sys` as a structure over the lattice of
face formulas, the cut of the virtual double category of tubes. Ten
`Core.Kan` sites do this inline (`cat.rfill`, `cat.bfill`,
`cat.lcoh`, `cat.rcoh`, `Path.paste-refl`, `Path.commutes`,
`pcom.lsplit`, `pcom.rsplit`, `pcom.catl`, `pcom.catr`).

Assessment of the clauses as written: they are well-formed on the
overlaps but mention only the seam path `p` — both tubes are
discarded, so the glued cylinder's composite re-transports `p` rather
than composing `t₁`-then-`t₂`. A genuine gluing would carry `t₂`'s
walls on `ψ` and admit `t₁` only through its composite (the bases
differ, so `t₁`'s tube cannot literally appear). Read as a placeholder
for the real construction. The idea is worth a design round of its
own; it is not scheduled.

## Reference questions (Lane's call)

The reference tree is notes, not expected to typecheck; repairs
involve Lane.

1. `cyl-compose`'s clauses, per the assessment above — placeholder or
   intended?
2. The reference's `hcom` (l. 109) —
   `hcom φ t p = hcomp i1 (cyl-compose φ i1 t (λ _ _ → s) p)` —
   shadows `Core.Kan.hcom` with an unrelated operation. Rename, or
   deliberate?
3. `Cyl-map-filler` is commented out with the note "Also
   definitional". It is not: `Cyl-map-composite` above it needs a real
   `hcom`, and `f` does not commute with `hcomp`. The in-tree
   `SysFunctor` correctly omits it. Correct the reference, or keep the
   historical record?
4. The `Sub`-valued filler layer (`Fill`, `composite→Ext`,
   `filler→Fill`) — keep it anywhere, or let the fan vocabulary plus
   `is-prop` carry it?

## Carried conjectures

- **The h-level development restates over the backend** —
  CONJECTURED. The level-1 instance already exists on both sides:
  `total-path-object` is Σ-closure of propositionality in fan
  vocabulary, beside `Σ-is-prop`. The open part is the tower at
  n ≥ 2, whose closure proofs (`retract→is-hlevel`,
  `Path-is-hlevel`) lean on `hcom`.
- **The unit coherences from per-hand associativity plus `idem`** —
  CONJECTURED; instance-level evidence and the open part at
  [stage-3-frontend](stage-3-frontend.md) §3.4.

Obligations O1–O6 and rulings R1–R2 live in
`notes/2026-07-22-deductive-system-design.md` and are not duplicated
here.
