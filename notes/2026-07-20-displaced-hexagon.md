# Plan — 2026-07-20 — the displaced hexagon's true gate

Item 2 of the braided-layer queue said the displaced `⊗₁-hexagon`
waits only on `comp-pathp₂-unitl`. The unitl cell is landed, but
working the tree to its interfaces shows the gate is wider: the
`μ`/`ρ` strips force two more Kan cells before the tree glues.

## Landed

**`comp-pathp₂-unitl`** (`Core.Kan`): the displaced `Path.unitl`
for a binary family — the refl-headed `comp-pathp₂` collapses to
its second line over the base unitl squares. `Path.unitl` is the
transposed `cat.rfill` at a refl head, so the cell is the
transposed `comp-pathp₂-rfill` at the refl-headed instance, one
line, every boundary definitional. First-attempt typecheck; all
Kan consumers re-check untouched.

**The `ap-merge` alignment** (`Cat.Monoidal.Hexagon`): the
`inner`/`θ` reconcilers of all four `μ`/`ρ` links were inline
`sym (Path.assoc …) ∙ ap (E ∙_) (sym (ap-comp …))` composites —
exactly `ap-merge`, which `Core.Path.Base` already carries. All
four now call it, so the displaced tree targets one displaced
cell per reconciler instead of a two-leaf inline shape.

**The assoc/map cells** (`Core.Kan`): `comp-pathp₂-unique`
displaces `HComposite.path` for a binary family — one com along
the hfil interiors of the two base path hcoms, the displaced
cells as m-walls, every boundary definitional.
`comp-pathp₂-lcoh`/`-rcoh` displace `cat.lcoh`/`cat.rcoh` (the
`-rcoh` cap is `comp-pathp₂-rfill`, whose composite side lands
the left-nested lid), and `comp-pathp₂-assoc` is
`comp-pathp₂-unique` at those cells — mirroring `Path.assoc` =
`HComposite.unique` at `lcoh`/`rcoh` leaf-for-leaf.
`comp-pathp₂-map` is one com along the base fill towers with the
F-filler's image and the G-filler as m-walls — the binary-family
displacement of `pcom.map`. All additive: the base systems are
rebuilt locally in `where` clauses (the `-rfill`/`-commutes`
idiom), no landed module touched. First-attempt typecheck; all
Kan consumers re-check untouched.

## The finding: the μ̂/ρ̂ links must be pair-paths

The tree's `Path.unitl` leaves demand it. The displaced edge
before each unitl leaf is a `comp-pathp₂` whose first line is the
hom component of the displaced `μ̂` (resp. `ρ̂`), and
`comp-pathp₂-unitl`'s left endpoint carries the literal `refl`
there; the interface between consecutive leaves is definitional
or nothing. So `λ i → μ̂ i .fst` must *reduce* to `refl` — a
`⊗₁-wit-σ[ μ , μ' ]` line (opaque contractibility transport)
cannot feed it, and in the wild setting there is no set-fill to
discharge the characterization square behind a constant-hom pair
either: hom types are untruncated, and the fiber of
`⊗₁-wit → hom` over the constant hom is a path space in `hom`,
not a proposition. The displaced links are pair-paths
`λ i → (φ⊗₁ψ)⊗₁χ , Θ i` — the level-1 mirror of the level-0
same-`fst` discipline — and `Θ` is a genuine construction: a
square of `⊗₁-composite`-lines gluing leaf-for-leaf over the
`κ`/`θ` algebra, in the family
`Famc p p' = PathP (λ t → ⊗₁-composite (p t) (p' t)) (⊗₁-emb σc) M`
by `comp-pathp₂ Famc` along the base `∙`-tree, exactly the
`pentagon₁` idiom one level in.

## The Kan shopping list

`κ = ap (n .snd ∙_) field ∙ Path.assoc … ∙ ap (_∙ β₂) ap-merge`,
so `Θ`'s leaves need:

1. **The field whisker** — existing cells: the leaf is
   `λ m → comp-pathp₂ ⊗₁-composite (n .snd) (field m) …
   (n̂ .snd) (field₁ m)`, the level-1 hexagon field entering as
   the second line; its `m = i0` endpoint is `(n̂ ↝̂ β̂c) .snd`
   definitionally.
2. **`comp-pathp₂-assoc`** — the displaced `Path.assoc`: a square
   from `comp-pathp₂ P (comp-pathp₂ Q R)` to
   `comp-pathp₂ (comp-pathp₂ P Q) R` over the base assoc squares.
   Landed (see above): `comp-pathp₂-unique` at the displaced
   `lcoh`/`rcoh` cells.
3. **The displaced `ap-merge`** — assembled from 2 plus a
   fiberwise-map naturality cell (`comp-pathp₂-map`): the
   `●₁`-pairings' characterizations whisker *pointwise* under
   `▿₁`, and `hcom` does not commute with fiberwise application
   definitionally, so relating the whisker of a `comp-pathp₂` to
   the `comp-pathp₂` of the whiskers is a lemma, not a reduction.
   `comp-pathp₂-map` landed (see above); the assembly with 2 is
   hexagon-session material. (`comp-pathp₂-ap` covers reindexing
   along a map of the *base* only.)

Everything else is ready as the braided-layer note said: the
σ̂-lines are `⊗₁-wit-σ[_,_]` instances at the sealed heads
(`assoc-σ●₁`, `braid-σ●₁`, their `●₁`-whiskers), the core is
`is-prop→SquareP` over `fiber-hexagon` with `⊗₁-wit-∙`-glued
edges, the shuffles are `comp-pathp₂-ap` squares, and
`braid●₁-nrm` is the `nrm-slide₁` one-liner. Both trees — `-r`
and `-l` — consume the same three cells, mirrored.

## Order

~~`comp-pathp₂-assoc` first (its own session, with the displaced
`HComposite` uniqueness worked out), `comp-pathp₂-map` beside
it~~ — landed; the two displaced hexagons land together next.
