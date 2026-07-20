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

## The execution map (scoped; the hexagon session follows it)

Template: `pentagon₁` — the two-layer displacement in
`Cat.Monoidal.Coherence`, whose shapes carry over slot-for-slot.
Build `-r` first, mint `-l` as its slot-mirror in the same pass;
both consume the same three Kan cells, mirrored.

0. **`comp-pathp₂-merge`** (`Core.Path.Base`, beside `ap-merge`
   and `comp-pathp₂-ap`): the displaced `ap-merge`. `ap-merge`
   is definitionally the two-leaf tree
   `sym (Path.assoc X (ap G p) (ap G e))
   ∙ ap (X ∙_) (sym (ap-comp G p e))`, so the displaced mate is
   `comp-pathp₂` at the `Fam` family along exactly that tree:
   leaf one the reversed `comp-pathp₂-assoc` at the head line
   and the two ap-image lines, leaf two the head-whiskered
   reversed `comp-pathp₂-ap`. Both leaves exist. Where the
   `▿₁`-whiskers meet a glued line, `comp-pathp₂-map` reconciles
   whisker-of-`comp-pathp₂` with `comp-pathp₂`-of-whiskers —
   shape read off the use site, home decided there (local to
   `Hexagon` or beside `-map`).
1. **The displaced fibers** — `hexagon-r₁`/`hexagon-l₁` in
   `hexagon-theory`, each over a pair of level-0 instances
   `Q`/`Q'` at `⊗₁-wit-nrm` witnesses (the `pentagon₁` layout):
   displaced stations by `●₁`/`↝̂` over `a₁…a₄`, `c₁`, `c₅–c₇`;
   `σ̂`-lines as `assoc-σ●₁`/`braid-σ●₁` instances, `↝̂`-slid and
   `●₁`-whiskered on the level-0 sides; `μ̂`/`ρ̂` as pair-paths
   with definitionally-refl hom, `Θ`/`θ̂` the `comp-pathp₂ Famc`
   glue along the `κ`/`θ` base trees — the field whisker
   (`⊗₁-hexagon-r♭`/`-l♭` entering as the second line),
   `comp-pathp₂-assoc`, `comp-pathp₂-merge`, one displaced cell
   per base leaf; `wit-prop` by `subst is-contr` along
   `fiber-hexagon`, and
   `fiber-hexagon₁ = is-prop→SquareP wit-prop top̂ refl bot̂ refl`
   — the `pentagon●₁` closing move.
2. **The canonical trees** — `braid●₁-nrm` the `nrm-slide₁`
   one-liner beside `braid●₀-nrm`; the `step̂`-trees with
   `comp-pathp₂-ap` squares at the `ap-comp` shuffles, the
   `braid●₁-nrm` slide under `step-l₂`'s whisker, and
   `comp-pathp₂-unitl` at the two `fst`-constant links — the
   pair-path discipline is what makes the unitl leaf's endpoint
   definitional (`λ i → μ̂ i .fst` reduces to `refl`); glue by
   `comp-pathp₂ Fam` along the base trees into
   `⊗₁-hexagon-r`/`⊗₁-hexagon-l`, `PathP`s over the object
   hexagons from the glued `sym`-assoc/braid traversal to the
   whiskered-braid traversal.

Gates: first-attempt typecheck; `Indiscrete` re-checks untouched
(its builders construct the fields, not the theory); cold profile
against the `-r` 866 ms baseline; `just lint changed` clean.

## Verification state

Executed as mapped, first-attempt typecheck throughout
(`--safe --erased-cubical`, Agda 2.9.0): `comp-pathp₂-merge`,
then `hexagon-r₁` whole (fiber, both pair-path links, canonical
tree), then `hexagon-l₁` minted as its slot-mirror — each check
first-attempt.

The step-0 reconciler question settled by generalization: the
shape read off the use sites is identical at all four `μ̂`/`ρ̂`
links — the merge's tail lines are always `▿₁`-whisker images,
and the stations' characterizations carry the whisker of the
glue where the bare merge ends at the glue of the whiskers — so
it landed as one Core cell, `comp-pathp₂-merge-map` in
`Core.Path.Base` beside `-merge` (the beside-`-map` home is
unavailable: `Core.Kan` sits below `Path.Base` in the import
order): the merge at the image lines, capped at the merged end
by the reversed `comp-pathp₂-map` at the reindexed inner family
through one `hcom` in the m-direction, every boundary
definitional. The `ρ̂`-links are bare `comp-pathp₂-merge-map`
instances wrapped in the pair-path; the `μ̂`-links wrap it in the
`β₂`-whisker as the third leaf of the `Famc` glue, and the
stations' `comp-pathp₂`-built characterizations make every
leaf-to-leaf interface definitional slot-for-slot.

Cold profile: the doubled module totals 13,250 ms against the
866 ms level-0 baseline (`Coherence` cold: 6,297 ms, for scale).
Heaviest cells: `fiber-hexagon₁` 865 ms (`-l`) / 559 ms (`-r`),
`⊗₁-hexagon-l` 551 ms, the `-l` `Θ-assoc` 418 ms — in family
with `pentagon̂●` 609 ms and `fiber-pentagon₁` 209 ms one level
down the coherence ladder; level-0 definitions unchanged; no
cell pathological. `Indiscrete` re-checks untouched; the full
non-WIP library re-checks clean (the seven failures of the
`src`-wide sweep are exactly the WIP modules already commented
in `All.lagda.md`); `just lint changed` clean.
