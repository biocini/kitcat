# Plan — 2026-07-20 — the Properties comparisons

The arc unblocked by the optimization pass: the
presentation-comparison material accumulated across the H2,
interchange-displacement, and Cat.Iso sessions, all of it ruled
off the spine with zero spine consumers (the
instances-prove-the-field-shape discipline). `Cat.Monoidal.
Properties` already carries the pattern: the pointwise-to-♭
interchange closures at both grades, J-towers over the embedding
fibers, living as the nontrivial direction of a presentation
equivalence. Standing discipline from the optimization pass:
chains named at level 0 from the start, never re-spelled; J is
at home here (the spine stays J-free, Properties is exactly
where the J-towers were exiled).

## The backlog, by item

1. **The hexagon swap-half comparison** (`Cat.Monoidal.
   Properties`). The anticipated consumer of
   `⊗₀/⊗₁-interchange-natural` and the `ι-mult` hypotheses —
   consumed nowhere on the spine since the full-braid H2 ruling.
   The statement: `⊗₀-hexagon-l♭`'s braid field against the
   swap-half decomposition — the six-conjugator composite of
   whiskered `ι`s that solving H2 for `s (U ●₀ V) W` leaves,
   since a `▿₀`-block in a `▵₀`-flank moves only along
   interchange lines. The hexagon-l note's shape analysis is the
   spec: same content wearing conjugators.

2. **The iso `≡`-of-types comparison.** The old double-J
   characterization of iso against the J-free `path-iso`
   package and `hom-pathp→square` — the comparison the Cat.Iso
   port dissolved to Properties material, same pattern as the
   H2 consumer story.

3. **Further pointwise-to-♭ closures.** The remaining record
   fields with pointwise-at-normal-forms mirrors (assoc,
   unitors, braid), on the `⊗₀/⊗₁-interchange♭-from` template —
   the object-grade J-tower over the fibers, the morphism-grade
   double dependent J over the graph-Σ total paths.

4. **The `_⊨₁_`/`⊗₁-repr-ap` comparisons.** Spine
   infrastructure consumed nowhere; their comparison uses were
   deferred at the Iso port. The least specified item — needs
   its statement discovered before it can be queued.

## Rulings (Lane)

- **Scope:** items 1 + 2 — the swap-half comparison as the main
  construction, the iso comparison as the self-contained
  companion. Items 3–4 queue behind; item 4 stays unqueued
  until a consumer names its statement.
- **Statement shape:** the **two-sided presentation
  equivalence**, not the one-direction `-from` closure — both
  directions plus the round-trips, the module's first genuine
  equivalence theorem. The existing `-from` closures become the
  nontrivial-direction ingredients.
- **Grades:** **both** — `⊗₀` and `⊗₁` land together, keeping
  the record modules' both-grades-mirrored discipline; the
  displaced conjugators come with the arc, so
  `⊗₁-interchange-natural` finally gets its consumer too.
- **Home for the iso comparison:** new **`Cat.Properties`**
  beside `Cat.Iso`, mirroring `Cat.Monoidal.Properties`' role
  one level down.

## Execution order

1. The swap-half decomposition stated: the six-conjugator
   composite as a named definition at `⊗₀` (chains named from
   the start), its `⊗₁` mirror over it.
2. Field ⇒ swap-half (the solve direction, both grades).
3. Swap-half ⇒ field and the round-trips, closing the
   equivalence.
4. `Cat.Properties`: the `≡`-of-types double-J characterization
   against `path-iso`/`hom-pathp→square`.

## Verification state

Items 1 + 2 executed in-session; first-attempt typecheck at both
grades (`--safe --erased-cubical`, Agda 2.9.0) after one paren
miscount, `just lint changed` clean.

Two statement-shape refinements against the plan's prose, found
at the derivation face:

- **The named decomposition is the flank-native form, not the
  solved form.** `swap-half₀.decomp` is three cells — `ap
  (_▵₀ H) (⊗₀-interchange♭ U V)` moving the `▿₀`-block into
  flank position (the only way it moves), then the two single
  flank swaps in their native slots, the strict mixed
  associativities gluing the seams. The "six-conjugator
  composite that solving leaves" is what the *bridge* traverses:
  the eight-link chain `two-step ≡ ιc ∙ decomp` routes through
  six interchange cells (`ιc`, `ιo`, `ιr`, `ιt ≡ ιw`, and the
  whiskered `ιuv`/`ιvw`/`ιuw`), consuming
  `⊗₀-interchange-natural`, `ι-mult-r₀ U V W`, `ι-mult-l₀ U V W`,
  `ι-mult-r₀ U W V`, one free naturality square (the `↝-fill`
  slide of the pairing along the braid, read through
  `Path.commutes`), and the sealed `braid-σ●₀` line. Stating the
  solved form instead would have made both directions groupoid
  algebra and left the naturality/`ι-mult` cells unconsumed —
  against the ruling's point.
- **The equivalence is one transport, not maps + round-trips,
  and the `-from` closures are not ingredients.** `cat.rfill`
  transposed and reversed is a line of paths over `ιc` from the
  braid to its swap half (`braid-fill`, every face definitional);
  the bridge pasted into fill form (`bridge-fill`) is the
  matching line from the field's RHS to the decomposition; and
  `λ j → braid-fill j ≡ bridge-fill j` is a line of *statement
  types*, so `transport` + `transport-equiv` closes the
  equivalence with round-trips for free. J appears nowhere in
  the swap-half arc; the J-closures stand untouched beside it.

Grade 1 is the construction displaced slot-for-slot:
`comp-pathp₂-rfill` for the fills, `comp-pathp₂-merge-map` at
both merges (its whisker-of-glue ends are exactly the record's
braid whiskers), `comp-pathp₂-commutes` at the `↝̂-fill` slide
(cap and com ends make the walls definitional),
`⊗₁-interchange-natural` and the `ι-mult-*₁` hypothesis squares
at their slots, reversed `comp-pathp₂-assoc` at the flattens,
the bridge glued by `comp-pathp₂` at the family of statement
lines along the base tree, the prepend retaken as one `com`
along the level-0 tube, and the displaced statement line
threaded over `transport-filler` of the level-0 line at a given
pair of object-grade proofs. No new Core cell was needed —
recasting both `ap-comp` splits as `ap-merge` links put every
seam inside `comp-pathp₂-merge-map`'s reach.

Item 2 (`Cat.Properties`) landed as mapped: `to-refl` is
`transport-refl` at the identity (native, no patch lemma),
`hom-pathp≡square` the double J with the `to-refl` conjugations
in the base line, `square→hom-pathp` the inverse transport, and
`hom-pathp≃square` the equivalence by `transport-equiv`. The
pointwise agreement of the equivalence's forward transport with
the spine's `hom-pathp→square` is not stated — it needs
`J-refl` coherences against a native com and no consumer names
it; it queues with the backlog if ever wanted.

Cold profiles: `Cat.Monoidal.Properties` 4,262 ms total
(heaviest cells `bridgê` 377 ms, `ι-slidê` 314 ms, everything
else ≤ 142 ms), `Cat.Properties` 248 ms. Hexagon and its
downstream (`Indiscrete`, `Twist`) re-check clean. `just
check-all` is blocked by the stale `All.lagda.md` (`import
Cat.Covariant` — the pre-existing deferred chore), so the
library sweep was per-module over the affected cone. Items 3–4
of the backlog remain queued.
