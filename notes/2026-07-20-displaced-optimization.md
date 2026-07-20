# Plan — 2026-07-20 — the displaced-layer optimization pass

Ruling (Lane): before any further module work — the Properties
comparisons wait — the next session is an optimization audit of
the displaced coherence layer, in the mold of the 07-20
refinement audit. Trigger: `Hexagon` cold-checks at 13,250 ms
(single run) against its 866 ms level-0-only baseline, and
`Coherence` at ~6.3 s. The displaced hexagons were written to the
execution map faster than to the styleguide's profiling norms,
and the layer is about to become the template for everything
above it — the cost discipline has to land here first.

## Baselines to establish first

Median-of-3 cold totals (the audit's rule: totals are ~1%-stable,
per-definition attributions reshuffle freely and bill the first
forcer) for `Cat.Monoidal.Hexagon`, `Cat.Monoidal.Coherence`,
`Cat.Monoidal.{Braid,Indiscrete,Iso,Twist}`. Single-run
reference points from the landing session: Hexagon 13,250 ms
(Miscellaneous 3,818 ms), Coherence 6,297 ms (post-audit ruling
was 5,913 ms neutral — re-establish before touching).
`--profile=internal` decomposes the Misc bucket (expect ~0.3 s
import floor + signatures, occurs, positivity — `braided-coherent`
shows 119 ms — serialization, and now two level-0 section
applications per displaced module).

## Suspects, ranked by the styleguide's own rules

1. **The η-wrapped reversed side, verbatim.** Both canonical
   trees consume `(λ m → left̂ (~ m))` inline — the styleguide's
   exact inline-face pattern (measured 240→37 ms at `face-σ̂a`).
   Name the reversed line (`left̂⁻` or state `left̂` in the
   reversed orientation to begin with) in `-r` and `-l`.
2. **The l/r asymmetries as first-forcer markers.** Structurally
   identical mirrors with 3–4× cost spreads: `Θ-assoc` 418 (l)
   vs 113 (r), `fiber-hexagon₁` 865 (l) vs 559 (r), `inner̂₁`
   347 (r) vs 110 (l), `Θ` 295 (r) vs 144 (l). The spread is
   attribution, and attribution marks where conversion is forced
   first — each pair is a probe site for a missing named face or
   a cheaper stated form. Only module totals confirm.
3. **Sealing `fiber-hexagon₁` (and `fiber-pentagon₁`).** The
   level-0 fiber squares are opaque with type-directed
   boundaries; their displaced mates are transparent. The only
   consumer is the generic-point projection (`hex̂●`), whose
   endpoints are the stated `E₀`/`R₀` — available by the typed
   rule without the interior. `top̂`/`bot̂` must stay transparent
   (the `ap-comp` leaves convert `E₀`/`R₀` against the
   reindexed-glue reading, which unfolds `⊗₁-wit-∙`'s fst).
4. **The μ̂ where-block mid-spellings.** `Θ-field`'s stated RHS,
   `Θ-assoc`'s LHS/RHS, and `Θ-merge`'s LHS re-spell the two mid
   composites; naming each mid once and referencing it from both
   ascriptions is the named-face norm applied to the Θ chain.
   Risk: this is argument-position-adjacent (the styleguide's
   "not the same disease") — measure, keep only what pays.
5. **The repeated inline `fst`-shadow lambdas.**
   `(λ i → ℓ̂-assoc₁ i .fst)` and kin recur across E-chain,
   split-, whisk-, and unitl̂-cells (each definition pays its own
   elaboration). The pentagon precedent says naming glue-seam
   subterms measured null — but those were single-occurrence
   argument positions; these recur across half a dozen
   definitions. One module-level named shadow per σ̂-line, then
   measure.
6. **`wit-prop`/`is-prop→SquareP` interior.** 865 ms on the `-l`
   square; the family re-elaborates the opaque fiber square at
   `(j ∧ k, i ∧ k)` per point. Check whether the subst family's
   shape (the `∧`-connection form) has a cheaper mirror before
   ruling it the hexagon's floor.
7. **`comp-pathp₂-merge-map`'s hcom cap at the use sites** —
   `θ̂` costs 165–171 ms per link; the cap re-states both merge
   endpoints inside the hcom faces. If naming the cap faces in
   `Core.Path.Base` pays there, all four links collect it.

## Ruled structural last time — do not re-litigate blind

The pentagon glue seams (`pentagon̂●` 609 ms, `⊗₁-pentagon`),
the compound `assoc-σ●` instances (`σ̂₄₁`/`σ̂₃₂`/`σ̂₅₄`), the
monoidal loop boundary (`ĉ`), record positivity under `--safe`.
The hexagon inherits the same classes: after the suspects above
are cleared, the remainder is expected to be the same seams one
level up — record the floor honestly rather than churning
(naming single-occurrence argument-position nesting measured
*worse*).

## Method and gates

The audit's protocol: per-definition profile ranks suspects;
probes in `src/Test` isolate (a definition's in-situ number is
not its own cost); median-of-3 cold module totals are the only
confirmation; every change is semantics-preserving — boundaries
stay definitional, `Indiscrete` and all consumers re-check
untouched, `just lint changed` clean; wins and nulls both get
recorded (the styleguide gains any new rule the session proves).
