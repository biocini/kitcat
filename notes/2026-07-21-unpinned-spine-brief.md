# Brief — 2026-07-21 — the un-pinned spine

Design-session prompt for the deformed `monoidal-axioms₀`: the
chiral interchange split with the framing *derived*, S¹-style,
from the loop's own concatenation action. This brief distills a
long design conversation (2026-07-20/21, Lane + Claude) that a
fresh session cannot see; read it in full before touching code.
It supersedes two earlier shapes as the entry question of the LB
certification program's Phase 2
(`notes/2026-07-20-lb-certification-program.md`): the
`balanced`-as-overlay record of the ribbon-arc note, and an
intermediate "graded spine" proposal `∀ k : ℤ → is-contr
(spine[k])` which Lane ruled wrong-shaped.

## The ruling that shapes everything

**Never index by the invariant you intend to derive** (Lane,
2026-07-21). External ℤ-indexing of the spine axiom is the
annotation disease at the axiom level — the same mistake as
braid-labels on a symmetric term skeleton, one level up. The
proof that the internal form suffices is S¹ itself: nobody
grades `Ω S¹` into sectors; `loop`'s concatenation action plus
the contractible universal cover *render* `Ω S¹ ≃ ℤ` by
encode–decode. The ℤ is output, never input. Structural, never
annotated, now holds at all three levels: syntax (crossings are
binders, not labels), domain (the group is the normal form's
home, not the theory's index), axioms (one contractibility, two
chiralities, winding computed).

## The design to spike

```agda
record monoidal-axioms₀' … where
  field
    I       : C.ob
    ⊗₀-emb  : C.ob → ⊗₀-composite
    ι⁺ ι⁻   : {A B} → is-rep A → is-rep B → A ▿₀ B ≡ A ▵₀ B
              -- the two crossing chiralities / causal protocols
    pull-contr : ∀ x y → is-contr (fiber ⊗₀-emb (⊗₀-emb x ▾₀ y))
              -- the SOLE contractibility, route-independent
    ⊗₀-unit : ∀ x → ⊗₀-ev (⊗₀-emb x) ≡ x
-- ω := ι⁺ ∙ sym ι⁻  (derived loop, the protocol discrepancy)
-- NO axiom identifies ι⁺ with ι⁻ and NO route is pinned
```

Why this works — the load-bearing fact, already machine-checked
in the tree: **the current spine axiom factors**. `Cat.Monoidal.
Twist` rebuilds its perturbed spine as `Σ-contr-contr
⊗₀-pull-contr (λ (k , p) → spine-tail p ι′)` with the recorded
comment that the pull fiber never mentions interchange — so
spine-over-ANY-route is a *theorem* (`spine-tail`,
`Cat.Groupoid`), and the only content the interchange field adds
to the current axiom is pinning one route (the synchronous
identification). Un-pin it: the tensor extracts from
`pull-contr` alone; certificates over every route come free; the
route space carries ω's concatenation action; and in ribbon
instances the route components form a ℤ-torsor *by
encode–decode in the instance*. The current `monoidal` is
recovered as the strictification: the record plus one field
identifying the chiralities (a Properties-grade equivalence).
`Twist` re-reads as the deformation constructor and
`twist-reduces-to-omega` as the boundary marker for which
coherence must be stated route-generically (the `thread[_]`
norm, docs/styleguide.md — the performance idiom and the
semantic design are the same instruction).

## Exploration agenda

1. **Spike the record** (Test/ first): re-derive `theory₀` from
   `pull-contr` + `spine-tail`, cell by cell. Classify:
   route-generic (survive unchanged), route-sensitive (detect
   the chirality — these ARE the framing semantics), and the
   currently-spine-supplied cells (`⊗₀-emb-comp-op`,
   `⊗₀-emb-comp-coh` — become route-relative; audit what the
   unit-law chain and `⊗₀-coh→∙` need). This audit is the
   session's core deliverable.
2. **The winding theorem**: the S¹ group-tensor instance;
   encode–decode giving route-components ≃ ℤ from ω's action;
   confirm the record never mentions a group. (S¹ is supported;
   `--cubical` move ruled acceptable if HITs demand it.)
3. **The chirality coherence question**: what relates ι⁺ and ι⁻
   beyond "some loop"? Candidate fields: ω-multiplicativity
   against the pairings (the balancing in loop form), the flank
   interaction. Conjecture on record: one irreducible
   loop-coherence field per flank, twist θ derived (trace of ω),
   balancing a theorem by fiber projection — "normalization as
   axiom" applied to ribbon structure. Instances decide.
4. **Recovery and instances**: current `monoidal` ≃ un-pinned +
   identification (Properties); `Groupoid`/`Indiscrete` at
   ω = refl; mint the chiralities against the tangle/`Gₙ`
   reading (ι⁺/ι⁻ = over/under crossing mediations) and
   Hasegawa crossed G-sets as the cheap model.
5. **The displaced grade**: `axioms₁` un-pins identically; the
   over-any-line machinery (`spine-tail`, `↝-fill`/`↝̂-fill`,
   `⊗₁-wit-σ[_,_]`) already carries it — expect zero new Kan
   cells.
6. **Consumers** (keep them named): ∂LB's graded cut elimination
   ("one cell per winding" — now emergent, not indexed); the
   kernel's two-tier conversion boundary (definitional slack =
   the locus ι⁺ = ι⁻, i.e. Müger transparency becomes a
   *definition*); ribbon L's two binders = the two chiralities
   (the causal reading: over/under = which of value/continuation
   is prioritized — a per-interaction protocol bit, NOT a
   sort-tag; conventions pinned by oracle, never prose).

## Guardrails

Wild discipline throughout (no truncations; contractibility only
from representability). Instances prove the field shape — no
record frozen before S¹ + tangle + crossed G-sets agree on it.
One-construction: the framing exists only as a derived shadow;
if any cell stores a group element beside structure, that's the
disease. Do NOT mint `balanced` as an overlay first — the fork
(overlay posits the twist; un-pinned spine derives it) is what
this session settles. The ribbon L report's §7 phrase "split the
interchange cell into its two chiralities and grade the spine"
is to be read with "grade" = *emergent*.

## Open rulings for Lane

1. Chirality-primitive (ι⁺, ι⁻ fields) vs loop-primitive (ι, ω)
   presentation — a Properties equivalence either way; which is
   the record?
2. Where the flank swap sits relative to the chiralities
   (deformation handles the pure braid/framing; the swap moves
   factors — confirm the layering).
3. Does this supersede Phase 2's `balanced` record outright, or
   feed a residual overlay for the factor-swapping layer?
4. Home and name for the deformed record (new module vs
   `Cat.Monoidal` surgery; migration story for the spine).

## Reading list

This brief; `notes/2026-07-20-lb-certification-program.md` (the
program + kernel audit); `notes/2026-07-20-ribbon-arc.md`;
Lane's ribbon L report draft (§2 the library, §5 the scheduling
reading, §7 the work list — location with Lane);
`src/Cat/Monoidal/{Twist,Braid,Hexagon,Coherence,Properties}
.lagda.md`; `src/Cat/Groupoid.lagda.md` (`spine-tail`);
`docs/styleguide.md` (the `thread[_]` norm); ∂LB corpus at
`~/src/ocaml/lb/docs/theory/` (esp. `dlb/metatheory.md` §5–§9,
`lb/twist_asynchrony_selinger_mellies.md`).
