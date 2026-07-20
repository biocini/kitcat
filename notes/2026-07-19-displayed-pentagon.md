# Session log — 2026-07-19 — the displayed pentagon

Objective: the roadmap's step 3 — `pentagonᴰ` over `Cat.Coherence`'s
`pentagon`, riding the named `∙`-tree leaf-for-leaf.

Branch: `monoidal-visible-frames`.

## What was done / strongest findings

The transcription dictionary held exactly: `Cat.Monoidal.Coherence`'s
`pentagon₁` under `⊗₁-wit ↦ is-representable[_]`, `⋉₁ ↦ ●ᴰ`,
`comp-pathp₂* ↦ comp-pathp₁*`, two-sided ↦ one-sided. Every proof
was a first-attempt typecheck; the only work after transcription was
performance, resolved by the staged seals.

- **The three staged instruments, all one-construction moves.**
  `comp-pathp₁-over` (`Core.Kan`) is the unary sibling of
  `comp-pathp₂-over` — the section glued over the com filler of
  `comp-pathp₁` itself. `comp-pathp₁-ap` (`Core.Path.Base`) is the
  displaced `ap-comp` at a unary family — one `HComposite.coh` cube
  instead of two. `●ᴰ-∙` (`Cat.Displayed.Base`, the staged
  witness-line gluer) assembles the Σ from `comp-pathp₁` on homs and
  `comp-pathp₁-over` on characterizations, so the hom component of a
  glued witness line *is* the reindexed `comp-pathp₁` by
  construction — the property every shuffle leaf consumes.

- **`Cat.Displayed.Coherence`** (new): `pentagon●ᴰ` displaces the
  five bracketings by fourfold `●ᴰ`, the σ-edges by `●ᴰ`-whiskered
  `assoc-σ●ᴰ` lines, glues `top̂`/`bot̂` by `●ᴰ-∙`, and fills the
  square by `is-prop→SquareP` at pointwise-contractible displayed
  witness spaces — one transported `repr-contrᴰ` from the `p̂₅`
  corner, exactly the `⊗₁-wit-contr` move. `nrm-slideᴰ` is the
  connection slide on the displayed characterization; `assoc●ᴰ-nrm`
  lands on `assocᴰ` definitionally at `m = i1` because `assocᴰ` *is*
  `assoc●ᴰ` at `nrm[_]`s. `pentagonᴰ` then glues one displaced leaf
  per base leaf over exactly `whisker₃ ∙ pentagon● ∙ whisker₂ ∙
  whisker₁`, every interface definitional.

- **The seal architecture transfers, and the profile pinpoints who
  pays.** Unsealed, the module cost 248.7 s cold, with 173.5 s in
  `pentagon̂●` alone — conversion re-normalizing the transparent
  `fiber-pentagon` inside the glue's base paths. Sealing
  `fiber-pentagon` (`Cat.Coherence`, `opaque`, the monoidal
  rationale verbatim): 79.8 s, `pentagon̂●` → 6.1 s. The residue sat
  in `ẑ` (12.9 s) and the σ̂-lines (~5 s each): comparing their
  ascribed families over `assoc-σ●` against `repr-σᴰ`'s families
  over `is-representable-prop` forces the unfolding. Sealing
  `assoc-σ●` (`Cat.Base`) with `assoc-σ●ᴰ` under `opaque unfolding
  assoc-σ●` — the `assoc-σ⋉₁`-over-`assoc-σ⋉₀` architecture — lands
  the module at **4.1 s cold**, every definition ≤ 0.26 s.

- **The seal's only casualties were the two legacy triangle cells.**
  `Cat.Coherence`'s pre-σ-square `assoc-eq = refl` and `face-a` are
  refl-conversions through `assoc-σ●`'s body; both now sit in
  `opaque unfolding assoc-σ●` blocks. The σ-square back-port will
  retire them. Nothing else in the library needed unfolding: every
  other consumer projects or indexes the sealed heads, and endpoints
  reduce by the type-directed rule.

- **Notation: `⋉`/`⋊` → `●`/`○`** (fwd and op), repo-wide in `src/`
  (~530 sites, zero collisions). The bowtie glyphs are the Unicode
  semidirect-product operators and misled in live use; the circles
  carry no such reading. Session notes keep the old glyphs as
  historical record.

## Cubical engineering facts (hard-won, reusable)

- Plain ``` fences in `.lagda.md` **are** typechecked by Agda 2.9's
  markdown mode: the "fenced-off" triangle module in `Cat.Coherence`
  was live all along — its `assoc-eq = refl` is what surfaced the
  seal's first conversion failure. Fencing without a language tag is
  not a way to disable code.
- A seal placed *below* an unfolding consumer is invisible to
  everyone above it: `assoc-σ●ᴰ` re-seals over `unfolding assoc-σ●`,
  so its consumers (the σ̂-lines, `●ᴰ-∙` glues, both pentagons) never
  see `is-representable-prop` at all. The 60× on this module is that
  invisibility, measured.
- `--profile=definitions` needs the module's `.agdai` deleted;
  `touch` does not invalidate (source-hash check).

## Verification state

All pass (`--safe --erased-cubical`, Agda 2.9.0):
`Core.{Kan,Path.Base}` and the full cone —
`Cat.{Type,Op,Base,Coherence,Groupoid,Terminal}`,
`Cat.Coherence.Gloss`, `Cat.Limits.{Product,Coproduct}`,
`Cat.Morphism.Iso`, `Cat.Functor.Adjoint`,
`Cat.Monoidal`, `Cat.Monoidal.{Bifunctor,Coherence}`,
`Cat.Displayed`, `Cat.Displayed.Base`,
`Cat.Displayed.Coherence` (new), `Test.ProductSpike`.
`Cat.Displayed.Coherence` 4.1 s cold. `All.lagda.md` remains stale
(phantom imports), unrelated. Changes uncommitted.

## Next steps

1. The σ-square triangle back-port to `Cat.Coherence` (hom level),
   now also retiring the `assoc-eq`/`face-a` unfolding blocks; the
   elementary faces move to `Cat.Coherence.Gloss` beside the
   straightening's J-form. `↝-fill`'s hom-level twin belongs in
   `Cat.Base`'s theory next to `_↝_`.
2. The displayed triangle (`triangleᴰ` over the back-ported
   σ-square tree): the face squares are `is-prop→SquareP` at
   displayed witness families over their base mates, the `ρ`-lines
   ride `comp-pathp₁-fill` (the unary `↝-fill` carrier, a two-line
   sibling of `comp-pathp₂-fill` when `↝ᴰ`-lines want it).
3. `●₁-coh`/`⊗₀-interchange-natural` displacement (the
   `⊗₁-interchange♭` decision point), then the hexagon/braid ports
   per the 07-19 port strategy.
4. `Cat.Displayed` follow-ons unchanged (∫ spike, square-level
   displaced repr calculus).
