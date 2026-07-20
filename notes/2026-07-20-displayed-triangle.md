# Session log — 2026-07-20 — the displayed triangle

Objective: the roadmap's steps 1–2 — the σ-square triangle
back-port to `Cat.Coherence`, then `triangleᴰ` over it. The
session then pivoted, at Lane's direction, into an optimization
pass over the existing proof structure: the σ-instrument
generalization (`repr-σᴰ[_]`/`⊗₁-wit-σ[_,_]`), the loop σ-spine,
and the inline-face discovery, which between them retired every
re-typing `unfolding` block in the library, halved both level-1
coherence modules, and produced `docs/styleguide.md`'s
Performance section. Getting this layer right before the next
dimension of coherence structure is the standing priority.

Branch: `monoidal-visible-frames`.

## What was done / strongest findings

- **Step 1, the back-port.** `Cat.Coherence`'s triangle is now
  the σ-square construction, a verbatim transcription of
  `triangle₀` under the grade dictionary; first-attempt
  typecheck. `Cat.Base` gained `↝-fill` (next to `_↝_`) and the
  unitor σ-lines `unitr-σ●`/`unitl-σ●` with the unitors as
  `fst`-shadows — the assoc σ-spine, third and fourth instances.
  The `assoc-eq`/`face-a` unfolding blocks are retired; the
  elementary faces moved to `Cat.Coherence.Gloss`, where
  `repr-lc` at the sealed σ-lines replaces the endpoint
  conversions the transparent unitors used to provide — the Gloss
  consumes the seals as opaque paths, no unfolding, and shares
  the main line's `triangle` type. Casualties of sealing the
  unitors: `unitr-op` (op-coh) computes through both unitor
  bodies and sits under `opaque unfolding unitr-σ● unitl-σ●`;
  `Cat.Displayed.Base`'s `unitl-ap` reads `κ₀ = unitl-σ● f`
  (the Bifunctor's `κ₀` move, one grade down).

- **Step 2, the displayed triangle.** `is-2-coherentᴰ` (field
  `is-cohᴰ`) is the displayed coherence hypothesis over
  `is-2-coherent`: a square of displayed composites over
  `is-coh`, relating the `▿ᴰ`-whiskers of `▾-idnᴰ` and
  `emb-idn-absorbᴰ` — `is-coh₁`-over-`is-coh₀` transcribed to
  the displayed grade. `comp-pathp₁-fill` (`Core.Kan`) is the
  unary sibling of `comp-pathp₂-fill`; `↝ᴰ-fill`
  (`Cat.Displayed.Base`) rides it as the displaced `↝-fill`.
  `triangleᴰ` then displaces the σ-square tree leaf-for-leaf —
  σ̂-lines, `↝ᴰ-fill` ρ̂-lines, `is-prop→SquareP` faces over the
  sealed base squares, `●ᴰ-∙` fiber triangle, `comp-pathp₁`
  glue — every interface definitional, first-attempt typecheck.

- **Generalize and specialize, never seal-and-unfold** (Lane's
  formulation). `repr-σᴰ` never used the canonical path's
  content — proof the generalization is free. `repr-σᴰ[_]`
  takes an arbitrary base identification and consumes it as a
  neutral family; `repr-σᴰ` is its instance at
  `is-representable-prop`. Every unfolding block whose only job
  was re-typing a σ-instance at a sealed head retired at once:
  `assoc-σ●ᴰ`, `unitr-σ●ᴰ`/`unitl-σ●ᴰ`, the triangle σ̂-lines.
  `⊗₁-wit-σ[_,_]` is the two-sided mirror at the monoidal grade,
  retiring the `assoc-σ●₁`/`unitr-σ●₁`/`unitl-σ●₁` blocks
  (formerly ~3 s of conversion each) and the `triangle₁` σ̂
  block.

- **The loop σ-spine, or: opacity is not a fix for structure.**
  Sealing `loop-sq` did nothing for `Ŝ` (2.95 s → 3.03 s),
  because `loop-sq`'s *statement* has the transparent
  `is-representable-prop _ r₀¹ r₀²` as its `k = i0` face — the
  type-directed boundary rule re-exposes that body to the
  `K`-family's transports regardless of the seal, and the coe
  through the family normalizes `emb-image-contr`'s tower.
  `fiber-triangleᴰ` costs 49 ms for exactly the complementary
  reason: all four faces of its base square are sealed σ-lines.
  The structural fix: the loop gets the same σ-spine as assoc
  and the unitors — sealed `σ-loop : r₀¹ ≡ r₀²` with
  `loop = ap fst σ-loop`, `loop-sq : σ-loop ≡ ap (↝ …)`, and the
  displaced `σ̂-loop` as a `σ[_]`-instance. `Ŝ` fell off the
  profile at both grades.

- **The inline-face discovery.** After the σ-work, `face-σ̂r`
  still sat at 830 ms against `face-σ̂l`'s 194 ms and the
  monoidal mates' ≤134 ms — same shape, so the gap had to be
  mechanical. `Test.FaceProbe-20260720` reproduced the whole
  cost as a syntax artifact: a fill face written inline occurs
  in the type ascription *and* in the fill argument, is
  elaborated twice, and the two elaborations are converted
  term-by-term with the face's implicits re-solved each time
  (745 ms inline vs 52 ms named, 14×). Naming the face bottoms
  (`whisker-σ̂r`/`whisker-σ̂l`/`assoc-σ̂`) at both fibered grades
  dropped every unitor/associator face off the profile. The
  sweep of all fill sites found nothing else: base-grade faces
  are ≤35 ms inline (small terms, exempt), and naming
  argument-position glue chains *redistributes* endpoint
  conversion without reducing it (`pentagon̂●` 576 ms → 677 ms
  summed — reverted). Two null experiments reverted on principle
  (sealing `repr-contrᴰ`, the glue naming).

- **Measured, final.** `Cat.Displayed.Coherence` 14.8 s →
  **6.7 s** cold (pentagon-only baseline 4.1 s; the whole
  triangle now costs ~2.6 s, largest triangle definition
  ~235 ms). `Cat.Monoidal.Coherence` **6.2 s** cold;
  `Bifunctor` + `Coherence` were 26.3 s combined before the
  pass. Net opacity *decreased*: six `unfolding` blocks retired
  against three new σ-heads (`σ-loop` at two grades, plus the
  hom unitor pair from step 1), which are load-bearing seals of
  the sanctioned kind.

- **`docs/styleguide.md` gained a Performance section** — the
  session's lessons as library-agnostic cubical Agda guidance
  (seal what families ride, boundaries survive sealing;
  generalize over the path instead of `unfolding` to re-type;
  name the faces of ascribed fills; argument nesting is not the
  disease; profile and keep only what pays), with schematic code
  for each. The width ruling (code 100) is synced there too.

## Cubical engineering facts (hard-won, reusable)

- Sealing a path-between-paths whose stated faces are transparent
  canonical paths buys nothing: the boundary rule hands the faces
  to every family over it. Seal the *faces* (give them σ-heads),
  not the square. Diagnostic: an `is-prop→SquareP` at a witness
  family is cheap iff every face of its base square is sealed or
  structural (`↝`/`ap` of a record field); one transparent
  `is-representable-prop` face costs seconds.
- A σ-instrument parameterized by its base line consumes sealed
  σ-lines as neutral families — the `opaque unfolding` re-typing
  pattern is never necessary for σ-instances and its conversion
  cost (~1.4–3.4 s per site here) is pure waste. The canonical
  instrument should be the instance, not the primitive.
- An inline term shared by a definition's ascription and its body
  is elaborated twice and converted structurally; a named,
  type-ascribed face is elaborated once and compared by name.
  This bites exactly where the term's implicits are heavy
  (`●ᴰ`/`●₁` whiskers of σ-lines); it is invisible at the base
  grades. The mirror non-fact: an argument-position term with a
  propagated expected type pays its conversions once already —
  naming its sub-terms is churn.
- `where`-block abbreviations inside `opaque` need type
  signatures (`-WMissingTypeSignatureForOpaque` under `-Werror`).

## Verification state

All pass (`--safe --erased-cubical`, Agda 2.9.0): `Core.Kan` and
the full cone — `Cat.{Type,Op,Base,Coherence,Terminal,Groupoid}`,
`Cat.Coherence.Gloss`, `Cat.Limits.{Terminal,Product,Coproduct,
Equalizer,Pullback}`, `Cat.Morphism.Iso`,
`Cat.Functor.{Adjoint,NatTrans}`, `Cat.Monoidal`,
`Cat.Monoidal.{Bifunctor,Coherence}`, `Cat.Displayed`,
`Cat.Displayed.{Base,Coherence}`, `Test.ProductSpike`.
`Data.Thin.Category` broken at HEAD independently (stale
`compose-contr`), queued with the deferred chores.
`All.lagda.md` stale (phantom imports), unrelated. Committed.

## Open questions

- `pentagon̂●` (monoidal, 576 ms) is the largest remaining
  definition: genuine endpoint conversion of the nested
  `comp-pathp₂` glue at the two-sided `Fam` — naming
  redistributes it, so a real reduction needs a different glue
  shape (or is inherent to the two-sided calculus; the one-sided
  mirror costs ~300 ms).
- The per-module `Miscellaneous` profile bucket (~2–3 s each in
  the coherence modules) is unattributed; worth understanding
  what lives there before trusting per-definition totals.

## Next steps

Ruling (Lane): getting this layer right comes before hiking up a
dimension — a session spent only on refining and optimizing what
exists is well spent.

1. Continue the refinement audit over the existing modules: the
   two open questions above, the remaining ≥200 ms definitions
   (`unitr-op`'s op-bridge at 514 ms, the pentagon σ̂/E chains,
   `↝₁-repr`/`⊗₁-repr-ap`), and any structure the audit turns up
   that wants the generalize-and-specialize treatment.
2. `●₁-coh`/`⊗₀-interchange-natural` displacement (the
   `⊗₁-interchange♭` decision point), then the hexagon/braid
   ports per the 07-19 port strategy — with the σ-spine,
   `σ[_]`-instance, and named-face disciplines from the start:
   any new canonical identification a family will ride gets a
   sealed σ-head, displaces as an instance, and enters fills by
   name.
3. `Cat.Displayed` follow-ons unchanged (∫ spike, square-level
   displaced repr calculus — the displaced
   `repr-lc`/`repr-refl`/`repr-ap`/`repr-∙`/`↝-repr`).
4. The deferred chores after the module phase: fence tagging,
   lint sweep, `Data.Thin.Category`'s `spine-contr` rename
   fallout, `All.lagda.md` sync.
