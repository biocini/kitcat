# Session log — 2026-07-19 — triangle endgame

Objective: the roadmap's step 1 — `⊗₁-triangle` over
`⊗₀-triangle`, assembled leaf-by-leaf as the pentagon's, checking
first whether any face dissolves before building fillers.

Branch: `monoidal-visible-frames`.

## What was done / strongest findings

The answer to the note's gate question is: **every face
dissolves** — no displaced `repr-∙`/`repr-refl` J-forms, no
`comp-pathp₂` unitl/unitr fillers, no displaced `wr`/`wl`
shuffles. The whole family of planned fillers evaporated under
one reformulation; every proof was a first-attempt typecheck,
and the only failures of the session were performance, fixed by
the established seal.

- **The σ-square reformulation.** `triangle₀`'s middle witnesses
  are no longer the `↝`-transports `s₁`/`s₂` of the bracketings
  but the unitor-bearing pairings `sl = ⊗₀-nrm x ⋉₀ Vg`,
  `sr = Uf ⋉₀ ⊗₀-nrm y` — the `⋉₀`-whiskers of the very witnesses
  the unitors project. Each face is then the `fst`-shadow of an
  `is-prop→SquareP` witness square whose four edges are
  wit-calculus lines: the unitor faces have constant sides and
  the whiskered unitor σ-line as bottom; the associator face has
  the `ρ`-lines as sides, `assoc-σ⋉₀` as bottom, and — the
  load-bearing observation — **`is-coh₀` transposed as its base
  square** (`λ m i → is-coh₀ x y (~ i) (~ m)`: rows the two
  fibers, columns `e₁`/`e₂` reversed). The coherence field is
  consumed as an index, not rewritten along, and the displaced
  face rides `is-coh₁` at exactly the same coordinates. The old
  `assoc-eq`/`assoc-eq₁` staging and the `opaque unfolding`
  bridges are gone — `face-a` lands on `⊗₀-assoc` because its
  bottom edge *is* the sealed `assoc-σ⋉₀` line.

- **`↝-fill`/`↝̂-fill`** (theory₀/theory₁), on
  **`comp-pathp₂-fill`** (`Core.Kan`, the filler of
  `comp-pathp₂` — the same com taken as a fil). `↝-fill U e m`
  slides a witness along its transport path by the composition
  filler: fst constant, `m = i0` the witness itself (path eta),
  `m = i1` the transport `U ↝ e` (the fill's lid) — both
  definitional, so the `∙ refl`-redex that killed the naive
  `λ k → e (k ∧ ~ m)` slide never appears. This is what makes the
  `ρ`-lines possible: `ρr m = ↝-fill (⊗₀-nrm x ⋉₀ ⊗₀-nrm I)
  (▾₀-idn A) m ⋉₀ ⊗₀-nrm y` runs from `r₂` to `sr` over `e₂` with
  constant fst, and `ρ̂r` is the same term one level up. It also
  supersedes `↝-repr`'s J at a distance: `λ m → ⊗₀-repr-unique
  (↝-fill U e (~ m)) (↝-fill V e (~ m))` is a strict-endpoint
  square, though the triangle no longer needs it.

- **The unitors got the assoc σ-spine** (`Cat.Monoidal`,
  `Cat.Monoidal.Bifunctor`): sealed `unitr-σ⋉₀`/`unitl-σ⋉₀` with
  `⊗₀-unitr`/`⊗₀-unitl` their fst-shadows, and sealed
  `unitr-σ⋉₁`/`unitl-σ⋉₁` (`⊗₁-wit-σ` mates, defined under
  `unfolding` exactly as `assoc-σ⋉₁` over `assoc-σ⋉₀`) with
  `⊗₁-unitr`/`⊗₁-unitl` their fst-shadows. The unitors were the
  last canonical cells not presented as shadows of sealed
  σ-lines; `unitl-ap`'s κ becomes the sealed line itself, and the
  keystone `⊗₁-emb-image-contr` is untouched — every boundary it
  needs reduces by the type-directed rule.

- **`⊗₁-triangle`** (`triangle₁`): top edge the `comp-pathp₂` of
  `⊗₁-assoc φ ι ψ` with `λ i → ⊗₁-unitr φ i ⊗₁ ψ`, bottom
  `λ i → φ ⊗₁ ⊗₁-unitl ψ i`, glued over exactly the base tree
  `whisker-a ∙ whisker-r ∙ step₁ ∙ step₂ ∙ face-l`: the whiskers
  are `comp-pathp₂`-congruences of the displaced faces, `step̂₁`
  is a reversed `comp-pathp₂-ap`, `step̂₂` the fst-shadow of
  `fiber-triangle₁` (`⊗₁-wit-∙` glue of the `σ̂`-lines against
  `σ̂ₗ₀`, filled by `is-prop→SquareP`), and `face-l̂` closes.
  `triangle-weak̂` (mid-free) is exported separately; `face₁-r`/
  `face₁-l` are the σ̂-shadows over `ap fst σᵣ₀`/`ap fst σₗ₀`.

## Cubical engineering facts (hard-won, reusable)

- The seal discipline scales as predicted, and the profile
  pinpoints exactly who pays: unsealed, the six new wit-squares
  cost 4–10 s each (module 42.5 s). Sealing the level-0 face
  squares: 27 s. Sealing the σ-lines with sealed σ̂-mates: the
  face squares drop to ~0.3 s and the module lands at 16.0 s
  cold. The residue is `Ŝ` (4.1 s, pre-existing) plus ~2 s per
  sealed σ̂-mate — the same intrinsic cost as `assoc-σ⋉₁`
  (3.4 s in Bifunctor), paid once in the theory and amortized by
  every displaced consumer.
- A sealed σ-line is only usable at level 1 if the canonical
  vocabulary is *itself* the shadow of the seal: `face-r`'s RHS
  survives as `ap (_⊗₀ y) (⊗₀-unitr x)` precisely because
  `⊗₀-unitr` now projects `unitr-σ⋉₀`. Sealing module-locally
  while the public cell stays a raw prop-application breaks the
  definitional bridge — hence the theory-level refactor rather
  than a triangle-local one.
- `fil`'s two ends are definitional (the cap at `i0`, the com at
  `i1` — interval algebra `i1 ∧ j = j` makes the systems agree
  syntactically), which is all `comp-pathp₂-fill` and both
  `↝-fill`s need. No coherence cube, no reconciliation.

## Verification state

All pass (`--safe --erased-cubical`, Agda 2.9.0):
`Core.Kan` and its full cone — `Cat.{Type,Op,Base,Coherence,
Groupoid,Terminal}`, `Cat.Limits.{Product,Coproduct}`,
`Cat.Morphism.Iso`, `Cat.Functor.Adjoint`, `Cat.Monoidal`,
`Cat.Monoidal.{Bifunctor,Coherence}`, `Cat.Displayed`,
`Cat.Displayed.Base`, `Cat.Coherence.Gloss`,
`Test.ProductSpike`.
`Cat.Monoidal.Coherence` 16.0 s cold (`Ŝ` 4.1 s and the three
σ̂-lines ~2 s each of it); `Cat.Monoidal.Bifunctor` 10.8 s cold
(the three σ⋉₁-mates 9.2 s of it). Changes uncommitted.

## Next steps

1. Back-port the σ-square triangle to `Cat.Coherence` (hom
   level): the same `sl`/`sr`/`ρ`-line architecture transcribes
   under ob ↦ hom, with the elementary `wr`/`wl`/`repr-refl`
   faces moving to `Cat.Coherence.Gloss` beside the
   straightening's J-form. `↝-fill`'s hom-level twin belongs in
   `Cat.Base`'s theory next to `_↝_`.
2. `⋉₁-coh`/`⊗₀-interchange-natural` displacement (the
   `⊗₁-interchange♭` decision point), then the hexagon/braid
   ports per the 07-19 port strategy.
3. The displayed pentagon (`pentagonᴰ` over `Cat.Coherence`'s
   `pentagon`): needs `comp-pathp₁-ap` (the unary sibling — one
   coh-cube instead of two), the `⋉ᴰ`-glue over the deferred
   `comp-pathp₁-over`, and `nrm-slideᴰ`; then the tree
   transcribes leaf-for-leaf. `comp-pathp₁-fill` (the unary
   `↝-fill` carrier) is a two-line sibling of `comp-pathp₂-fill`
   when the displayed `↝ᴰ`-lines want it. Profile before
   sealing, as ever.
4. `Cat.Displayed` follow-ons unchanged (∫ spike, square-level
   displaced repr calculus).
