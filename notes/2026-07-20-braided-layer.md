# Session log — 2026-07-20 — the indiscrete/braided/twist/hexagon layer

Executing step 3 of `notes/2026-07-20-interchange-plan.md`, per the
scoping in `notes/2026-07-20-interchange-displacement.md`. All four
modules landed: `Cat.Monoidal.{Indiscrete,Braid,Hexagon,Twist}`.

## What was done

- **`Cat.Monoidal.Indiscrete`** — the ♭-form builder, per the
  2026-07-20 ruling: the builder's input IS a `monoidal-axioms₀`
  (its interchange field already flat — record field, instance
  proof, and builder input are one shape), and the builder's own
  job is purely the hom level. `⊗₁-composite` is a Π into
  contractible homs (`Π-is-hlevel Z`), so `⊗₁-interchange♭` and
  `⊗₁-unit` are `PathP-is-contr` centers, `⊗₁-spine-contr` a
  `Σ-is-hlevel Z` of them (the 2-cell a `PathP-is-contr` of a
  `PathP-is-contr`), `⊗₁-emb-⨾` an `is-contr→is-prop` path. The
  old file's per-field `htensor-*` scaffold reduces to six
  copattern clauses. First-attempt typecheck.
- **`Cat.Monoidal.Braid`** — the braided record on the new spine.
  The field-shape question flagged in the 07-20 note is resolved
  by the settled genus (the `⊗₁-interchange♭` ruling, the
  Groupoid re-founding, the Indiscrete ruling — the ♭ form at
  witness arguments is the one shape interfaces target): `braided
  (M : monoidal C)` carries `⊗₀-flank-swap♭ : rep A → rep B →
  A ▵₀ B ≡ B ▿₀ A` and its displaced mate `⊗₁-flank-swap♭` (a
  `PathP` over the level-0 lines at `⊗₁-wit`s, `(η ▵₁ ζ) →
  (ζ ▿₁ η)`), both grades in one record over the bundle as
  `is-monoidal-2-coherent` does. The flank swap stays the one
  honest datum; `⊗₀-braid♭`/`⊗₁-braid♭` compose it after the
  interchange fields (`comp-pathp₂` playing `∙` one grade up),
  and the pointwise forms are `nrm`-shadows, definitional against
  embedded factors. `braid-theory` derives the braidings by the
  unitor idiom verbatim: sealed `braid-σ●₀ : (U ●₀ V) ↝
  ⊗₀-braid♭ U V ≡ V ●₀ U`, `⊗₀-braid` its `fst`-shadow;
  `braid-σ●₁` the `⊗₁-wit-σ[_,_]` instance at the sealed lines
  threading `(Û ●₁ V̂) ↝̂ ⊗₁-braid♭ Û V̂` to `V̂ ●₁ Û`, and
  `⊗₁-braid` its `fst`-shadow — naturality of the braiding is its
  type, for free. Invertibility is free (a path in `ob`).
  First-attempt typecheck.
- **`Cat.Monoidal.Hexagon`** — `braided-coherent (B : braided M)`
  with the H1 field at both grades. Strict mixed associativity of
  the ternary orders collapses the old formulation's 416 lines of
  E₃-fiber re-nesting outright: `⊗₀-hexagon♭` is one 2-path
  `⊗₀-braid♭ U (V ●₀ W) ≡ ap (_▿₀ H) (⊗₀-braid♭ U V) ∙
  ap (G ▿₀_) (⊗₀-braid♭ U W)` — composable and parallel with no
  reassociation — and `⊗₁-hexagon♭` its square one grade up, the
  `comp-pathp₂`-composite of the whiskered `⊗₁-braid♭` lines over
  it. The derived object hexagon runs in the one propositional
  fiber over `G ▿₀ H ▿₀ F`: the left traversal is three σ-links
  (`↝`-whiskered `assoc-σ●₀`, `braid-σ●₀` at the pairing,
  `assoc-σ●₀` back), the right five — the field enters as the
  `fst`-constant move `μ` (the transport along the one-step braid
  rebent along `⊗₀-hexagon♭` and split across the `∙`), plus one
  reconciler `ρ` between the `↝` along a whiskered base line and
  the `●₀`-whisker of the transported pairing, pure `∙`/`ap`
  algebra on the characterization. `fiber-hexagon` is one
  `is-contr→is-set`, sealed; the shadow tree splits by `ap-comp`,
  lands on the named associators/braidings definitionally,
  discharges the two `refl`-shadows by `Path.unitl`, and
  straightens the compound braid by `braid●₀-nrm` (the
  `nrm-slide₀` trick, `fst` constant, strict endpoints).
  First-attempt typecheck.
- **`Cat.Monoidal.Twist`** — reshaped onto the ♭ builder and
  demoted a level: the countermodel now lives at
  `monoidal-axioms₀` (the grading isolates it), with
  `twist-monoidal = indiscrete-monoidal hom-contr Mω` carrying it
  to the full bundle untouched — which is what makes the defect a
  counterexample against the whole `monoidal`, not a level-0
  artifact. The loop family perturbs the field at witness
  arguments: `ω : rep A → rep B → A ▵₀ B ≡ A ▵₀ B`,
  `ι♭ω U V = ⊗₀-interchange♭ U V ∙ ω U V`. `Mω` shares `I`,
  `⊗₀-emb`, `⊗₀-unit`; its spine re-assembles from the base
  `⊗₀-pull-contr` (interchange-free) extended by `spine-tail`
  (imported from `Cat.Groupoid`) over the twisted line, Groupoid's
  reshape transcribed — so `_⊗₀_`, `⊗₀-emb-comp`, and the whole
  pre-side comparison chain are definitionally shared, and
  `Mω.⊗₀-emb-comp-op a b ≐ ⊗₀-emb-comp a b ∙ ιω a b`. The twist
  algebra is three whiskers over `ev-comp-op-eq` (`ap-comp`, the
  loop killed by hypothesis, `Path.unitr`, `⊗₀-coh→∙` folding the
  interchange half back), and `reduce` is `conj-cancel` on the
  same α/ζ/β skeleton as the old file.

## The hypothesis reshape (Twist)

The old triviality hypothesis was one diagonal point
(`ω I I I I ≡ refl`) because the old absorption cells routed
interchange only at the `(I,I)`-diagonal, through the unit
equivalences. The new absorption chain is spine-centered:
`⊗₀-absorb-l t` routes `⊗₀-comp-eq-post I t` for every `t`, whose
twisted form carries `ap ⊗₀-ev (ω (⊗₀-nrm I) (⊗₀-nrm t))`. The
hypothesis accordingly widens to ev-triviality along the left-unit
line — `Hω : (t : ob) → ap ⊗₀-ev (ω (⊗₀-nrm I) (⊗₀-nrm t)) ≡
refl` — while the forced loop
`ζ = happly (ω (⊗₀-nrm I) (⊗₀-nrm x)) (I , r)` sits at an
arbitrary right context `r`, strictly beyond the hypothesis (at
`r = I` the conclusion degenerates to an `Hω` instance; at general
`r` it is new). Same character as the old unit-supported loop
family, restated in the shape the new derivation actually forces.

## Cubical engineering facts (hard-won, reusable)

- **Strict mixed associativity does the hexagon's re-nesting for
  free.** `(F ▵₀ G) ▿₀ H ≐ F ▵₀ (G ▿₀ H)` and the `▿₀`-nests'
  bracketing-freedom make the H1 field's two sides composable and
  parallel as stated — the old module's `tensor-E₃`, Cell
  transports, and six `w-recon`/`v-recon` blocks have no
  transcription target at all.
- **Σ-eta keeps shadows definitional at sealed heads.** `_↝_` and
  `_●₀_` pattern-match their pair arguments, but applied to an
  opaque σ-line at a generic interval point the argument
  η-expands, so `fst ((σ i) ↝ e) ≐ σ i .fst` and
  `fst ((σ i) ●₀ W) ≐ σ i .fst ⊗₀ w` — `ap fst` of every
  whiskered sealed line lands on the named object path with no
  lemma and no unfolding.
- **Same-`fst` reconciliations are pair-paths, not σ-projections.**
  A link between witnesses with equal `fst` and `∙`/`ap`-related
  characterizations is written `λ i → (c , θ i)` with `θ` the path
  algebra; its shadow is `refl` definitionally and costs one
  `Path.unitl` at projection. No `⊗₀-repr-refl`, no prop-path, no
  seal needed — the pair's `fst` is literally constant.
- **The twisted spine re-assembly is the Groupoid pattern.** The
  pull fiber never mentions interchange, so
  `Σ-contr-contr pull-contr (λ (k , p) → spine-tail p ι')` is
  contractibility of the spine over ANY interchange line `ι'`,
  and choosing the base center makes every pre-side derived cell
  of the twisted theory definitionally the base's. `spine-tail`
  earned an export consumer outside `Cat.Groupoid`.

## Verification state

All four new modules pass (`--safe --erased-cubical`, Agda 2.9.0),
`just lint changed` clean. No existing module was touched. Cold
totals, single runs: `Indiscrete` 272 ms, `Braid` 500 ms,
`Hexagon` 866 ms (no definition over ~25 ms; only
`fiber-hexagon`, `braid-σ●₀`, and the inherited seals are opaque
— the `μ`/`ρ` links stay transparent for their definitional
shadows, to be revisited only if a displaced consumer's profile
says so), `Twist` 407 ms. Typechecks were first-attempt except
one qualified-module fix in Twist (`⊗₀-emb-comp-op` is a record
member, not a `theory₀` cell — `Mω₀` alongside `θω`).
`All.lagda.md` still deferred per the chore batch. Nothing
committed yet.

## The braided field-shape ruling

**Ruled (Lane, 2026-07-20): the flank swap is the primitive field,
at both grades, in ♭ form at witness arguments** — as landed. The
swap and the braid are interdefinable with no axiom either way
(`swap♭ = sym ι♭ ∙ braid♭`), so the fork was purely which term is
primitive; the swap wins as the minimal new datum (interchange's
half not re-stated), the instance-shaped one (an instance's
genuinely pointwise move is the swap; the braid is always
assembled), and the one H2 wants — `⊗₀-braid♭ (U ●₀ V) W` opens
with `⊗₀-interchange♭ (U ●₀ V) W`, exactly
`⊗₀-interchange-natural`'s subject, so the ι-half and swap-half
get their own coherence layers. The cost accepted: consumers
project the *braid*, which under swap-as-field is an ∙-composite
rather than a neutral. This is prospective, not measured (the
hexagon module has no definition over ~25 ms, and the seals ride
`braid-σ●₀`, not `braid♭`); if displaced-hexagon or H2 profiling
shows the ∙-projection hurting, flipping the primitive is a
mechanical refactor. Also settled: orientation
(interchange-then-swap, the old decomposition), one record over
the bundle (`is-monoidal-2-coherent` precedent), derived
braidings in `braid-theory`.

The instance model extends with one wrinkle: the swap's endpoints
transpose the factors, so the March-style conjugation transposes
its lines — `swap♭ (m , p) (n , q) = sym (λ i → p i ▵₀ q i)
∙ s m n ∙ (λ i → q i ▿₀ p i)` for pointwise swap data `s`.

## Open items
1. **H2** (braiding the composite past one object) remains neither
   field nor theorem, as in the old form — and it is where
   `ι-mult-r₁`/`ι-mult-l₁` and `⊗₁-interchange-natural` get their
   first consumer: `⊗₀-braid♭ (U ●₀ V) W` opens with
   `⊗₀-interchange♭ (U ●₀ V) W`, exactly the naturality square's
   subject. Whether H2 derives from H1 by symmetry or is its own
   field is still the open question.
2. **The displaced hexagon** (`⊗₁-hexagon` over `⊗₀-hexagon`,
   triangle₁-style leaf-for-leaf) — every level-0 line was built
   for it (sealed σ-heads, `⊗₁-wit-σ[_,_]`-ready links), but the
   two `Path.unitl` leaves need a displaced mate
   (`comp-pathp₂-unitl`, the `comp-pathp₂-rfill` recipe in
   `Core.Kan`) before the tree glues.
3. An `indiscrete-braided` builder as the instance exemplar — the
   caller supplies `⊗₀-flank-swap♭` for its object tier, level 1
   discharges from `hom-contr`. (Not the path groupoid: it has no
   monoidal structure to braid — a monoidal instance on a
   groupoid needs group-like carrier data and is its own future
   arc.)
4. The `Monoidal.Iso` port with the braiding isomorphism
   packaging — the last unported module of the plan's
   `{Twist, Braid, Hexagon, Iso, Indiscrete}` set; `_⊨₁_` and
   `⊗₁-repr-ap` gain their consumers there.
