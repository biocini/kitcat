# Session log — 2026-07-19 — monoidal API, notation, naturality

Objective: diagnose the unification failures that forced the `Ω₁`/`_≡₁_`/
`⊗₁-total` shims in `Cat.Monoidal.Bifunctor`; repair the API at the root;
settle a sustainable operator notation; complete the Bifunctor's stated
scope (naturality of the associator and unitors); scaffold
`Cat.Monoidal.Coherence`.

Branch: `monoidal-visible-frames` (off `fa2188d`).

## What was done

- **Visible frames** (`7755ce7`): `⊗₁-composite` had its frames as hidden
  Πs, breaking the `Cat.Type` discipline (anonymous data belongs inside
  the context; `composite` is a visible Π). Hidden-Π-headed types get
  eta-expanded with frame metas at every inference-mode position (bare
  `_≡_`, `fiber`, Σ-bound operator variables) — the entire shim layer was
  checking-mode compensation. Frames are now visible; `_$₁_` (infixl 90)
  applies a composite with frames read off the context argument's type;
  `is-⊗₁-representable`/`_⊨₁_`/`⊗₁-nrm` moved into `tensor-representable₁`
  mirroring level 0. Every shim deleted; no proof term changed. The record
  wrapper (1lab `_=>_`-style) was evaluated and rejected: level 0 proves
  visible-Π suffices, and no stuck higher-order constraint ever fired.
- **API completion** (`e195c1d`): `⊗₁-repr-ap`; `_⨾₁_` hoisted from a
  proof-local where-block into `tensor-representable₁`; the `theory₁`
  fiber module named `⊗₁-hfiber` with `pull-contr`/`push-contr` mirroring
  `theory₀`.
- **Notation** (`ffd2741`): see conventions below. 10 files, pure token
  substitution, lemma names migrated mechanically.
- **Core upstreaming** (`0cef96e`): `comp-pathp₂` (two-base-path
  comp-pathp for a binary family) → `Core.Kan`; `Path.switch` → the
  groupoid laws in `Core.Kan`; `sq-from-∙`, `ap-fst-fiber` →
  `Core.Transport.Properties` (not `Core.Data.Sigma` — import graph).
  Bifunctor's dead `Core.Groupoid`/`Core.Transport.Base` imports removed.
- **`ap` normalization** (`9eec39a`): `Core.Kan` no longer renames
  `ap` to `cong`; the renaming existed solely to free the name for a
  `pcom` member, now `pcom.map`. `hcom-cong` keeps its name (the word is
  the property).
- **Naturality** (`1fee68b`): `⊗₁-unitl`, `⊗₁-unitr`, `⊗₁-assoc` — the
  displaced images of the level-0 identities, each a single
  `is-prop→PathP` through a line of displaced fibers. Recipe:
  `ap-fst-fiber` at the identity's defining witness path gives the
  `∙`-decomposition of its `⊗₀-emb`-image; `sq-from-∙` packages the
  square; the line's `i1`-end is the plain image fiber, so
  contractibility rides in from `⊗₁-emb-image-contr`. `⊗₁-assoc`
  exploits strict associativity of `▿₀`/`▿₁` (bracketing-free nests)
  and `comp-pathp₂` at the family `⊗₁-composite`. The old curried
  formulation spent ~500 lines on these three (E₃ fibers, Cell
  transports, `inv-coe-filler`); the new section is ~170 including
  machinery, all first-attempt typechecks.
- **Coherence scaffold** (this commit): `Cat.Monoidal.Coherence` with
  `coherence₀` — `⋉₀-coh`, `⊗₀-interchange-natural`, `pentagon⋉₀`
  (five bracketings in one propositional fiber, `fiber-pentagon` by
  `is-contr→is-set`), `assoc⋉₀-nrm`, and the object-level
  `⊗₀-pentagon`. Token transcription of `Cat.Coherence`'s pentagon core.
- **The triangle** (`f73a35b`): token transcription of
  `Cat.Coherence.triangle` under the dictionary — five witnesses on
  `A ▿₀ E ▿₀ B`, unitor faces by `⊗₀-repr-ap`, associator face
  definitionally `⊗₀-assoc x I y`, `loop-refl`/`face-a` consuming the
  2-coherence field. First-attempt typecheck.
- **`is-monoidal-2-coherent`** (`d732a74`, per Lane's direction): ONE
  extension record over the full `monoidal C` bundle, fields `is-coh₀`
  and `is-coh₁` — the levels are proved separately but travel
  together; any `monoidal C`-based record answers for both. Lives in
  `Cat.Monoidal.Coherence` (mirroring `Cat.Coherence`/`is-2-coherent`);
  `Cat.Monoidal` no longer carries a coherence record. `is-coh₁` is
  the level-0 square displaced along morphisms, via the new `theory₁`
  cell `⊗₁-emb-idn-absorb` (= `⊗₁-interchange (idn I) φ` glued to
  `⊗₁-idn-▴` by `comp-pathp₂`). The derived-theory module is now
  `coherence (M : monoidal C)` — `theory₁` in scope throughout.
- **The displaced pentagon** (`58ee03e`): `theory₁` gains the
  displaced witness calculus — `⊗₁-wit U U' η` (fiber of `⊗₁-emb`
  displaced along level-0 witness paths), `⊗₁-wit-contr` (any
  inhabitant contracts: slide its characterization along its own base
  line to the plain image fiber — `subst is-contr` at the `j ∧ i`
  connection; no nest chains needed), `_⋉₁_` (token mirror of `_⋉₀_`
  with `comp-pathp₂` for `∙`), `assoc-σ⋉₁`/`assoc⋉₁`, `⊗₁-wit-∙`.
  `Core.Kan` gains `comp-pathp₂-over` (sections glued over the `com`
  filler of `comp-pathp₂`; `fil` at `i1` is `com` definitionally).
  `Cat.Monoidal.Coherence` gains `pentagon⋉₁`: `p̂₁`–`p̂₅` the
  `⋉₁`-bracketings, `σ̂`-edges the whiskered `assoc-σ⋉₁` lines,
  `fiber-pentagon₁` by `is-prop→SquareP` over pointwise-transported
  `⊗₁-wit-contr`, hom shadow by `fst`-projection over
  `fiber-pentagon`'s shadow.

## Notation conventions (durable)

Small round glyphs are the scarcest resource in a cubical library
(`∙` paths, `·` was substitution, `●` witnesses). The substitution
calculus now uses vertical triangles — its semantic axis is over/under
(the `Cat.Type` context vocabulary), orthogonal to the horizontal
whiskering triangles `◂▸◃▹`, which stay reserved for genuine 2-cell
whiskering.

| shape | glyph | agda-input | reading |
|---|---|---|---|
| cell into over slot | `x ▴ G` | `\tb` (3rd) | operand on the slot's side fills it |
| cell into under slot | `F ▾ y` | `\tb` (4th) | over = left, under = right |
| composite into over slot | `F ▵ G` | `\tw` (3rd) | hollow = a composite fills |
| composite into under slot | `F ▿ G` | `\tw` (4th) | solid = a cell fills |
| witness pairing | `U ⋉ V` / `U ⋊ V` | `\join` (2nd, 3rd) | bar marks the head factor |
| witness transport | `U ↝ e` | `\r~` (1st) | extend along a composite path |

Grading: bare at hom level (`Cat.Type`/`Cat.Base`), `₀`/`₁` at the
tensor levels. `_$₁_` applies a level-1 composite; `_⨾₁_` is vertical
composition of hom-composites, right-normalized (second factor at the
identity frame — the form `⊗₁-emb-⨾` produces and `⊗₁-pre-comp`
consumes; the mirror, if ever needed, is the `-op` twin).

Interchange reads `⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y`; the ♭-closure is
"the hollow triangle flips": `A ▿₀ B ≡ A ▵₀ B`.

## Design decisions

- Visible Π over record wrapper for `⊗₁-composite` (transcription
  discipline; level 0 as existence proof; escalation trigger — stuck
  flex-rigid constraints — never fired).
- Flat `♭` interchange stays the level-0 field (fields-as-neutrals,
  reaffirmed from 07-14). **Open**: `monoidal-axioms₁` takes the
  pointwise `⊗₁-interchange` as its field with no `⊗₁-interchange♭`;
  decide whether level 1 wants the ♭ shape when the displaced pentagon
  needs interchange at witness composites. (The `⋉`-form pentagon did
  NOT need it — the question is now deferred to the hexagon/braid
  ports and the interchange-coherence displacement `⋉₁-coh`.)
- One coherence record over the bundle (Lane): `is-monoidal-2-coherent
  (M : monoidal C)`, fields `is-coh₀`/`is-coh₁`; downstream records
  based on `monoidal C` handle both levels.
- Circumflex marks displaced witnesses: `Û : ⊗₁-wit U U' η`, `p̂ᵢ`,
  `σ̂ᵢⱼ`, `top̂`/`bot̂` — the hat is "the level-1 lift of".
- `Core.Path.Composition` compiles again (Lane filled the holes);
  revisit deferred.

## Cubical engineering facts (hard-won, reusable)

- `hcomp`/`com` at a Σ-type does NOT project componentwise
  definitionally: `fst ∘ comp-pathp₂ (Σ-family) ≠ comp-pathp₂ (fst)`
  as a refl-check. Σ-valued glues whose `fst` must be the fst-level
  glue are ASSEMBLED as pairs — `comp-pathp₂` on `fst`,
  `comp-pathp₂-over` on `snd` — never projected. This is why
  `⊗₁-wit-∙` exists.
- `fil A φ i1 s ≡ com A φ s` IS definitional — `comp-pathp₂-over`'s
  characterization family rides the `com` filler and its lid lands on
  `comp-pathp₂` on the nose.
- PathP boundary reduction is definitional for ANY head (neutral
  included): endpoint-exactness of glued corners is free whenever the
  corner is the stated endpoint of a typed PathP. This is what makes
  the `σ̂`-edges' corners match the `p̂ᵢ` with no reconciliation.
- Do NOT state definitional facts about `com`-towers as standalone
  `refl` lemmas: conversion explodes (a `top-fst = refl` probe hung
  the typechecker). The fact still holds by construction; consumers
  just use it silently.
- **Seal prop-paths that level-1 families project.** Conversion
  whnfs both sides, so a type mentioning `(assoc-σ⋉₀ … i) .fst`
  under a generic interval binder normalizes the whole
  `is-⊗₀-representable-prop` hcom tower at fourfold-`⋉₀` arguments —
  each `σ̂` declaration cost 4–6.7 s (measured by
  `--profile=definitions`; `--profile=internal` put it all in
  `Typing.CheckRHS`). Homogeneous level-0 σ-types never project, so
  level 0 never pays. Fix: `opaque assoc-σ⋉₀` — projections stay
  neutral, comparison is syntactic, boundaries still reduce by the
  type-directed rule. 32.7 s → 3.0 s for the module. The `= refl`
  checks that genuinely need the tower (`assoc-eq`, `face-a`) sit in
  `opaque unfolding assoc-σ⋉₀` blocks. `assoc-σ⋉₁` is opaque for the
  same reason one level up (`(assoc-σ⋉₁ … i) .fst` in a future
  consumer's family would unfold `is-prop→PathP` towers).
  `fiber-pentagon` is the next candidate if a consumer's family ever
  projects it at generic points.
- Interval-typed signatures inside `monoidal`-opening modules must
  write `Core.Base.I` (the unit `I` shadows the interval).

## Verification state

All live modules pass (`--safe --erased-cubical`, Agda 2.9.0):
`Cat.{Type,Op,Base,Groupoid,Coherence,Terminal}`,
`Cat.Limits.{Product,Coproduct}`, `Cat.Monoidal`,
`Cat.Monoidal.{Bifunctor,Coherence}`, plus the `Core` cone including
all `Transport.Properties` importers (full sweep after `Core.Kan`
grew `comp-pathp₂-over`). `Cat.Monoidal.Coherence` checks in ~3 s
after sealing `assoc-σ⋉₀` (see the engineering facts).
`All.lagda.md` is stale (Lane deleting).
`src/Test/{Probe,Probe2,Scratch}` are scratch, not gated.

## Next steps

1. **Pentagon endgame** — from `pentagon⋉₁` to the `⊗₀-pentagon`-based
   `⊗₁-pentagon` (edges the `comp-pathp₂`-composites of whiskered
   `⊗₁-assoc`, over the canonical `⊗₀-pentagon`). Since `⊗₀-pentagon`
   is a `∙`-tree of six squares (`A₃`-whisker, two `ap-comp` shuffles,
   `ap (ap fst) fiber-pentagon`, one shuffle, `A₂`/`A₁`-whiskers), the
   level-1 square can be glued leaf-by-leaf with `comp-pathp₂` at the
   family `λ p p' → PathP (λ i → C.hom (p i) (p' i)) A₅ A₁` —
   `pentagon⋉₁` supplies the core leaf. Remaining: displace the
   `ap-comp` shuffles (their base is `ap fst` of fiber paths — lift
   through `⊗₁-wit` squares over `HComposite.unique`), displace
   `assoc⋉₀-nrm` (triple-J straightening; its displacement should J
   the same witness paths), and discharge the `⋉₀`-vs-nest `∙ refl`
   redexes (`Path.unitr`, as in Bifunctor's `assoc-ap`). Also relate
   `assoc⋉₁` at `⊗₁-nrm`s to `⊗₁-assoc` (the `assoc⋉₀-nrm` analogue —
   both ends are `is-prop→PathP`-style through contractible lines, so
   `is-prop→PathP-is-contr` at the `⊗₁-wit` family should give it).
2. **`triangle₁`**: displace `triangle₀` over the morphism level —
   first consumer of `is-coh₁`. The `⊗₁-wit` calculus should carry it:
   the five witnesses become `⊗₁-wit`s, the faces `⊗₁-wit`-lines, the
   loop closed by `is-coh₁`.
3. Interchange-coherence displacement: `⋉₁-coh`/`⊗₁-interchange-natural`
   over their level-0 mates — the `⊗₁-interchange♭` decision lands
   here or in the hexagon.
4. The braided story: port `old-formulation-curried/Monoidal/`
   `{Twist,Braid,Hexagon}` onto the new spine (`absorb-coh` layer noted
   as irreducible in the old form — re-examine against the new
   naturality recipe).
5. `Cat.Monoidal.{Iso,Indiscrete}` ports; `_⊨₁_`/`⊗₁-repr-ap` gain
   their consumers here.
