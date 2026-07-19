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
  needs interchange at witness composites.
- `Core.Path.Composition` compiles again (Lane filled the holes);
  revisit deferred.

## Verification state

All live modules pass (`--safe --erased-cubical`, Agda 2.9.0):
`Cat.{Type,Op,Base,Groupoid,Coherence,Terminal}`,
`Cat.Limits.{Product,Coproduct}`, `Cat.Monoidal`,
`Cat.Monoidal.{Bifunctor,Coherence}`, plus the `Core` cone including
all `Transport.Properties` importers. `All.lagda.md` is stale (Lane
deleting). `src/Test/{Probe,Probe2,Scratch}` are scratch, not gated.

## Next steps

1. **Level-1 coherence**: displace `⊗₀-pentagon` over `⊗₁-assoc` (the
   `assoc-line` technique from Bifunctor should lift the fiber pentagon
   through `⊗₁-hfiber`); then the triangle, consuming
   `monoidal-2-coherent` — first consumer of `is-⊗₀-2-coherent`, and
   the point where the `⊗₁-interchange♭` decision comes due.
2. The braided story: port `old-formulation-curried/Monoidal/`
   `{Twist,Braid,Hexagon}` onto the new spine (`absorb-coh` layer noted
   as irreducible in the old form — re-examine against the new
   naturality recipe).
3. `Cat.Monoidal.{Iso,Indiscrete}` ports; `_⊨₁_`/`⊗₁-repr-ap` gain
   their consumers here.
