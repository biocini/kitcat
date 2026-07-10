# Kitcat Theoretical Lexicon (Cat.*)

The canonical vocabulary of the `Cat.*` namespace. STYLEGUIDE.md
governs formatting and casing; this document governs what the
theory's concepts are *called*. Scope: `Cat.*` only — `Core.*` and
everything outside is settled and serves as the style baseline
(conciseness, kebab-case, abbreviation register) that `Cat.*` names
must match.

Decisions recorded here were settled in the 2026-07-09 lexicon
workshop. Renames marked *at refactor* apply when `Cat.Type` /
`Cat.Monoidal` are re-expressed over `Cat.Codep`; renames marked
*now* apply immediately to the go-forward `Cat.Codep.*` surface.

## Principles

1. **Conventional first.** Where the concept is conventional, use
   the literature's name (source noted per entry).
2. **House names only for new things.** A coinage is legitimate
   only where the literature has nothing to reuse.
3. **Zero placeholders.** A name that is neither conventional nor
   an earned coinage gets renamed.
4. **One concept, one name.** Where the `Cat.Type` / `Cat.Monoidal`
   / `Cat.Codep` triplication drifted, the `Cat.Codep` spelling
   survives; "composite" abbreviates to `comp`.
5. **Degeneracy in witnesses, never fields.** Instantiation
   artifacts (⊤-quantifiers, curry glue) may appear in anonymous
   specialization witnesses, never in record fields or generic
   statements.
6. **Closed suffix system.** Law names are built from the suffix
   set below, not invented per-lemma.
7. **Core compatibility.** When choosing between candidates, prefer
   the one Core already uses for the analogous operation.

## Carriers and actions

| Term | Meaning | Status |
|---|---|---|
| `ob`, `hom` | objects, hom-types | conventional (CT) |
| `idn` | identity morphism | conventional abbrev. |
| `emb` | the representation primitive `hom x y → composite x y`; an embedding by `emb-image-contr` | house, **settled** (Lane) |
| `pre f` | the pre-slot action `f ⨾_` — precomposition with f | conventional; **replaces `noy`** |
| `post f` | the post-slot action `_⨾ f` — postcomposition with f | conventional; **replaces `yon`** |
| `compose-contr` | contractibility of the representation fiber over a composite — the first of the five `codep-axioms` fields | house (canonical spelling; `tensor-compose-contr`, `composable-contr` variants die at refactor) |
| `codep-structure` | trilayer layer 1: operations `hom`/`idn`/`emb`, the two actions `pre`/`post`, + all axiom-free derived (carrier, `composite`, `_·_`, `is-representable`) — no laws | house (Group-on split, 2026-07) |
| `codep-axioms` | trilayer layer 2: the five axioms — `compose-contr`, `interchange`, `post-eval`, `unit-eqvl`, `unit-eqvr` — plus extraction (`_⨾_`, `emb-comp`, laws), over a structure value | house |
| `codep-category` | trilayer layer 3: the universe-ranging bundle — fields `ob`/`structure`/`axioms`. The axioms are complete, so the bundle IS the category: `Cat.Type.category ≅ codep-category` | house (bundled object) |
| `coupling-laws`, `unit-laws` | the bundle-gated derived-law modules (`(C : codep-category o h)`): coupling → `post-comp`/`comp-eq`/`idem`/`pre-comp`; unit → absorption, `unitl`/`unitr`, `unit-is-prop` | house (kebab, 2026-07) |
| `idem-from-coupling` | the provenance lemma: `idem` derivable from `compose-contr`+`interchange`+`post-eval` alone — its explicit hypothesis list machine-checks non-usage of the unit axioms | house (the record-boundary guarantee, now a theorem) |
| `binder`, `pass`, `fam`, `at`, `acted`, `ctx` | the codep carrier decomposition; `at` re-anchors a passenger (definitionally idempotent) | house (the re-anchoring mechanism has no CwF analogue — CwF posits substitution, codep derives it) |
| `unit` | the canonical binder-point `unit y = (y , idn y)` — what `at` re-anchors to; `unit-eqvl`/`unit-eqvr` assert its actions invertible | house (was `idn-b`; the `-b` plumbing tier is retired — `fam-b` inlined into `fam`, 2026-07-09 modularity pass) |
| `sub`, `_·_` | substitution on contexts / codependent application | conventional (CwF) |
| `act` | the derived lax action `emb g` at the identity context | house (Petrakis's dep-application, codependent side) |
| `composite` | the represented Π-type `(γ : ctx x y) → fam (γ .fst)`. An element is a FORMAL composite: for any candidate context relating x and y, a `fam` witness. Replaces `loose` | house (Lane); continuous with Core.Kan |
| `is-representable` | the tightness predicate `fiber emb F`: one name generates F at every context (the free-theorem clause). Subsumes the composite witness (`f ⨾ g => h` = its point at `emb f · g`); its h-level under accrued structure IS the h-level shift. Axiom schema: a designated composite is contractibly representable | house/conventional — the central predicate |
| loose | RESERVED — not currently a code identifier. Designates the future VDC layer's context-witnessed cells (single `α : fam γ` over one context, PathP-shaped, composition gated on context alignment) — the original vision's loose cells. Do not reuse for anything else | conventional (equipment), reserved for its honest referent |
| tight | prose synonym (equipment analogy) for a representable composite; the code notion is `is-representable`. NOT a synonym for `hom` — `hom≃representable` (`hom ≃ Σ F, is-representable F`) is the unconditional total-space equivalence; the unit fragment supplies `is-representable-prop`, which upgrades its READING to a subtype inclusion (names-are-tight) | conventional prose, anchored to code |
| `𝟙` | the monoidal unit object | conventional; **replaces `I`** (which collided with the cubical interval and forced `hiding (I)`) |
| `_⊗_`, `⊗-assoc`, `⊗-unitl`, `⊗-unitr`, `⊗-braid` | binary tensor API | conventional notation |

## Coherence tower

| Term | Meaning | Status |
|---|---|---|
| pentagon, triangle, hexagon, syllepsis | the Mac Lane / Joyal–Street / Sojakova coherence identities | conventional |
| `E₃`, `E₄`, `E₃-contr`, `E₄-contr` | n-ary composite target fibers and their contractibility | house (code-only; the prose "Eₙ rung" usage is retired — coherence *levels* are named by their identity: triangle, hexagon, syllepsis) |
| `triangle-coherent` | record supplying `absorb-coh`, completing the full Mac Lane triangle | house; **replaces `2-coherent`** (and `monoidal-2-coherent`, which dies at refactor) |
| `hexagon-coherent` | record supplying `hexagon-emb`, completing H1 | house; **replaces `braided-coherent`** |
| `absorb-coh`, `hexagon-emb` | the irreducible fields (paid coherences) | house |
| `faceᵢⱼ`, `σᵢⱼ` / `αᵢⱼ` | diagram-edge scheme: σ = fiber-level path, α = `ap fst σ` | house scheme, preserved verbatim |
| `assoc-σ`, `hom-identity` | the E₃ fiber path; the projected fiber-level identity | house, uniform (the `path` holdout in `Core.Coherence.Paths` conforms when finished) |
| free vs field | a coherence is *free* when its diagram sits in one contractible fiber; a *field* when it crosses fibers | house methodology term |

## Unit / identity fragment

| Term | Meaning | Status |
|---|---|---|
| `absorb-l`, `absorb-r` | identity absorption (`pre idn ≡ id`, `post idn ≡ id` pointwise) | house, already uniform |
| `unitl`, `unitr` | unit laws | conventional; matches Core's path-groupoid law names (`idl`/`idr` divergence from 1lab is deliberate) |
| `post-eval` | `post f idn ≡ f` — evaluation at the identity recovers the morphism | **replaces `yon-eval`** |
| `idem` | binary idempotency `idn ⨾ idn ≡ idn`, from `idem-from-coupling`. `post-idpt` is now inlined (it is `pe (idn x)` inside the lemma) — no standalone Codep symbol | house; survives as Cat.Type's `yon-idpt` until the refactor renames it |
| `unit-eqvl`, `unit-eqvr` | the two unit-equivalence axioms `is-equiv (pre idn)` / `is-equiv (post idn)` (in `codep-axioms`) | **rename** of `unit-l-equiv`/`unit-r-equiv`; matches `Cat.Type`'s `C.unit-eqvl`/`C.unit-eqvr` |
| `unit-is-prop` | identity uniqueness (Kraus chain: binary hypothesis, `e² = e`, involutions excluded) | house (bare spelling survives; `tensor-` prefix dies at refactor) |
| `interchange` | the pre- and post-actions commute (the profunctor coupling) | house |
| Kraus chain | the idempotent-equivalence uniqueness argument | house attribution label (technique after N. Kraus; not his term) |

## Classified / virtual

| Term | Meaning | Status |
|---|---|---|
| **virtual** | *restricted meaning*: classifier-gated composition — composites exist only virtually (when classified). `Cat.Virtual` keeps the name; the **general theory is no longer called virtual** (it is the representable codependent theory, RCC). Honest echo of Cruttwell–Shulman VDC partiality; not the VDC notion itself | house, restricted 2026-07-09 |
| `classifier` | propositional gate on composable pairs | house (nearest literature: duploid polarity) |
| duploid, polarity, thunkable | the intended application vocabulary | conventional (Munch-Maccagnoni) |

## Prose theory terms

| Term | Meaning | Status |
|---|---|---|
| wild / untruncated | no hom-truncation hypotheses, ever | conventional (HoTT community) |
| representable codependent (RCC) | the general theory: Petrakis's codependent side + representability + coherence-via-contractibility | house framing over conventional pieces (Petrakis arXiv:2303.14754) |
| composite-centric | `_⨾_=>_` (the composite witness) as primary notion, bare `≡` last resort | house |
| passenger / acted | the slot decomposition: inert left data vs the single acted slot | house |
| re-anchor | the `at` operation (prose name) | house |
| coherence-via-contractibility | the engine: `is-contr→is-n-type` on representation fibers | house label (Joyal–Kock lineage) |
| h-prefix (`htensor`, `hpre`, `hpost`) | *hom-tier* (morphism-level) lift of an object-tier operation — not "higher" | house, meaning fixed here |

## Rename table (settled 2026-07-09)

| Old | New | Where | When |
|---|---|---|---|
| `noy` / `yon` | `pre` / `post` | `Cat.Codep.*` | now |
| `noy` / `yon` | `pre` / `post` | `Cat.Type`, `Cat.Monoidal`, `Cat.Virtual`, slices | at refactor |
| `yon-eval` / `yon-idpt` | `post-eval` / (absorbed into `idem-from-coupling`) | everywhere | with the above |
| `hnoy` / `hyon` | `hpre` / `hpost` | `Cat.Monoidal.Bifunctor` | at refactor |
| `I` | `𝟙` | `Cat.Monoidal.*` | at refactor |
| `2-coherent` | `triangle-coherent` | `Cat.Coherence` | at refactor |
| `monoidal-2-coherent` | (dies — instance of `triangle-coherent`) | — | at refactor |
| `braided-coherent` | `hexagon-coherent` | `Cat.Monoidal.Hexagon` | at refactor |
| `tensor-compose-contr` etc. | bare Codep spellings | `Cat.Monoidal` | at refactor (tier collapse) |
| `emb-composite-pt` | (dies — Codep's `act-comp` subsumes) | — | at refactor |
| `nat-trans` (Cat.Yoneda) | `fam-nat` | `Cat.Yoneda` | at refactor |
| `⟨_,_,_⟩` (classified comp) | distinct notation (TBD with coder) | `Cat.Virtual` | at refactor |
| prose "Eₙ" tower rungs | level names (triangle / hexagon / syllepsis) | DESIGN.md | now |
| prose "virtual" (general theory) | representable codependent / RCC | DESIGN.md | now |
| — (new) | `is-representable` + restated `compose-contr`; `is-representable-prop` (unit fragment), `hom≃representable` (Base — unconditional) | `Cat.Codep.Base` / `.Unit` | now |
| `loose` / `loose-ext` | `composite` / `composite-ext` | `Cat.Codep.*` | now |
| `pre-composite` / `post-composite` | `pre-comp` / `post-comp` (suffix conformance) | `Cat.Codep.*` | now |

## Suffix system (closed)

Law and lemma names are composed from this set; do not invent new
suffixes without adding them here.

| Suffix | Meaning | Example |
|---|---|---|
| `-contr` | a contractibility statement | `compose-contr`, `E₄-contr` |
| `-comp` | compatibility with composition | `act-comp`, `sub-comp`, `·-comp`, `emb-comp` |
| `-eval` | evaluation at the identity | `post-eval` |
| `-idpt` | idempotency | `post-idpt` (Cat.Type's `yon-idpt`; absorbed into `idem-from-coupling` in Codep) |
| `-coh` | an irreducible (paid) coherence field | `absorb-coh` |
| `-ext` | extensionality / pointwise-to-path | `composite-ext` |
| `-ind` | an eliminator | `E₃-ind` |
| `-β` / `-η` | computation / uniqueness rules of a universal property | `product-β` |
| `-is-prop` | propositionality of a structure | `unit-is-prop` |
| `-d` | displayed version | `hom-d`, `emb-d` |
| `/X` | slice construction | `hom/X` |
| `unitl`/`unitr`, `absorb-l`/`absorb-r` | left/right law pairs (noun-adjective per STYLEGUIDE) | — |
