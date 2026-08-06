---
artifact: SelingerSelfDual.pdf
sha256: dd5bc2acec2e69467902c5487c19f78d43921149dd7c201f97e04063a0271940
format: pdf
fetch-url: https://ncatlab.org/nlab/files/SelingerSelfDual.pdf
metadata-url: https://www.mscs.dal.ca/~selinger/papers/#halftwist
fetched: 2026-08-05
secondary-artifact: SelingerSelfDual.pdftext
secondary-sha256: 104659696c15c4b24f7aba5f7d8adc0f8ff4814b2344e55a9c44a8049d451f5c
---

# Selinger — Autonomous categories in which A ≅ A*

## Citation

Peter Selinger. *Autonomous categories in which A ≅ A\**. Extended
abstract. In *Proceedings of the 7th International Workshop on
Quantum Physics and Logic (QPL 2010)*, Oxford, pp. 151–160, 2010.

The author's own papers page gives this exact venue and page range
under the anchor `#halftwist`, and marks the hosted PDF a preprint.
No DOI or EPTCS volume was found for the QPL 2010 proceedings.

From the abstract: "there has been some interest in autonomous
categories (such as compact closed categories) in which the objects
are self-dual, in the sense that A ≅ A\*, or even A = A\*, for all
objects A. In this talk, we investigate which coherence conditions
should be required of such a category. We also investigate what
graphical language could be used to reason about such a category."

## Vetting

Directed agent ingestion, 2026-08-05. **PROVISIONAL.**

Statements verified: 27/27 CONFIRMED (digest-level), 2026-08-06, by
Claude (Opus 5), @ dd5bc2ac / 10465969. Two prefixes, because the
digests and the Section map anchor into both vendored files. The first
pins `SelingerSelfDual.pdf` (frontmatter `sha256`), the second pins
`SelingerSelfDual.pdftext` (frontmatter `secondary-sha256`). A
re-fetch or a re-extraction voids the field.

`M` is 27, the count of top-level bullets under Content digests. The
two axiom-list digests count as one bullet each. "Self-duality
structure, tortile form" covers (T1)-(T5), and "Self-duality
structure, right-autonomous form" covers (A1)-(A7). Adding or editing
a digest raises `M` and drops `N`.

First pass (2026-08-05): the vendored PDF's title page and abstract,
read to build the bibliographic record above; the author's own papers
page, read to confirm venue, page range, and that the requested
nLab-hosted copy and the author-hosted `halftwist.pdf` are the same
extended abstract (same title, author, page count, and section
structure — a line-diff of both `pdftotext` extractions turned up
only font/glyph differences between the two PDF builds, no content
differences). The requested nLab copy is the one vendored here.

Second pass (2026-08-06): all 10 pages read as 250 dpi renders
(`pdftoppm -png -r 250`, Poppler 26.06.0) against the extraction,
line by line. This pass wrote the full section map and every content
digest below, and the two Files findings (the `ǫ` font mapping and
the diagram-region inventory). It did not certify them.
`resources/README.md` reserves the `Statements verified:` field for a
read that did not write the material it checks.

Third pass (2026-08-06), the statement audit: an independent read of
all 10 pages at 250 dpi, with 600 dpi crops over every displayed
equation and every graphical-language picture. It re-derived both
Files findings (a `python3` codepoint census of the extraction for
Finding 1, and a render-against-range comparison for Finding 2),
re-ran the Source errata grep, recomputed both frontmatter hashes
against disk, and refetched the author's papers page. Both hashes
match. The venue and page range in Citation match the papers page.

Of the 27 digests, 14 stood as written. The audit corrected 13
against the page renders and certifies them as corrected. What
changed:

- Composition order. The digests write `f;g` for "`f` first". Several
  had transcribed the source's applicative `∘` without reversing it,
  which left the composite ill-typed. The Notation key now states the
  convention, and every transcribed composite reads left to right.
  Affected: the two hexagons, (T2), Theorem 3.6's scalar example, the
  naturality remark at l.695, and §5's `η̂_A`, `ε̂_A`.
- The balanced-category square (2.1) and Theorem 3.2's square. Both
  have a bottom arrow that runs right to left, so neither reads as a
  two-term equation. The axioms are
  `θ_{A⊗B} = c_{A,B};(θ_B⊗θ_A);c_{B,A}` and `φ;h_B;φ∗ = h_A`.
- The two `♯` operators. The source separates them by script
  position, not by overloading one symbol. Subscript `f_♯` is the
  structural operator of the Definition at l.558. Superscript `f^♯`
  is Remark 4.5's induced dagger. The characterization reads
  `(f^♯)_♯ = f∗`. Page 7 and page 9 show the contrast directly, and
  the extraction hides it.
- Axiom (A6). The page 8 render shows three binary `h` boxes on the
  right side, not two.
- Equation (4.2). It is the three-strand braid relation, three `h`
  boxes on each side. The five-box display above it carries no
  equation number, and neither do the `c_{A,B}` and `θ_A`
  definitions below it.
- Remark 4.5. The source says Theorem 3.2's isomorphisms are unitary
  for the induced dagger, not that they are exactly the unitary ones.
  The uniqueness of `f^♯` is asserted without argument there, so the
  digest now marks its ground as the entry's own.
- Smaller repairs: the tensor order in (1.3)'s inverse pair, the
  scope of the half-twist reading, the twist picture, the suppressed
  subscript in (3.1), and five page or line attributions in the Files
  ranges and the `≅` caveat.

The audit did not re-verify the first pass's comparison against the
author-hosted `halftwist.pdf`, which is not vendored here.

## Files

- `SelingerSelfDual.pdf` — the canonical artifact, fetched from the
  nLab file host. `format: pdf`, since no source markup is available.
- `SelingerSelfDual.pdftext` — greppability fallback, a `pdftotext`
  extraction (Poppler 26.06.0) of the native text layer. No OCR chain
  was needed or run. Pinned in the frontmatter as `secondary-artifact`.
  No correction patch has been applied (see the two findings below);
  the content digests carry the corrected reading instead.

**Finding 1 — a font `ToUnicode` defect drops every counit symbol.**
The paper's counit glyph (a lowercase epsilon, used throughout as
`ε̂` and `ε_A`) is drawn with a font whose `ToUnicode` map sends that
glyph's code to U+01EB LATIN SMALL LETTER O WITH OGONEK, not to a
Greek epsilon. `pdftotext` follows the map faithfully, so the
extraction carries a real but wrong character everywhere the source
shows an epsilon — confirmed by inspecting the codepoints of every
non-ASCII character in `SelingerSelfDual.pdftext` (18 occurrences, at
`l.68`, `l.77`, `l.95`, `l.113`, `l.283`, `l.305`, and elsewhere). A
reader who greps the extraction for `ε` or `ϵ` finds nothing; the
literal character on disk is `ǫ` (U+01EB). Every other Greek letter
in the document (θ, η, α, φ, λ, ρ) maps correctly. The content
digests below write the epsilon correctly, as `ε` (U+03B5), not as
the extraction's `ǫ`. This is the same class of defect as the
mirrored-triangle `ToUnicode` bug documented in
[`munch-maccagnoni-duploids`](../munch-maccagnoni-duploids/README.md)
— a font-table fault, not an extractor fault — but no correction
patch was written for it here, because a single-glyph substitution
this pervasive (18 sites, several inside the diagram regions of
Finding 2) would not leave the file easier to read than the digests
already make it.

**Finding 2 — the paper's graphical-language boxes and multi-arrow
diagrams extract out of reading order.** Every displayed equation
that draws a labeled box (`h_A`, `h_A⊗B`, …) or a multi-object
commutative diagram scrambles across many short lines, because
`pdftotext` lays out the diagram's text fragments by position, not by
the reading order a human would infer from the arrows. This is the
same phenomenon `munch-maccagnoni-duploids` calls "interleaved
two-column displays," and it is not patchable by a line-local `sed`
substitution: `resources/README.md`'s correction-patch mechanism is
for a dropped or wrong character on an otherwise-ordered line, and a
patch may not move a line. Repairing genuine reading-order chaos
would require moving lines, so per that entry's own precedent for the
same defect class, the affected ranges are inventoried here instead
of patched, and the content digests below carry the corrected
reading, each confirmed against the named PDF page render.

Affected ranges (line numbers index `SelingerSelfDual.pdftext`):

| Range | Content | Page | Reading order |
| --- | --- | --- | --- |
| `l.55-120` | the `h_A` box picture, then equations (1.1), (1.2): the strict exact-pairing diagrams and their graphical-language cap/cup pictures | 2 | scrambled |
| `l.135-220` | the `i_A` picture, then equations (1.3)-(1.5): the derived braiding, the half-twist picture (1.4), the two-strand crossing identity, the full-twist picture | 3 | scrambled |
| `l.291-313` | §2's graphical-language cheat sheet: braiding, twist, dual `η_A`, `ε_A` pictures | 4 | scrambled |
| `l.347-455` | axioms (T2), (T3), (T5), the `i_A` composite, and their graphical-language pictures | 5 | scrambled |
| `l.588-693` | axioms (A4), (A6), (A7) and their graphical-language pictures | 8 | scrambled |
| `l.699-780` | equation (4.1)'s naturality picture, the two derived pictures below it (the second is (4.2)), and the definitions of `c_{A,B}` and `θ_A` | 8 | scrambled |

Two ranges extract cleanly enough to read directly and are not in the
table: Theorem 3.2's commutative square (`l.468-481`, page 6) and
Remark 3.7's equation (3.1) (`l.511-519`, page 6). Both are small
arrow diagrams without a graphical-language box, and both stay
readable in the raw extraction, with the caveat below. In each, the
arrow labels extract ahead of the objects they annotate, and (3.1)'s
base line splits, its second half landing before its first.

One further, narrower caveat holds everywhere, including the two
clean ranges: the source's `≅` (`\cong`) typesets as a tilde stacked
over an equals sign, and several fonts in this PDF draw that as two
separate strokes. `pdftotext` then emits them as `∼` and `=` on
separate lines (e.g. `l.1-2`, `l.9-10`, `l.363-364`) rather than as
one `≅`. This is a display-order symptom of the same font behavior
Finding 2 describes, not a separate defect.

All vendored forms are gitignored. Re-fetching is mechanical from the
frontmatter; a re-extraction would need to re-derive both findings
above, since nothing here is hash-pinned below the whole-file level.

## Source provenance

Fetched directly from `https://ncatlab.org/nlab/files/SelingerSelfDual.pdf`
on 2026-08-05 (`Content-Type: application/pdf`, no paywall). The
author also hosts the same extended abstract, under the filename
`halftwist.pdf` (and a 2-up print variant), from
`https://www.mscs.dal.ca/~selinger/papers/`, marked "(preprint)" and
carrying the QPL 2010 citation transcribed above; that copy differs
from the nLab copy only in PDF build/font (see Vetting), and was not
vendored, since the nLab URL is what was requested. Page renders were
produced locally from the vendored PDF (`pdftoppm -png -r 250`,
Poppler 26.06.0) and are not themselves vendored artifacts.

## Section map

Anchors index `SelingerSelfDual.pdftext`. Jump with
`sed -n 'A,Bp' SelingerSelfDual.pdftext`. Full line-anchored depth:
every definition, theorem, conjecture, remark, example, and numbered
axiom group, per `resources/README.md`'s depth standard for a
load-bearing source.

- l.1 Title, author, affiliation; l.7 Abstract
- §1 Introduction — l.16
  - §1.1 Self-duality — l.17 (background prose; not digested at
    statement level)
  - §1.2 Self-duality without coherence — l.42, equation (1.1) l.75,
    equation (1.2) l.119
  - §1.3 Self-duality with coherence — l.146, equation (1.3) l.168,
    equation (1.4) l.179, equation (1.5) l.213
- §2 Background — l.228
  - Definition (Braided monoidal category) — l.230
  - Definition (Balanced monoidal category) — l.239, equation (2.1)
    l.246
  - Definition (Right autonomous category) — l.258, equation (2.2)
    l.281
  - Graphical-language table (braiding, twist, dual) — l.291
  - Definition (Tortile category) — l.327
- §3 Self-duality structure on tortile categories — l.335
  - Definition (self-duality structure, tortile form) — l.342,
    axioms (T1) l.345, (T2) l.346, (T3) l.372, (T4) l.402, (T5) l.419
  - Remark 3.1 — l.461
  - Theorem 3.2 — l.462
  - Conjecture 3.3 (Coherence) — l.483
  - Theorem 3.4 — l.487
  - Remark 3.5 — l.490
  - Theorem 3.6 (with proof) — l.495
  - Remark 3.7, equation (3.1) — l.510, l.519
  - Example 3.8 (Natural examples) — l.532
  - Example 3.9 (Unnatural example) — l.536
  - Example 3.10 — l.541
- §4 Self-duality structure on right autonomous categories — l.550
  - Definition (self-duality structure, right-autonomous form),
    `f♯` notation — l.558, axioms (A1) l.576, (A2) l.580, (A3) l.586,
    (A4) l.588, (A5) l.607, (A6) l.610, (A7) l.660
  - Naturality remarks, equation (4.1) — l.695, l.710
  - Equation (4.2), consequence of (4.1)+(A6) — l.737
  - Definitions of `c_{A,B}` and `θ_A` from `h` — l.752, l.778
  - Theorem 4.1 — l.791
  - Remark 4.2 — l.795
  - Remark 4.3 — l.797
  - Remark 4.4 — l.803
  - Remark 4.5 (Induced dagger structure) — l.813
- §5 Strict self-duality — l.834
- §6 Conclusions — l.851
- References — l.860

## Content digests

Statement-level, in the source's own notation, transcribed by the
rule below, and confirmed against the named PDF page render wherever
the range falls in Finding 2's table above.

**Notation key.** A subscript is written `_X` (`h_A`, `θ_A`,
`c_{A,B}` for a two-part subscript), a superscript `^X`. Composition
is diagrammatic: `f;g` applies `f` first. The source composes
applicatively with `∘`, so a transcription of a source formula
reverses its order. The dual of an object or morphism is the source's
own postfix `A∗`, `f∗` (U+2217, matching the extraction). The source
uses `♯` (U+266F MUSIC SHARP SIGN, matching the extraction) for two
different operators and separates them by script position. Subscript
`f_♯` is the structural operator of the Definition at l.558.
Superscript `f^♯` is Remark 4.5's induced dagger. The extraction
flattens both to a bare `♯`, so the position reads only off a page
render. `ε`/`ε̂` render the counit, which the source draws with the
lunate glyph of LaTeX `\epsilon`. The digests write `ε` (U+03B5), not
that glyph and not the extraction's `ǫ` (see Finding 1). `α`, `λ`,
`ρ` are the monoidal associator and unitors. `θ` is a twist. `η`, `ε`
are a duality unit and counit. `≅` is written whole, per the caveat
in Files. In a picture, a *cap* is a left-closed bend and a *cup* is
a right-closed bend.

- **§1.2, strict self-duality without coherence** (l.42, equations
  (1.1)-(1.2)): the non-strict approach equips every object A with an
  independent isomorphism `h_A : A → A∗` and no further conditions;
  the sound-and-complete graphical language is the ordinary
  autonomous-category language plus an uninterpreted box `h_A` (and
  its inverse) with no laws. The strict version requires `A = A∗` for
  every object, equivalently a unit `η̂_A : I → A⊗A` and counit
  `ε̂_A : A⊗A → I` satisfying the two ordinary exact-pairing triangles
  (1.1) — `(id_A⊗η̂);(ε̂⊗id_A) = id_A` and `(η̂⊗id_A);(id_A⊗ε̂) = id_A` —
  with **no additional condition imposed**. Neither `η̂_A` nor `ε̂_A`
  can be drawn as the ordinary cup or cap, since that would validate
  laws the axioms do not grant. The only sound-and-complete picture,
  strict or not, draws `η̂_A` as a cap with an `h_A⁻¹` box and `ε̂_A` as
  a cup with an `h_A` box (1.2). Even under strictness no equation is
  forced between morphisms in general. The canonical `i_A : A → A∗∗`
  (from a symmetric or pivotal structure) is drawn as a crossing carrying both
  an `h_A` and an `h_A⁻¹` box, and the source states explicitly that
  this is "not a diagram for the identity morphism," even though
  `A = A∗∗` holds as bare objects under strictness.
- **§1.3, self-duality forces a braiding and a half-twist** (l.146,
  equations (1.3)-(1.5)): any autonomous category already carries a
  canonical `(A⊗B)∗ ≅ B∗⊗A∗`. Composing it with `h_{A⊗B}` and
  `h_B⁻¹⊗h_A⁻¹` gives a derived isomorphism (1.3),
  `A⊗B --h_{A⊗B}--> (A⊗B)∗ ≅--> B∗⊗A∗ --h_B⁻¹⊗h_A⁻¹--> B⊗A`. If the
  category is already symmetric or braided, one wants (1.3) to equal
  the symmetry or braiding. Even absent an assumed braiding,
  self-duality forces one via (1.3). Graphically, `(A⊗B)∗ ≅ B∗⊗A∗` is
  drawn as an identity, so (1.3) rules out drawing `h_X : X → X∗` as
  an identity for an arbitrary object term `X`. The case `X = A⊗B`
  shows it must be drawn as a half-twist (1.4) instead. Under that
  reading, (1.3) becomes a picture identity relating two
  half-twist-and-crossing composites. Consequently
  `θ_{A∗} := A∗ --h_{A∗}--> A∗∗ --h∗_A--> A∗` (1.5) is drawn as a full
  twist on `A∗`. **Conclusion, stated directly by the source**: an
  autonomous category with self-duality should at minimum be tortile
  (and possibly compact closed, if the braiding is a symmetry).
  Tortile is the minimal autonomous structure on which requiring a
  self-duality even makes sense. This is the argument the paper's two
  axiom systems (§3, §4) both build on.
- **Braided monoidal category** (Definition, l.230): a braiding is a
  natural family of isomorphisms `c_{A,B} : A⊗B → B⊗A` satisfying the
  two hexagon axioms, both between maps `(A⊗B)⊗C → B⊗(C⊗A)`:
  `(c_{A,B}⊗id_C);α_{B,A,C};(id_B⊗c_{A,C}) =
  α_{A,B,C};c_{A,B⊗C};α_{B,C,A}` and
  `(c⁻¹_{B,A}⊗id_C);α_{B,A,C};(id_B⊗c⁻¹_{C,A}) =
  α_{A,B,C};c⁻¹_{B⊗C,A};α_{B,C,A}`. A monoidal category with a chosen
  braiding is a braided monoidal category.
- **Balanced monoidal category** (Definition, l.239, equation (2.1)):
  a twist is a natural family of isomorphisms `θ_A : A → A` with
  `θ_I = id_I` such that `θ_{A⊗B} = c_{A,B};(θ_B⊗θ_A);c_{B,A}` for all
  `A,B`. The square carries `c_{A,B}` on top, `θ_{A⊗B}` down the left,
  `θ_B⊗θ_A` down the right, and `c_{B,A} : B⊗A → A⊗B` on the bottom
  pointing right to left, so both paths run from the top-left `A⊗B` to
  the bottom-left `A⊗B`. A balanced monoidal category is a braided
  monoidal category with a twist.
- **Right autonomous category** (Definition, l.258, equation (2.2)):
  a right dual for `A` is `(B,η,ε)` with `η : I → B⊗A`,
  `ε : A⊗B → I` such that the two adjunction triangles commute:
  `(id_A⊗η);(ε⊗id_A) = id_A` (through `A⊗B⊗A`) and
  `(η⊗id_B);(id_B⊗ε) = id_B` (through `B⊗A⊗B`). `η` and `ε` determine
  each other uniquely, and `(B,η,ε)`, if it exists, is unique up to
  isomorphism given `A`. A monoidal category is right autonomous if
  every object has a right dual, then denoted `(A∗,η_A,ε_A)`. Graphical
  language [6,3,2]: braiding as a crossing of two bands, twist as one
  band with a full twist in it, `η_A` as a cap `A/A∗`, `ε_A` as a cup
  `A∗/A`. In each of the three cases (braided, balanced, right
  autonomous) a coherence theorem states that an equation follows from
  the axioms if and only if it holds graphically. Combining balanced
  with autonomous needs one further compatibility axiom for the
  combined language to stay coherent.
- **Tortile category** (Definition, l.327): a balanced monoidal
  category that is also right autonomous and satisfies
  `θ_{A∗} = (θ_A)∗`. A compact closed category [Kelly–Laplaza] is the
  special case `θ_A = id_A` for all `A` (hence `c_{A,B} = c⁻¹_{B,A}`);
  equivalently, a compact closed category is a right autonomous
  symmetric monoidal category.
- **Self-duality structure, tortile form** (Definition, l.342): for
  `C` tortile, a family `h_A : A → A∗`, one per object, satisfying
  five axioms for all `A,B`:
  - (T1, l.345) `h_A` is an isomorphism.
  - (T2, l.346) `h_{A∗};h∗_A = θ_{A∗} : A∗ → A∗`. Equivalently
    `h∗_A;h_{A∗} = θ_{A∗∗} : A∗∗ → A∗∗`. (The source writes both with
    `∘`: `h∗_A ∘ h_{A∗}` and `h_{A∗} ∘ h∗_A`.) Graphically (page 5):
    an `h_{A∗}` box and an `h_A` box, joined by bends of the
    autonomous structure, equal a full twist on `A∗`, matching (1.5)'s
    reading of `θ_{A∗}`.
  - (T3, l.372, extraction scrambled per Finding 2, read from the page
    5 render) `h_{A⊗B} = [A⊗B --h_A⊗h_B--> A∗⊗B∗ --c_{A∗,B∗}-->
    B∗⊗A∗ ≅--> (A⊗B)∗]`, the last isomorphism canonical from the
    autonomous structure. Graphically: the `h_{A⊗B}` box on `(B,A)`
    factors as the two boxes `h_B`, `h_A` composed with a crossing.
  - (T4, l.402, extraction scrambled, read from the render)
    `h_I : I ≅→ I∗` is the canonical isomorphism from the autonomous
    structure.
  - (T5, l.419, extraction scrambled, read from the render)
    `h_A = [A --i_A--> A∗∗ --h∗_A--> A∗]`, where
    `i_A : A ≅→ A∗∗` is the canonical pivotal isomorphism,
    `i_A = A --θ_A--> A --id⊗η_{A∗}--> A⊗A∗∗⊗A∗
    --c⁻¹_{A∗∗,A}⊗id--> A∗∗⊗A⊗A∗ --id⊗ε_A--> A∗∗`. Graphically, in the
    braided-autonomous language: an `h_A` box composed with a cap
    equals a twist-and-crossing composite ending in an `h_A` box.
- **Remark 3.1** (l.461): axioms (T1)-(T5) are sound for the graphical
  language where `h` is drawn as a half-twist, per (1.4).
- **Theorem 3.2** (l.462): for `φ : A → B` any canonical isomorphism
  arising from the tortile structure — one drawn as an identity in the
  ordinary graphical language: `α`, `λ`, `ρ`, `(A⊗B)∗ ≅ B∗⊗A∗`,
  `I ≅ I∗`, or `i_A : A → A∗∗` — but explicitly **not** `θ` or `c` —
  the square commutes. It has `φ` on top, `h_A` down the left, `h_B`
  down the right, and `φ∗ : B∗ → A∗` on the bottom pointing right to
  left, so the two paths `A → A∗` agree: `φ;h_B;φ∗ = h_A`.
- **Conjecture 3.3 (Coherence)** (l.483): an equation follows from the
  axioms of tortile categories with self-duality structure if and only
  if it holds in the graphical language, where `h_A` is drawn as a
  half-twist per (1.4). **Stated by the source as a conjecture, not a
  theorem** — the paper proves soundness of the axioms for the
  graphical language (Remark 3.1) but only conjectures completeness.
- **Theorem 3.4** (l.487): assuming (T1)-(T4), if (T5) holds for some
  objects `A,B` then it also holds for `A∗`, `A⊗B`, and `I`. So it
  suffices to check (T5) on a generating set of objects.
- **Remark 3.5** (l.490): when the objects of `C` are freely
  generated, (T2)-(T4) can serve as the definitions of `h_{A∗}`,
  `h_{A⊗B}`, `h_I`; it suffices to choose `h_A` on the generators
  subject only to (T5), extend via (T2)-(T4), and Theorem 3.4 then
  gives a self-duality structure on all of `C`.
- **Theorem 3.6, with proof** (l.495): (T1) is a consequence of (T2)
  and (T5); the remaining axioms (T2)-(T5) are independent. Proof
  sketch, over a tortile category freely generated from a set of
  generators: violating (T5) alone is possible by choosing `h_A` on
  generators arbitrarily and extending via (T2)-(T4) (yields (T1)-(T4)
  valid, (T5) not); violating exactly one of (T2)-(T4) alone is
  possible by choosing `h_A` on generators to satisfy (T5), extending
  inductively, then multiplying the definition of exactly one of
  `h_{A∗}`, `h_{A⊗B}`, `h_I` by a nontrivial scalar `φ` (e.g.
  `h_{A∗} = φ·[θ_{A∗};(h∗_A)⁻¹]`, which the source writes
  `φ · (h∗_A)⁻¹ ∘ θ_{A∗}`) — the extra scalar does not invalidate
  (T5); and (T2)+(T5)⇒(T1) because `h∗_A` is a split epi by (T2)
  (hence `h_A` a split mono), and since `i_A` is an isomorphism, (T5)
  then forces `h∗_A` mono, hence iso, hence `h_A` iso.
- **Remark 3.7, equation (3.1)** (l.510): (T5) in particular implies
  that `A --h_A--> A∗ --(h∗)⁻¹--> A∗∗` (3.1) is a monoidal natural
  transformation, because it equals `i_A`, itself monoidal-natural in
  any tortile category. Partial converse: if (3.1) is assumed merely
  natural, its monoidality already follows from (T1)-(T4) alone — but
  naturality of (3.1) is not strong enough to force it to equal `i_A`,
  i.e. it does not imply (T5). The source suppresses the subscript in
  (3.1) itself. The second map is `(h∗_A)⁻¹`.
- **Example 3.8, Natural examples** (l.532): the compact closed
  category of finite-dimensional real inner product spaces carries a
  self-duality with `h_A : A → A∗` the adjoint of the inner product
  `A⊗A → I`. The compact closed category of finite sets and relations
  carries a self-duality with `A = A∗` and `h_A : A → A∗` the identity
  relation.
- **Example 3.9, Unnatural example** (l.536): the compact closed
  category of finite-dimensional complex inner product spaces (finite
  dimensional Hilbert spaces) admits a self-duality, but not
  canonically: rename the objects (up to equivalence of categories) so
  they are freely generated, then choose the structure per Remark 3.5.
- **Example 3.10** (l.541): from any tortile `C`, construct `D` with
  self-duality: objects of `D` are pairs `(A,h)` with `A` an object of
  `C` and `h : A → A∗` a `C`-isomorphism satisfying (T5); a morphism
  `(A,h) → (B,h′)` is just a `C`-morphism `A → B`. `(A,h)⊗(B,h′)`,
  `(A,h)∗`, and `(I,h⁗)` are defined the unique way making the axioms
  hold, with the tortile structure inherited from `C`. Non-canonical:
  each object `A` of `C` can generate many pairwise non-isomorphic
  objects `(A,h_1),(A,h_2),…` of `D`.
- **Self-duality structure, right-autonomous form; the `_♯` operator**
  (Definition, l.558): for `C` right autonomous, a family
  `h_A : A → A∗` satisfying — the source's own count — "eight axioms
  (for all A, B, C, f, and g)"; the enumeration below runs only
  (A1)-(A7) (see Source errata). Defines, for `f : A → B`, the
  **structural sharp** `f_♯ := A∗ --h_A⁻¹--> A --f--> B --h_B--> B∗`,
  used throughout (A3)-(A7). The sharp sits in subscript position
  here, which is what separates it from Remark 4.5's superscript
  dagger. Some axioms are stated in the graphical language of right
  autonomous categories, legitimate by that language's own coherence
  theorem.
  - (A1, l.576) `h_A` is an isomorphism.
  - (A2, l.580, extraction scrambled, read from the render)
    `h_I : I ≅→ I∗` is the canonical isomorphism from the autonomous
    structure.
  - (A3, l.586) `(f∗)_♯ = (f_♯)∗`.
  - (A4, l.588) the square commutes, with the vertical isomorphisms
    canonical from the autonomous structure:
    `(A⊗B)∗ --(f⊗g)_♯--> (A′⊗B′)∗` over
    `B∗⊗A∗ --g_♯⊗f_♯--> B′∗⊗A′∗`, both verticals `≅`.
  - (A5, l.607) `α∗ = (α_♯)⁻¹`, where
    `α : (A⊗B)⊗C → A⊗(B⊗C)` is the monoidal associator; equivalently,
    `h_{A⊗(B⊗C)}` equals `h_{(A⊗B)⊗C}` modulo associativity.
  - (A6, l.610, diagrammatic, page 8) states a coherence between
    applying `h` once to the triple tensor `A⊗(B⊗C)` (then splitting
    the result through `h_{A∗}`, `h_{B∗}`, `h_{C∗}` on the three
    starred factors) and applying `h` in three binary steps
    (`h_{A⊗B}`, then `h_{A∗⊗C}`, then `h_{B∗⊗C∗}`) — the ternary
    counterpart of (T3)'s binary tensor-compatibility. Both sides run
    the three wires `C`, `B`, `A` to `A∗∗`, `B∗∗`, `C∗∗`. Used
    together with (A5) and (4.2) to prove the derived `c_{A,B}`
    satisfies the hexagon axioms (l.788).
  - (A7, l.660, diagrammatic, page 8) states that applying `h` four
    times in succession, `A --h--> A∗ --h--> A∗∗ --h--> A∗∗∗ --h-->
    A∗∗∗∗`, equals one `h_{A⊗A∗∗∗}` box whose `A∗∗∗` input and `A∗`
    output are joined by a bend over the top, leaving `A` in and
    `A∗∗∗∗` out. Named by the source itself (Remark 4.2, l.796) as "a
    version of yanking."
- **Naturality of `h`, equation (4.1)** (l.695): `(−)_♯` is a
  covariant functor with object part `(−)∗`. `h_A : A → A∗` is a
  natural transformation with respect to `_♯`, by definition
  `f;h_B = h_A;f_♯` (the source writes `h_B ∘ f = f_♯ ∘ h_A`), and
  `h_{A∗} = (h_A)_♯`. Axiom (A4) is equivalent to (4.1), componentwise
  naturality of `h_{A⊗B}`: an `f` box on the top wire and a `g` box on
  the bottom wire, followed by an `h` box across both, equal the `h`
  box first, followed by `g_♯` on the top wire and `f_♯` on the
  bottom. This naturality, together with (A6), gives equation (4.2)
  (l.737). (4.2) is a three-strand identity between two composites of
  three binary `h` boxes each, the braid-relation shape that Remark
  4.2 calls a version of the Yang-Baxter equation. The unnumbered
  five-box display just above it (l.717, page 8) is the naturality
  consequence that (A6) is then applied to.
- **`c_{A,B}` and `θ_A` defined from `h`** (l.752, l.778, both
  unnumbered): the paper defines `c_{A,B}` graphically, as one `h` box
  across two wires followed by an `h⁻¹` box on each wire, and
  `θ_A := A --h_A--> A∗ --h_{A∗}--> A∗∗ --h∗_A--> A∗ --h_A⁻¹--> A`.
  Then `c_{A,B}` satisfies the two hexagon axioms by (A6), (A5), and
  (4.2), giving a braided structure. One must separately verify that
  `θ_A` gives a balanced structure and that the remaining tortile
  axioms hold.
- **Theorem 4.1** (l.791): a self-duality structure on a right
  autonomous category yields a tortile structure satisfying the
  axioms of §3. Conversely, any self-duality structure on a tortile
  category satisfies the axioms of §4. The two constructions are
  mutually inverse, giving a one-to-one correspondence between
  tortile categories with a §3-style self-duality structure and
  autonomous categories with a §4-style one. **This is the paper's
  central equivalence result**, establishing that the two axiom
  systems (T1)-(T5) and (A1)-(A7) are two presentations of the same
  notion.
- **Remark 4.2** (l.795): equation (4.2) is a version of the
  Yang-Baxter equation for braids; axiom (A7) is a version of
  yanking.
- **Remark 4.3** (l.797): axiom (A5) states that the associativity
  isomorphism satisfies Theorem 3.2's condition; the corresponding
  property for Theorem 3.2's other canonical isomorphisms follows
  from the remaining axioms, mostly from (A7) together with coherence
  for braided autonomous categories.
- **Remark 4.4** (l.803): a consequence of (A7) and (A4) is
  `f∗∗ = f_{♯♯}`; equivalently, `A --h_A--> A∗ --h_{A∗}--> A∗∗` is a
  natural transformation.
- **Remark 4.5, Induced dagger structure** (l.813): a self-duality
  structure on a right autonomous (or tortile, or compact closed)
  category induces a second, distinct operator, the **induced
  dagger**, written `f^♯` with the sharp in superscript position. For
  `f : A → B` it has type `B → A`, as against the structural
  subscript sharp's `A∗ → B∗`. It is characterized as the unique
  morphism with `(f^♯)_♯ = f∗ : B∗ → A∗`: the structural sharp applied
  to the dagger is the ordinary dual, and both sides have type
  `B∗ → A∗`, so the characterization typechecks. (The source asserts
  uniqueness without argument. It follows from (A1), which makes
  `(−)_♯` a bijection `Hom(B,A) → Hom(B∗,A∗)`.) Theorem 3.2's
  properties then say precisely that the canonical isomorphisms named
  there are unitary for this induced dagger. The source flags that
  this dagger is usually **not** the "natural" dagger a concrete
  example category already carries: for `f : I → I` the induced dagger
  always gives `f^♯ = f`, whereas the natural dagger on
  finite-dimensional Hilbert spaces sends `f` to its complex
  conjugate. Also, if `C` is tortile with self-duality, the induced
  dagger is not a *dagger tortile* structure, since
  `(c_{A,B})^♯ = c_{B,A}` and `(θ_A)^♯ = θ_A`, whereas a dagger
  tortile category needs `(c_{A,B})† = c⁻¹_{A,B}` and
  `(θ_A)† = θ_A⁻¹`. So `c_{A,B}` and `θ_A` fail to be unitary for the
  induced dagger. For this reason the source states it avoids the
  ordinary notation `(−)†` for these "unnatural" dagger structures. In
  "natural" examples such as real inner product spaces, the induced
  dagger does coincide with the usual one.
- **§5, Strict self-duality** (l.834): every self-duality structure
  `h_A : A → A∗` on a right autonomous category induces a strict
  autonomous structure `η̂_A : I → A⊗A`, `ε̂_A : A⊗A → I`, via
  `η̂_A = η_A;(h_A⁻¹⊗id_A)` and `ε̂_A = (id_A⊗h_A);ε_A` (the source
  writes `(h_A⁻¹⊗id_A) ∘ η_A` and `ε_A ∘ (id_A⊗h_A)`, displayed
  graphically in (1.2)). The source flags axiomatizing self-duality
  directly in terms of `η̂_A`, `ε̂_A` — bypassing a pre-existing
  autonomous structure and the isomorphisms `h_A` entirely — as an
  open question, **explicitly deferred to a full version of the
  article** that this extended abstract does not itself deliver.
- **§6, Conclusions** (l.851): the paper proposes coherence
  conditions for autonomous categories with `A ≅ A∗`, in two
  equivalent formulations (§3, §4, unified by Theorem 4.1). All listed
  conditions are sound for the graphical language (Remark 3.1) and
  hold in the stated examples (3.8-3.10); **completeness is
  conjectured, not proved** (Conjecture 3.3). The source names
  categories with chosen Frobenius algebra structures on each object
  as a further area where self-duality arises, and states generalizing
  the coherence conditions to Frobenius algebras as future work.

## Source errata

- **The right-autonomous definition (l.558) claims eight axioms but
  states seven.** "A self-duality structure on `C` is given by a
  family of morphisms `h_A : A → A∗`, one for each object `A`,
  satisfying the following eight axioms" (the word "eight" is at
  `l.560`) is followed by an enumeration that runs (A1) through (A7)
  only (`l.576`-`l.693`), with no `(A8)` anywhere in the document.
  `grep -n "(A[0-9])" SelingerSelfDual.pdftext` returns A1 through A7
  and nothing else, and `A8` does not occur in the file. Whether this
  is a stray word ("eight" for "seven") or an axiom dropped between
  drafts is not stated by the source and is not guessed here.

## What the source establishes

Coherence conditions for autonomous (in particular tortile and
compact closed) categories in which every object A carries a chosen
isomorphism h_A : A → A\*, in two equivalent formulations (proved
equivalent by Theorem 4.1), together with a proposed sound graphical
language for the resulting structure (Remark 3.1) and a completeness
conjecture the source does not prove (Conjecture 3.3). It also treats
the strict variant A = A\* directly in terms of a unit and counit on
A ⊗ A (§5), leaving the direct axiomatization of that unit/counit
pair — bypassing h_A altogether — as future work. It notes the
self-duality structure induces a dagger structure that usually does
not coincide with the dagger a concrete example category carries
natively (§4, Remark 4.5). Entries record what the source states;
every mathematical claim here is CONJECTURED until machine-checked —
and Conjecture 3.3 and the §5 axiomatization question are CONJECTURED
by the source's own account, not merely pending kitcat's mechanization.
