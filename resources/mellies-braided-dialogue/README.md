---
artifact: mellies-braided-dialogue.pdf
sha256: fd7fb96e832cb40ed0b587c24e005a37d43b81812fe05b333f92649a0fb2a6c4
format: pdf
fetch-url: https://www.irif.fr/~mellies/tensorial-logic/6-braided-notions-of-dialogue-categories.pdf
fetched: 2026-07-11
---

# Melliès — Braided notions of dialogue categories

## Citation

Paul-André Melliès. *Braided notions of dialogue categories*.
Manuscript, dated March 7, 2012. Laboratoire Preuves, Programmes,
Systèmes, CNRS — Université Paris Diderot.
Hosted at:
<https://www.irif.fr/~mellies/tensorial-logic/6-braided-notions-of-dialogue-categories.pdf>
(the author's tensorial-logic page also hosts companion slides,
`braided-notions-of-dialogue-categories-slides.pdf`).

Publication status: **unpublished manuscript**. An independent
literature check (2026-07-12) — arXiv author listing, DBLP
exact-title search and the author's full DBLP bibliography, and the
author's own IRIF tensorial-logic index — found no journal,
proceedings, or arXiv version; the author's page marks this item
in-progress. So "unpublished manuscript" is the correct citation
(honest negative: the search was performed and returned nothing
citable beyond the IRIF-hosted PDF).

Cross-reference: the manuscript's central notion — the *balanced
dialogue category* (Definition 12) — is load-bearing in the
**published** Paul-André Melliès, *Ribbon Tensorial Logic*, LICS
2018 (DOI 10.1145/3209108.3209129; HAL hal-02436302), whose
coherence theorem concerns balanced dialogue categories. When
citing, cite **this manuscript** for its specific result that
`Mod(H)` over a ribbon Hopf algebra `H` is a balanced dialogue
category (Proposition 23), and cite *Ribbon Tensorial Logic*
(published) for the balanced-dialogue-category coherence theorem.
Honesty caveat: the LICS 2018 full text was not read, so whether
this manuscript's specific headline `Mod(H)` theorem is reproduced
there is UNVERIFIED.

## Vetting

Opened 2026-07-11 by Claude (Fable 5), at Lane's direction as part
of the founding `resources/` ingestion. Checked: title page and
abstract against the citation; the section map and definition
inventory below extracted from the full text (pdftotext).
Bit-identity of the vendored file with the IRIF URL above verified
by sha256 on 2026-07-11.

Brought to the `resources/` format bar 2026-07-12 by Claude (Opus
4.8): canonical format recorded as PDF, Files inventory added, and
the line-anchored location→content map built (`l.NNN` anchors into
the `.pdftext`, with the central notion — the balanced dialogue
category, Definition 12 — and the headline `Mod(H)` theorem
anchored). The recorded PDF hash was re-verified
(`shasum -a 256 mellies-braided-dialogue.pdf`) and matches. The
publication-status negative was re-checked and recorded above.

Provisional marker retired 2026-07-13 (Vetted, below); at ingestion the entry was agent-vetted, Lane's confirmation
pending (the format authority governs what the marker means).

Statements verified: 3/4 CONFIRMED on first pass, 1 CORRECTED
applied (spot-check), 2026-07-13, by verifier (Claude), @ fd7fb96e; confirming re-pass clean 2026-07-13.

Vetted: 2026-07-13, Lane (ratified at Lane's explicit direction,
conveyed in-session; full-shelf ratification).

## Files

Canonical format: **PDF** (no source markup is published for this
manuscript). All vendored and derived forms are gitignored; only
this README is tracked.

- `mellies-braided-dialogue.pdf` — the canonical artifact: the
  42-page IRIF manuscript compile dated March 7, 2012. This is the
  file the frontmatter's canonical `sha256` is of.
- `mellies-braided-dialogue.pdftext` — a `pdftotext` extraction of
  the canonical PDF (greppability fallback; the map's `l.NNN`
  anchors index this file). Regenerate with
  `pdftotext mellies-braided-dialogue.pdf mellies-braided-dialogue.pdftext`.
  Provenance: pdftotext 26.06.0 (flake-pinned poppler; regenerate
  inside `nix develop`); regenerating with this version reproduces
  the vendored extraction byte-identically (checked 2026-07-13
  against a temp-file regeneration).

Grep `mellies-braided-dialogue.pdftext` for a definition; jump with
`sed -n 'A,Bp' mellies-braided-dialogue.pdftext`.

## Source provenance

Fetched 2026-07-11 from the author's IRIF tensorial-logic page
(the frontmatter's fetch URL); bit-identity of the vendored copy
with that URL was verified by sha256 at fetch time, and the URL
still served a PDF when HEAD-checked 2026-07-13. The vendored
filename differs from the URL basename. This is an unpublished
manuscript hosted only on the author's page, which can recompile
or relink it at any time (the sibling entry
`mellies-micrological-negation` documents exactly such a drift),
so a re-fetch is not guaranteed to reproduce this vintage. Verify
any re-fetched copy against the frontmatter's `sha256`; the hash
is the identity.

## Section map

Line anchors are into `mellies-braided-dialogue.pdftext`; jump with
`sed -n 'A,Bp' mellies-braided-dialogue.pdftext`. Depth is a
solid outline anchored to the load-bearing definitions and the
headline theorem — this is a conceptual/background source for the
braid/ribbon thread, not a mechanization target. Definition and
proposition numbers are as printed in the manuscript; a full
`Contents` listing sits at the end of the file (`l.4655`).

- **Title / Abstract** — `l.1` / `l.6`.
- **§1 Introduction** — `l.19`. Definition 1 (∗-autonomous
  category = a dialogue category whose tensorial pole is dualizing)
  — `l.95`. Plan of the paper — `l.129`.
- **§2 A fractional notation** — `l.141`. Double negation monads
  (the two canonical adjunctions of a dialogue category) — `l.310`.
- **§3 Helical dialogue categories** — `l.439`.
  - Definition 2 (helical presheaf on a monoidal category) —
    `l.461`.
  - Definition 3 (helical dialogue category = dialogue category
    with a helical structure) — `l.677`.
  - Proposition 1 (equivalent formulation of a helical structure)
    — `l.772`; Proposition 2 (helical structure = a natural
    isomorphism `turn`) — `l.787`.
  - Definition 4 (left name ⌜f⌝ of a morphism) — `l.1387`.
  - Definition 5 (cyclic dialogue category = the degenerate helical
    case) — `l.2093`.
- **§4 Intermezzo: the dialogical twist** — `l.2111`. The
  dialogical twist reformulated internally — `l.2145`.
  - Proposition 5 (a unique morphism `twist : ⊥ → ⊥`) — `l.2188`.
  - Definitions 6–7 (cyclic ∗-autonomous categories) — `l.2106`,
    `l.2836`.
- **§5 Ribbon categories** (classical notions recalled) — `l.2841`.
  - Definition 8 (braiding) — `l.2916`; Definition 9 (balanced
    category = braided monoidal + a twist) — `l.3066`.
  - Definition 10 (dual pairs) — `l.3145`; Definition 11 (ribbon
    category) — `l.3229`.
  - Proposition 13 (ribbon category = a braided category with
    compatible duals/twist) — `l.3325`.
- **§6 Balanced dialogue categories** (the paper's central notion) —
  `l.3352`.
  - **Definition 12 (balanced dialogue category** = a dialogue
    category equipped with a braiding and a twist defining a
    balanced category) — `l.3366`. *The load-bearing notion.*
  - Proposition 14 (the dialogical twist agrees with the ribbon
    twist) — `l.3490`; Proposition 15 — `l.3691`.
  - Definition 13 (ultra-thin pole) — `l.3757`.
- **§7 Four illustrations** — `l.3761`.
  - 7.1 First illustration: ribbon categories — `l.3765`.
    Definition 14 (pre-ribbon category) — `l.3772`; Proposition 16
    (ribbon category = pre-ribbon category satisfying Eq. 22) —
    `l.3875`.
  - 7.2 Second illustration: ribbon categories with a distinguished
    object — `l.3880`.
  - 7.3 Third illustration: representation theory (`Mod(H)`) —
    `l.3938`. Algebraic inputs: Definition 15 (bialgebra) — `l.3940`;
    Definition 16 (left H-module) — `l.4045`; Definition 17 (Hopf
    algebra) — `l.4130`; Definition 18 (braiding on a bialgebra) —
    `l.4286`; Definition 19 (thin Hopf algebra) — `l.4359`;
    Definition 20 (ribbon Hopf algebra) — `l.4473`.
    - **Proposition 23 (headline):** given a ribbon Hopf algebra
      `H` in a balanced dialogue category `C`, together with a left
      H-module structure on the tensorial pole ⊥, with `H` thin in
      `C` and of invertible antipode, `Mod(H)` (left H-modules) is
      a balanced dialogue category with tensorial pole the left
      H-module ⊥ — `l.4568`. (The abstract states the
      Vect-instance: modules of arbitrary dimension over a field,
      pole the underlying field k.)
    - Proposition 24 (the subcategory of H-modules with a left dual
      is a ribbon category — the finite-dimensional recovery) —
      `l.4573`.
  - 7.4 Fourth illustration: ∗-autonomous categories — `l.4578`.
    Definition 21 (helical/cyclic ∗-autonomous category) — `l.4586`;
    Proposition 25 (dictionary with Rosenthal's and
    Blute–Lamarche–Ruet's cyclic ∗-autonomous categories) — `l.4589`.
- **References** — `l.4595`. **Contents** — `l.4655`.

## What the source establishes

Everything below records what the source states (checked against
the vendored copy); every mathematical claim is CONJECTURED until
machine-checked.

**Abstract.** A dialogue category is a monoidal category equipped
with an exponentiating object ⊥ (its *tensorial pole*): every
object x acquires a left negation x ⊸ ⊥ and a right negation
⊥ ⟜ x, and x is *not* required to coincide with its double
negation. The paper formulates two non-commutative notions of
dialogue category — *helical* and *balanced* — and shows that the
category Mod(H) of left H-modules **of arbitrary dimension** over a
ribbon Hopf algebra H is a balanced dialogue category whose
tensorial pole is the underlying field k (Proposition 23),
recovering the well-known ribbon structure on the full subcategory
of finite-dimensional modules (Proposition 24).

**Framing.** The introduction positions the work between quantum
groups/low-dimensional topology (cyclic categories of Freyd–Yetter,
ribbon categories of Turaev, Shum, Joyal–Street) and the
tensorial-logic program: the duality A ↦ A* is not assumed
involutive, and the dialogue-categorical account is designed to
recover the topological notions at the involutive boundary. The
stated motivation for the balanced dialogue category is a braided,
twisted variant of tensorial logic — *ribbon logic* — whose free
balanced dialogue category has ribbon-logic formulas as objects and
ribbon-logic proofs (ribbon tangles) as morphisms.
