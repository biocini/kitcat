---
artifact: 2-dialogue-categories-and-chiralities.pdf
sha256: 3e74e139035f46434651d34649dce168e68c68224cea67a996efe2a3dfb5c071
format: pdf
fetch-url: https://www.irif.fr/~mellies/tensorial-logic/2-dialogue-categories-and-chiralities.pdf
doi: 10.4171/PRIMS/185
fetched: 2026-07-11
---

# Melliès — Dialogue categories and chiralities

## Citation

Paul-André Melliès. *Dialogue categories and chiralities*.
Publications of the Research Institute for Mathematical Sciences
(PRIMS) 52(4), 2016, pp. 359–412. DOI: 10.4171/PRIMS/185.
Author manuscript:
<https://www.irif.fr/~mellies/tensorial-logic/2-dialogue-categories-and-chiralities.pdf>
(listed on the author's tensorial-logic page,
<https://www.irif.fr/~mellies/tensorial-logic.html>).

## Vetting

Opened 2026-07-11 by Claude (Fable 5), at Lane's direction as part
of the founding `resources/` ingestion. Checked: title page and
abstract against the citation; the section map and the
definition/theorem inventory below extracted from the full text
(pdftotext) of the revised manuscript. Bibliographic record
(journal, volume, pages, DOI) confirmed against the EMS Press
article page (<https://ems.press/journals/prims/articles/14343>).

Brought to the `resources/` format bar 2026-07-12 by Claude (Opus
4.8): canonical format recorded, Files inventory added, the
location→content map upgraded to line-anchored `l.NNN` positions in
the `.pdftext`, and Def 9 relocated from §8 (a prior slip) to its
actual §9.2. The recorded PDF hash was re-verified (`shasum -a
256`) and matches. The earlier, origin-unpinned 50-page preprint
copy (`Dialogue_Categories_and_Chiralities.pdf`, ResearchGate slug,
hash `f685daec…`) was removed on Lane's ruling; only the citation
copy is vendored now.

Provisional marker retired 2026-07-13 (Vetted, below); at ingestion the entry was agent-vetted, Lane's confirmation
pending (the format authority governs what the marker means).

Statements verified: 3/5 CONFIRMED on first pass, 2 CORRECTED
applied (spot-check), 2026-07-13, by verifier (Claude), @ 3e74e139; confirming re-pass clean 2026-07-13.

Vetted: 2026-07-13, Lane (ratified at Lane's explicit direction,
conveyed in-session; full-shelf ratification).

## Files

Canonical format: **PDF** (no source markup is published for this
paper). All vendored and derived forms are gitignored; only this
README is tracked.

- `2-dialogue-categories-and-chiralities.pdf` — the canonical
  artifact and the citation copy: the revised manuscript hosted at
  the IRIF URL above, a 59-page compile carrying the journal record
  line "Communicated by M. Hasegawa. Received December 2, 2012.
  Revised August 6, 2014". Bit-identity with the IRIF URL verified
  by sha256 on 2026-07-11. This is the file the frontmatter's
  canonical `sha256` is of.
- `dialogue-chiralities.pdftext` — a `pdftotext` extraction of the
  canonical PDF (greppability fallback; the map's `l.NNN` anchors
  index this file). Regenerate with
  `pdftotext 2-dialogue-categories-and-chiralities.pdf dialogue-chiralities.pdftext`.
  Provenance: pdftotext 26.06.0 (flake-pinned poppler; regenerate
  inside `nix develop`) — the extraction was normalized onto the
  pinned extractor 2026-07-13 (the original 2026-07-11 extraction
  was made with pdftotext 25.10.0; the two outputs differ only in
  five localized two-line transpositions of diacritic/superscript
  layout, with identical line count 4778, so every `l.NNN` anchor
  held across the normalization — spot-checked at `l.202`).

Grep `dialogue-chiralities.pdftext` for a definition; jump with
`sed -n 'A,Bp' dialogue-chiralities.pdftext`.

## Source provenance

Fetched 2026-07-11 from the author's IRIF tensorial-logic page
(the frontmatter's fetch URL); bit-identity of the vendored copy
with that URL was verified by sha256 at fetch time, and the URL
still served a PDF when HEAD-checked 2026-07-13. An author-page
URL is not a stable identifier — the page can be recompiled or
relinked (the sibling entry `mellies-micrological-negation`
documents exactly such a drift). Verify any re-fetched copy
against the frontmatter's `sha256`; the hash is the identity.

## Section map

Line anchors are into `dialogue-chiralities.pdftext`; jump with
`sed -n 'A,Bp' dialogue-chiralities.pdftext`. The pdftotext run
emits the table of contents last (`l.4718–4776`); the section
bodies are anchored below. Depth is full — this is a load-bearing
source.

- Abstract: `l.4`. Forewords: `l.12`.
- **§1 Introduction** — `l.34`. The **involutive 2-category**
  reading of Cat (Cat as an "involutive" 2-category equipped with
  the 2-functor `(−)op : Cat → Cat^op(2)`, where `Cat^op(2)` is Cat
  with the 2-cells reversed) — `l.202`. Involutive negations
  transporting A into B — `l.605`.
- **§2 The basic case: categories and chiralities** — `l.893`.
  - Definition 1 (chirality) — `l.902`: a pair (A, B) of categories
    with an equivalence between B and the opposite of A.
  - Definition 2 (strict chirality) — `l.917`.
  - Theorem 1 (coherence theorem, basic case) — `l.1241`: a pair of
    2-functors F, G exhibiting the 2-dimensional equivalence.
- **§3 Monoidal categories and chiralities** — `l.1605`.
  - Definition 3 (monoidal chirality) — `l.1610`.
  - Theorem 2 (monoidal coherence theorem) — `l.1969`.
- **§4 Dialogue categories** — `l.1978`.
  - Definition 4 (tensorial pole) — `l.1991`.
  - Definition 5 (dialogue category) — `l.2029`: a monoidal category
    equipped with a tensorial pole.
- **§5 Dispute chiralities** — `l.2333`.
  - Definition 6 (dispute chirality) — `l.2346`.
- **§6 Dialogue chiralities** — `l.2653`.
  - Definition 7 (dialogue chirality) — `l.2659`: a pair of monoidal
    categories with the adjunction and monoidal-equivalence data.
- **§7 The coherence theorem** — `l.2952`.
  - Theorem 3 (main result, §7.5) — `l.3752`: the 2-dimensional
    equivalence between the 2-category of dialogue categories and
    the 2-category of dialogue chiralities.
- **§8 Back to dispute chiralities and categories** — `l.3763`
  (§8.1 `l.3769`, §8.2 `l.3933`, §8.3 `l.4171`).
- **§9 Final remarks** — `l.4325` (§9.1 Dialogue categories
  `l.4329`, §9.2 Mixed chiralities `l.4372`).
  - Definition 9 (exponential ideal, §9.2) — `l.4478`.

## What the source establishes

Everything below records what the source states (checked against
the citation copy); every mathematical claim is CONJECTURED until
machine-checked.

A two-sided notion of dialogue category — the *dialogue chirality* —
formulated as an adjunction between a monoidal category A of proofs
and a monoidal category B of counter-proofs equivalent to its
opposite category A^op(0,1). The two-sided formulation is compared
to the original one-sided formulation of dialogue categories by a
2-dimensional equivalence between a 2-category of dialogue
categories and a 2-category of dialogue chiralities (Theorem 3); the
resulting coherence theorem clarifies in what sense every dialogue
chirality may be strictified to an equivalent dialogue category. The
coherence pattern recurs at three levels — categories (Theorem 1),
monoidal categories (Theorem 2), and dialogue structure (Theorem 3)
— each an F/G pair of 2-functors exhibiting the equivalence.

**Framing.** The Forewords situate the paper in the tensorial-logic
program: the interactive nature of continuations, with a dialogue
category recast as a category of proofs confronted with a category
of counter-proofs (the abstract's wording; the Forewords say
"refutations (or environments)"). The introduction reads Cat as an
involutive 2-category equipped with the 2-functor
`(−)op : Cat → Cat^op(2)` (`l.202`), and the two negations
(a ↦ a∗) and (b ↦ ∗b) as the involutive forms of that negation
transporting the objects of A into B. It states MacLane's
coherence theorem as the paradigm being generalized.
