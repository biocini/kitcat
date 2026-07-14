---
artifact: kelly-mclane-conditions.pdf
sha256: a7f8d3080ddddf3fe8503958e734877d125b16586865ade092bc125fbcf8d8b2
format: scan
fetch-url: https://raw.githubusercontent.com/clementjacq/zg-cj-paper/e3db0fd5eedac314b64e3460c92378e4286f98c6/On%20MacLane%E2%80%99s%20Conditions%20for%20Coherence%20of%20Natural%20Associativities%20Commutativities%20Kelly%20_%2064.pdf
doi: 10.1016/0021-8693(64)90018-3
fetched: 2026-07-13
---

# Kelly — On MacLane's conditions for coherence

Kelly's six-page improvement of MacLane's coherence conditions for
natural associativities, commutativities, and identities: the paper
that trims MacLane's finite condition lists to their minimal cores
(pentagon + one unit triangle in the associativity/identities case)
by naturality-plus-cancellation derivations, and proves each trimmed
list irredundant by explicit sign-function countermodels on graded
abelian groups.

## Citation

G. M. Kelly. *On MacLane's Conditions for Coherence of Natural
Associativities, Commutativities, etc.* Journal of Algebra 1(4),
1964, pp. 397–402. Elsevier.
DOI: [10.1016/0021-8693(64)90018-3](https://doi.org/10.1016/0021-8693%2864%2990018-3).
Communicated by Saunders MacLane; received July 13, 1964. Author
affiliation: Department of Mathematics, University of Illinois,
Urbana, Illinois. (The paper prints "MacLane" solid, without the
space of modern usage; the citation keeps the printed form.)

## Vetting

PROVISIONAL. Ingested 2026-07-13 by Claude (Fable 5), the ingest
agent, at Lane's direction; the document was supplied by Lane via
institutional access (the source is paywalled). Checked: the full
six-page text was read from the PDF directly — the fine print
(diagram edge labels, the sign-function tables) from 300 dpi page
renders — and the conditions (1)–(10) and (3′), Theorems 1–10 with
the primed variants, the five proofs, the independence tables, and
both references were transcribed from it; the bibliographic header
(journal line, author, affiliation, communicated-by, received date)
was read from the title page; the DOI was located by web search,
checked to resolve (doi.org → Elsevier linkinghub, PII
0021869364900183), and cross-checked against a published
bibliography (LIPIcs TYPES 2019, which cites exactly this DOI for
this title, volume, and page range).

Re-extracted 2026-07-13 (the correction-patch pass, same day, by
Claude (Fable 5), the ingest agent, at Lane's direction): the
`.pdftext` was regenerated through the pinned chain and the tracked
correction patch was added as the chain's final step (see Files);
every line anchor in this README was re-computed against the
corrected extraction. The canonical PDF was not touched — its hash
was re-verified unchanged before and after the pass. Digest content
was not altered in this pass (anchors only).

Statements verified: 46/46 CONFIRMED (every statement; all 21
countermodel rows re-read at 300 dpi in both passes; the audit's
six corrections re-verified against the source in the confirming
pass), 2026-07-13, by verifier (Claude, Fable 5), @ a7f8d308.
Audit trail: 40/46 on the first pass with 6 CORRECTED (2 MAJOR in
entry commentary, 0 in transcription), corrections applied
verbatim by the dispatching lead; the re-extraction pass (the
tracked correction patch) preceded the confirming pass, which
re-verified corrections, anchors, patch honesty, and the
frontmatter identity fresh.

## Files

Canonical format: **PDF** (a scan of the 1964 letterpress printing;
no source markup exists for an article of this vintage). All
vendored and derived forms are gitignored; only this README and the
correction patch are tracked.

- `kelly-mclane-conditions.pdf` — the canonical artifact: the
  6-page publisher scan (pp. 397–402), title-page header "JOURNAL
  OF ALGEBRA, 1, 397-402 (1964)". This is the file the frontmatter's
  `sha256` is of. (The filename spells "mclane" — it is kept as supplied;
  the hash, not the name, is the identity.)
- `kelly-mclane-conditions.pdftext` — the corrected text
  extraction, 242 lines: the raw `pdftotext` output with the
  tracked correction patch applied as the chain's final step.
  Regenerate byte-identically (inside `nix develop`) with

  ```
  pdftotext kelly-mclane-conditions.pdf kelly-mclane-conditions.pdftext
  patch kelly-mclane-conditions.pdftext kelly-mclane-conditions.pdftext.patch
  ```

  Provenance: pdftotext 26.06.0 (flake-pinned poppler) over the
  PDF's embedded text layer, then GNU patch 2.8 applying the
  tracked patch (generated with GNU diffutils 3.12, `diff -U0`).
  Not OCR-derived (see the chain record below). Page separators
  are form feeds.
- `kelly-mclane-conditions.pdftext.patch` — the **tracked**
  correction patch (21 hunks, `diff -U0` unified format): custody
  metadata, committed beside this README. It corrects garbled
  load-bearing content in the raw extraction; every hunk was
  verified against a 300 dpi page render (`pdftoppm -r 300 -png`,
  poppler 26.06.0) by visual reasoning before it was written, and
  no hunk writes content its page render does not show. Corrected
  blocks are marked in-file with `[patch: …]` lines naming their
  render; diagram (8)'s faint edge labels carry an explicit
  faintness note pinning the reading to the printed remark on
  p.399. Correction sites, each with the render that verified it:
  - the title block, restored (journal line, title, author,
    affiliation, communicated-by, received date) — p.397;
  - diagram (1), the pentagon — p.397;
  - diagrams (2)–(8), with (4) as printed equation — p.398;
  - diagrams (9), (10); the f-definition remark; diagram (3′) —
    p.399;
  - Theorem 1–5 statements, de-interleaved — p.399;
  - Theorem 3′, 6, 7 statements — p.399;
  - Theorem 5′, 8, 4′, 4″, 9, 4‴, 10 statements, de-interleaved
    (Theorem 10's conclusion "(2)", dropped by the extractor,
    restored) and the Theorem 6 naturality square — p.400;
  - the Theorem 6 proof conclusion; the Theorem 7 lead-in and
    five-region diagram (dropped whole by the extractor) — p.400;
  - the cancellation-principle paragraph; the Theorem 8, 9, 10
    proof paragraphs — p.401;
  - the sign-function definitions and brevity conventions — p.401;
  - the best-possible tables for Theorems 1, 2, 3′ — p.401;
  - the tables for Theorems 4′, 4″, 4‴, 5′, and the references —
    p.402.

Repair/OCR chain record (2026-07-13, inside `nix develop`): `qpdf`
12.3.2 `--check` reports only linearization hint-table warnings —
no structural damage, so no repair step was applied. `ocrmypdf`
17.8.0 `--redo-ocr` was evaluated against the embedded text layer
and **rejected**: its output carries both the original layer and
the new OCR text (nearly every printed line appears twice; a
1243-line extraction against 497), which makes line anchors
ambiguous, and its glyph recovery is marginal — the load-bearing
sites stay garbled either way ("G. M. KrLLy", `«, y, €, ¢` for
α, γ, ε, φ). The embedded text layer was kept as the extraction
base; the tracked patch carries the corrections.

**The corrected extraction transcribes the load-bearing sites; the
PDF remains the readable copy for everything else.** The raw 1964
letterpress extraction destroys the twelve displayed diagrams (the
ten numbered condition diagrams — (4) prints as an equation — plus
the Theorem 6 naturality square and the Theorem 7 five-region
diagram, the latter dropped without a trace), garbles glyphs
systematically (ξ→`[`, η→`7`/`q`, φ→`4`/`+`, ⇔→`e`/`o`/`u`/`G`,
"and"→"rind"/"ad"), interleaves adjacent theorem statements, and
drops the title block. The patch corrects exactly these
load-bearing sites as render-verified transcriptions. Residual
garbling remains in un-patched prose (the p.397 setup paragraph,
running heads, the p.401 independence prose): there, anchors
locate, and the PDF is read directly.

## Source provenance

Paywalled at the publisher: the citation locator is the DOI
(frontmatter `doi:`), which resolves to the ScienceDirect article
page (PII 0021869364900183); retrieving the PDF there requires an
institutional license. The vendored copy was supplied by Lane,
2026-07-13, who located it in a third-party GitHub repository; that
commit-pinned copy (the frontmatter `fetch-url`) was re-fetched and
verified byte-identical to the canonical hash the same day, so it
serves as the public re-fetch surface — with the caveat that a
third-party host guarantees no persistence; the frontmatter
`sha256` remains the identity.

## Section map

Line anchors are into `kelly-mclane-conditions.pdftext` — the
corrected extraction (raw `pdftotext` + the tracked patch;
regenerate per Files); jump with
`sed -n 'A,Bp' kelly-mclane-conditions.pdftext`. Page breaks (form
feeds) in the extraction: p.397 = `l.1–60`, p.398 = `l.61–85`,
p.399 = `l.86–120`, p.400 = `l.121–159`, p.401 = `l.160–214`,
p.402 = `l.215–242`. The paper has no numbered sections; the map
is by content block. Depth is full — a mechanization-adjacent
source. Blocks marked `[patch: …]` are render-verified
transcriptions (see Files).

- Title block — `l.1–8` (p.397, patch-restored).
- Setup: 𝒜, T, the data a, c, e, f; MacLane's coherence notion;
  the paper's aim — `l.10–53` (p.397; un-patched, garbled prose —
  read the PDF for the wording).
- Condition (1), the pentagon — `l.55–59` (p.397, patch block).
- Conditions (2)–(8) — `l.62–84` (p.398, patch blocks; (2) at
  `l.63`, (3) at `l.66`, (4) at `l.69`, (5) at `l.70`, (6) at
  `l.73`, (7) at `l.76`, (8) at `l.79` with its faint-label note
  at `l.82–84`).
- Conditions (9), (10); the f := e∘c remark; variant (3′) —
  `l.87–101` (p.399; (9) at `l.88`, (10) at `l.91`, remark at
  `l.95–97`, (3′) at `l.99`).
- MacLane's Theorems 1–4 and Kelly's Theorem 5 — `l.103–111`
  (p.399; Thm 1 `l.105`, Thm 2 `l.106`, Thm 3 `l.107`, Thm 4
  `l.108`, Thm 5 `l.111`).
- Theorems 3′, 6, 7 (the associativity/identities reduction) —
  `l.112–119` (p.399; Thm 3′ `l.115`, Thm 6 `l.116`, Thm 7
  `l.117`).
- Theorems 5′, 8, 4′, 4″, 9, 4‴, 10 (the symmetric reductions) —
  `l.125–138` (p.400; Thm 5′ `l.129`, Thm 8 `l.130`, Thm 4′
  `l.132`, Thm 4″ `l.134`, Thm 9 `l.135`, Thm 4‴ `l.137`, Thm 10
  `l.138`).
- Proofs of Theorems 6–10 — `l.139–184` (pp.400–401; Thm 6 at
  `l.140–147` with its naturality square at `l.141–142`, Thm 7 at
  `l.148–175` with the five-region diagram at `l.149–158` and the
  cancellation principle at `l.172–175`, Thm 8 at `l.176–179`,
  Thm 9 at `l.180–181`, Thm 10 at `l.183–184`).
- Independence machinery: graded abelian groups, the sign
  functions — `l.185–204` (p.401; the sign-function definitions,
  patch-transcribed, at `l.195–199`).
- Best-possible tables — `l.205–237` (pp.401–402, patch blocks;
  Thm 1 `l.206`, Thm 2 `l.207`, Thm 3′ `l.211`, Thm 4′ `l.217`,
  Thm 4″ `l.222`, Thm 4‴ `l.229`, Thm 5′ `l.233`).
- References — `l.238–242` (p.402, patch-transcribed).

## Content digests

Statement-level, in the source's notation. Every mathematical claim
below is CONJECTURED until machine-checked.

### Setting and the coherence notion (`l.10–53`, p.397)

𝒜 a category, T a covariant bifunctor from 𝒜 × 𝒜 to 𝒜; write AB
for T(A, B) and fg for T(f, g). The data, each a **natural
isomorphism**:

- a : A(BC) → (AB)C — a *natural associativity* for T;
- c : AB → BA — T (naturally) commutative;
- e : KA → A — the fixed object K of 𝒜 a left identity;
- f : AK → A — K a right identity.

Coherence (MacLane [1, 2]): given one or more of a, c, e, f, the
given isomorphisms are *coherent* if every natural automorphism
manufactured from them and their inverses alone (together with
identity morphisms) is the identity automorphism. The formal
definition is in [2]; conditions (1)–(10) below belong to the
infinite set of statements whose conjunction is the assertion of
coherence. MacLane showed in [2] that coherence is equivalent to
finitely many of these; the paper's object is to show some of his
lists contain redundant conditions.

### The conditions (pp.397–399)

Each condition asserts that the stated diagram commutes, for all
objects. Diagram content transcribed from the PDF (the raw
extraction destroys them; the corrected extraction carries
render-verified transcriptions at the anchors — see Files).

- **(1)** (`l.56`, p.397) — the pentagon:
  `A[B(CD)] —a→ (AB)(CD) —a→ [(AB)C]D` equals
  `A[B(CD)] —1a→ A[(BC)D] —a→ [A(BC)]D —a1→ [(AB)C]D`.
- **(2)** (`l.63`, p.398) — `AB —c→ BA —c→ AB` is the identity.
- **(3)** (`l.66`, p.398) — the hexagon:
  `A(BC) —a→ (AB)C —c→ C(AB) —a→ (CA)B` equals
  `A(BC) —1c→ A(CB) —a→ (AC)B —c1→ (CA)B`.
- **(4)** (`l.69`, p.398) — `e = f : KK → K`.
- **(5)** (`l.70`, p.398) — left-unit triangle:
  `e1 ∘ a = e : K(BC) → BC`, where `a : K(BC) → (KB)C` and
  `e1 : (KB)C → BC`.
- **(6)** (`l.73`, p.398) — middle-unit triangle:
  `f1 ∘ a = 1e : A(KC) → AC`, where `a : A(KC) → (AK)C` and
  `f1 : (AK)C → AC`. (This is the triangle now standard in the
  definition of a monoidal category.)
- **(7)** (`l.76`, p.398) — right-unit triangle:
  `f ∘ a = 1f : A(BK) → AB`, where `a : A(BK) → (AB)K` and
  `f : (AB)K → AB`.
- **(8)** (`l.79`, p.398) — `f = e ∘ c : AK → A`, where
  `c : AK → KA` and `e : KA → A`. (The triangle defining f from e
  and c; the printed edge labels are faint in the scan, but the
  reading is pinned by the remark at `l.95–97`: (8) is how f is
  *defined* in terms of e and c when f is not given.)
- **(9)** (`l.88`, p.399) —
  `e1 ∘ c1 ∘ a = 1e : A(KC) → AC`, where `a : A(KC) → (AK)C`,
  `c1 : (AK)C → (KA)C`, `e1 : (KA)C → AC`.
- **(10)** (`l.91`, p.399) — `e ∘ c = e : KK → K`.
- Remark (`l.95–97`, p.399): (9) and (10) are what (6) and (4),
  respectively, become if f is not given but is *defined* in terms
  of e and c by (8).
- **(3′)** (`l.99`, p.399) — a variant of (3), equivalent to it
  in the presence of (2): both routes `A(CB) → (AC)B` agree —
  `A(CB) —a→ (AC)B` directly, and
  `A(CB) —1c→ A(BC) —a→ (AB)C —c→ C(AB) —a→ (CA)B —c1→ (AC)B`.
  (Relative to (3), both c-labelled edges run in the opposite
  sense: 1c here is A(CB) → A(BC) and c1 is (CA)B → (AC)B —
  instances of c at swapped arguments, not formal inverses. The
  source: "obviously equivalent to it in the presence of (2)".)

### MacLane's theorems and Kelly's reductions (pp.399–400)

MacLane's results in [2], as stated by the paper ("⇔" reads "are
coherent if and only if the listed conditions hold"):

- **Theorem 1** (`l.105`) — a is coherent ⇔ (1).
- **Theorem 2** (`l.106`) — a and c ⇔ (1), (2), (3).
- **Theorem 3** (`l.107`) — a, e, and f ⇔ (1), (4), (5), (6),
  (7).
- **Theorem 4** (`l.108`) — a, c, and e ⇔ (1), (2), (3), (5), (9),
  (10).

Kelly's contributions:

- **Theorem 5** (`l.111`) — a, c, e, and f ⇔ (1), (2), (3),
  (4), (5), (6), (8). (The four-datum case is not considered in
  [2]; the paper notes Theorem 4 is clearly equivalent to this.)
- **Theorem 3′** (`l.115`) — a, e, and f are coherent ⇔ (1)
  and (6). Theorems 1 and 2 are best possible, but Theorem 3
  improves to this: of MacLane's five conditions, only the
  pentagon and the middle triangle remain; (4), (5), (7) are
  derivable. Because:
- **Theorem 6** (`l.116`) — (5) and (6) ⇒ (4); whence by
  symmetry (6) and (7) ⇒ (4).
- **Theorem 7** (`l.117`) — (1) and (6) ⇒ (5); whence by
  symmetry (1) and (6) ⇒ (7). (The symmetry: (1) is unchanged if a
  is replaced by a⁻¹ and AB by BA.)
- **Theorem 5′** (`l.129`) — a, c, e, and f are coherent ⇔
  (1), (2), (3), and (6). (Theorem 5 improved: the source drops
  (4) and (5) "but in fact still more is true" — (8) drops too, by
  Theorem 8.) Because:
- **Theorem 8** (`l.130`) — (2), (3), (6), and (7) ⇒ (8).
- **Theorem 4′** (`l.132`) — a, c, and e are coherent ⇔ (1),
  (2), (3), and (9). (From Theorem 5′, a fortiori.)
- **Theorem 4″** (`l.134`) — a, c, and e are coherent ⇔ (1),
  (2), (3), and (5). Because:
- **Theorem 9** (`l.135`) — (2), (3), (5), and (8) ⇒ (6).
- **Theorem 4‴** (`l.137`) — a, c, and e are coherent ⇔ (1),
  (3′), and (9): replacing (3) by (3′) does a little better than
  Theorem 4′, dropping (2). Because:
- **Theorem 10** (`l.138`) — (3′), (6), (7), and (8) ⇒ (2).

### The proofs of Theorems 6–10 (`l.139–184`, pp.400–401)

The derivations are naturality-plus-cancellation arguments; the
exact hypotheses each uses are listed, since that is what a
consumer of these reductions must match.

- **Theorem 6** (`l.140–147`): naturality of e applied at
  `e : KK → K` gives a commuting square
  `K(KK) —e→ KK`, `1e ↓`, `KK —e→ K`; whence
  `1e = e : K(KK) → KK`, **since e is an isomorphism** (the
  cancellation). Putting B = C = K in (5) and A = C = K in (6) and
  using this identity gives `e1 = f1 : (KK)K → KK`; the naturality
  of f then yields `e = f : KK → K`. Uses: (5), (6), naturality of
  e and of f, e invertible.
- **Theorem 7** (`l.148–175`): a five-region diagram on
  `A[K(CD)] —a→ (AK)(CD) —a→ [(AK)C]D` with inner vertices A(CD)
  and (AC)D: the outside commutes by (1), regions II and IV by
  (6), regions III and V by the naturality of a; hence region I —
  the A-tensored image of (5) at (C, D), i.e.
  `1(e1) ∘ 1a = 1e : A[K(CD)] → A(CD)` — commutes.
  Putting A = K then gives (5) itself, because — e being both
  natural and an isomorphism — **one can conclude
  `h = k : P → Q` from `1h = 1k : KP → KQ`** (the paper's
  cancellation principle, stated in exactly this form). Uses: (1),
  (6), naturality of a and of e, e invertible.
- **Theorem 8** (`l.176–179`): similar to Theorem 7 — put B = K in
  (3), use (6), (7), and the naturality of c to infer a diagram
  differing from (8) in that the sense of c is reversed; (2) then
  gives (8). Uses: (2), (3), (6), (7), naturality of c.
- **Theorem 9** (`l.180–181`): put A = K in (3); using (5), (8)
  with the sense of c reversed — a consequence of (8) and (2) —
  and the naturality of c, we get (6). Uses: (2), (3), (5), (8),
  naturality of c.
- **Theorem 10** (`l.183–184`): put B = K in (3′); using (6), (7),
  (8), and the naturality of c, we get (2). Uses: (3′), (6), (7),
  (8), naturality of c.

### Independence: the best-possible results (`l.185–242`, pp.401–402)

Theorems 1, 2, 3′, 4′, 4″, 4‴, 5′ are *best possible*: the
conditions in each list are independent. The model: 𝒜 = graded
abelian groups and homogeneous maps of degree 0; T = the usual
tensor product of graded abelian groups; K = the infinite cyclic
group in degree 0. Define (ξ, η, ζ the degrees of x, y, z; α, γ,
ε, φ functions of the degrees, varying per example — the source
says only "functions"; they occur as exponents of −1):

- a(x ⊗ (y ⊗ z)) = (−1)^α(ξ,η,ζ) (x ⊗ y) ⊗ z
- c(x ⊗ y) = (−1)^γ(ξ,η) y ⊗ x
- e(1 ⊗ x) = (−1)^ε(ξ) x
- f(x ⊗ 1) = (−1)^φ(ξ) x

Shorthand: α = 1 means α(ξ,η,ζ) = 1 for all arguments, γ = ξ means
γ(ξ,η) = ξ, etc.; (1)T / (2)F denote the truth of (1) and
falsehood of (2). The tables (transcribed from the PDF; the
extraction garbles them):

- **Theorem 1** (`l.206`): α = 1 gives (1)F.
- **Theorem 2** (`l.207–210`):
  (i) α = 1, γ = 1: (1)F, (2)T, (3)T.
  (ii) α = 0, γ = ξ: (1)T, (2)F, (3)T.
  (iii) α = 0, γ = 1: (1)T, (2)T, (3)F.
- **Theorem 3′** (`l.211–213`):
  (i) α = 1, ε = 1, φ = 0: (1)F, (6)T.
  (ii) α = 0, ε = 0, φ = 1: (1)T, (6)F.
- **Theorem 4′** (`l.217–221`):
  (i) α = 1, γ = 1, ε = 0: (1)F, (2)T, (3)T, (9)T.
  (ii) α = 0, γ = ½ξ(η² − η), ε = 0: (1)T, (2)F, (3)T, (9)T.
  (iii) α = 0, γ = ½ξη(ξ + η), ε = 0: (1)T, (2)T, (3)F, (9)T.
  (iv) α = 0, γ = 0, ε = ξ: (1)T, (2)T, (3)T, (9)F.
- **Theorem 4″** (`l.222–228`):
  (i) α(1,2,7) = α(2,7,1) = α(7,2,1) = α(1,7,2) = 1 and α(ξ,η,ζ) =
  0 for all other triples; γ = 0, ε = 0: (1)F — apply to
  x ⊗ [y ⊗ (z ⊗ t)] where x, y, z, t have degrees 1, 2, 3, 4
  respectively — with (2)T, (3)T, (5)T.
  (ii) α = 0, γ = ξ, ε = 0: (1)T, (2)F, (3)T, (5)T.
  (iii) α = ξ, γ = 0, ε = 0: (1)T, (2)T, (3)F, (5)T.
  (iv) α = 0, γ = 0, ε = ξ: (1)T, (2)T, (3)T, (5)F.
- **Theorem 4‴** (`l.229–232`):
  (i) α = 1, γ = 1, ε = 0: (1)F, (3′)T, (9)T.
  (ii) α = 0, γ = η, ε = 0: (1)T, (3′)F, (9)T.
  (iii) α = 0, γ = 0, ε = ξ: (1)T, (3′)T, (9)F.
- **Theorem 5′** (`l.233–237`):
  (i) α = 1, γ = 1, ε = 0, φ = 1: (1)F, (2)T, (3)T, (6)T.
  (ii) α = 0, γ = ξ, ε = 0, φ = 0: (1)T, (2)F, (3)T, (6)T.
  (iii) α = 0, γ = 1, ε = 0, φ = 0: (1)T, (2)T, (3)F, (6)T.
  (iv) α = 0, γ = 0, ε = 0, φ = 1: (1)T, (2)T, (3)T, (6)F.

### References (`l.238–242`, p.402)

1. MacLane, S., "Categorical Algebra." Boulder Colloquium
   Lectures, 1963.
2. MacLane, S., Natural associativity and commutativity. *Rice.
   Univ. Stud.* 49 (1963), 28–46. (The period after "Rice" is the
   printed form, kept per this entry's transcription practice.)

## What the source establishes

Everything below records what the source states; every mathematical
claim is CONJECTURED until machine-checked.

Against MacLane's finite lists of coherence conditions [2], the
paper proves five redundancy theorems (Theorems 6–10) and uses them
to trim each list to an independent core:

- Associativity + two-sided identities (a, e, f): MacLane's five
  conditions (1), (4), (5), (6), (7) reduce to **two — the
  pentagon (1) and the middle unit triangle (6)** (Theorem 3′).
  The unit conditions e = f on KK, the left triangle (5), and the
  right triangle (7) are all derivable.
- Symmetry added: with all four data (a, c, e, f) the seven
  conditions of Theorem 5 reduce to **(1), (2), (3), (6)**
  (Theorem 5′); for the three-datum case a, c, e, Theorems 4′ /
  4″ / 4‴ give (1), (2), (3), (9) / (1), (2), (3), (5) /
  (1), (3′), (9) — the last trading (3) for (3′) to drop (2).

The key cancellation principle, stated once in the proof of
Theorem 7: e natural and invertible allows concluding
`h = k : P → Q` from `1h = 1k : KP → KQ` — an identity-flanked
equation is stripped of its K-factor. (Theorem 6's proof cancels
the isomorphism e directly; the proofs of Theorems 8–10 run on
prior conditions plus the naturality of c.) The best-possible tables certify that no further
trimming is possible: explicit (−1)-sign structures on graded
abelian groups witness the independence of every retained
condition, including a degree-supported associator breaking only
the pentagon (Theorem 4″ (i)).

Field status: this is the paper standardly credited with reducing
MacLane's unit axioms to the single triangle — the pentagon +
triangle presentation of monoidal categories now universal — and
Kelly's later coherence work builds on it.
