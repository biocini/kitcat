---
artifact: bentzen-naive-cubical.tar.gz
sha256: 95621e6e1a3cb378d8a0b3ab6ce247ace410a32fd1ab0f1f4442d3a613a9b067
format: latex-source
fetch-url: https://arxiv.org/e-print/1911.05844
metadata-url: https://arxiv.org/abs/1911.05844
doi: 10.1017/S096012952200007X
version: v2
fetched: 2026-07-13
sha256-inner: 658dffb6119c3c27df284a53268a6001ce21d5a4f54ff6003dbc4caf4fcbd2fe
---

# Bentzen — Naive cubical type theory

An informal but rigorous ("naive") presentation of cartesian cubical
type theory, the cubical analogue of the HoTT book's informalization
program: paths as functions out of the interval, the Kan operations
(transport and composition), derived weak connections, the cubical
groupoid laws by explicit composition scenarios, dependent paths and
heterogeneous composition, a derivation of path induction, and the
Eckmann–Hilton duality. The implicit formal foundation is the
cartesian cubical type theory of Angiuli, Brunerie, Coquand,
Favonia, Harper, and Licata.

Load declaration: foundational-reference tier, held at full digest
depth — the cubical-reasoning companion to the sibling entry
`resources/rijke-hott/`: that entry fixes the univalent-mathematics
vocabulary in the Book-HoTT style; this one fixes the cubical idiom
(the interval, path types with strict boundaries, transport and
composition reasoning, fillers, connections). The map and digests
below therefore run at statement level over the whole of the
paper's technical content.

## Citation

Bruno Bentzen. *Naive cubical type theory*. arXiv:1911.05844
[cs.LO], v2, 9 May 2021 (v1: 13 November 2019).
<https://arxiv.org/abs/1911.05844>. Journal reference (per the abs
page, opened 2026-07-13): *Mathematical Structures in Computer
Science*, 31, pp. 1205–1231, 2021; DOI
10.1017/S096012952200007X (Cambridge University Press). Author
affiliation (per the paper, `ictt.tex:119`): Carnegie Mellon
University (bbentzen@andrew.cmu.edu).

## Vetting

Ingested 2026-07-13 by Claude (Fable 5) at Lane's
direction, via the ingestion protocol: the arXiv LaTeX e-print
fetched directly, the canonical artifact hashed and checked stable
across two independent fetches, the metadata (title, author,
subjects, v1/v2 submission history, related DOI) checked against
<https://arxiv.org/abs/1911.05844>, and the extracted source read
in full (every line) for the map and digests below.

Depth directive (Lane, 2026-07-13): foundational-reference tier —
statement-level content digests across the whole technical content,
matching the depth model of the sibling `resources/rijke-hott/`
entry; the entry-statement audit is expected to run at full depth
(every digest statement, not a spot-check).

Statements verified: 57/57 CONFIRMED (full depth — every
content-digest statement; +4/4 source notes), 2026-07-13, by
verifier (Claude, Fable 5), @ 95621e6e. Audit report:
six MINOR corrections applied verbatim by the dispatching lead
and confirmed by a re-pass the same day (0 FATAL, 0 MAJOR on both
passes); the audit and re-pass records are session artifacts of
2026-07-13. Lane's discretion (ratify / spot-audit / veto) is
open, self-initiated per the contract.

Vetted: 2026-07-13, Lane (ratified at Lane's explicit direction,
conveyed in-session; full-shelf ratification).

## Source notes

Small source blemishes recorded so extraction does not trip on
them; the digests below transcribe each printed statement as-is.

- Duplicate label — `\label{def:transport}` appears on both Lemma
  3.1.1 (`ictt.tex:406`) and Lemma 3.1.2 (`ictt.tex:425`). No `\ref`
  to it occurs anywhere in the source, so nothing is misresolved;
  cite by the line anchors here, not by label.
- Involution orientation — Lemma 4.2.5 (`ictt.tex:873`) states
  `inv_p : path(p, (p⁻¹)⁻¹)`, from `p` to `(p⁻¹)⁻¹`; §5.3 uses the
  reversed orientation, from `(p⁻¹)⁻¹` to `p` — at `ictt.tex:1234`
  (the degenerate-line restatement), `:1244` (`inv_A` printed as a
  path from `(A⁻¹)⁻¹` to `A`), and `:1251` (Lemma 5.3.1's
  statement). The two orientations are interconvertible by path
  inversion (Lemma 3.2.1); the digests transcribe each location as
  printed.
- Proof-prose slip — the funext proof (`ictt.tex:358`) says the
  constructed path lives "in A → B" while the ambient type is the
  dependent `Π(x:A) B(x)`; the adjacent display (`:360`) annotates
  the abstraction as `λi.λx.(H(x)(i)) : Π(x:A) B(x)`, missing the
  `𝕀 →` prefix — the same slip family; the theorem statement
  (`:351–356`) is unaffected.
- Subscript slip — the right-vs-left asymmetry prose
  (`ictt.tex:792`) prints "just in case `q` is `refl_a`" where the
  following sentence on the same line (`q :≡ refl_b`)
  evidences an intended `refl_b`; the §4.2 digest renders the
  clause neutrally ("just in case `q` is refl").
- Inert macro slip — `ictt.tex:99` defines `\ff` as `\mathsf{tt}`
  (evidently intended `\mathsf{ff}`); `\ff` is never used in the
  body, so no printed content is affected.

## Files

Canonical format: **LaTeX source** (an arXiv e-print). All vendored
and derived forms are gitignored; only this README is tracked.

- `bentzen-naive-cubical.tar.gz` — the canonical artifact (the
  arXiv e-print tarball, a gzip-compressed tar with two members).
  This is the file the frontmatter's canonical `sha256` is of.
- `ictt.tex` — the extracted LaTeX source (the source's own
  internal filename), 1546 lines. **This is the file the reader
  greps**; jump with `sed -n 'A,Bp' ictt.tex`. Re-extract with
  `tar xzf bentzen-naive-cubical.tar.gz`.
- `ictt.bbl` — the compiled bibliography shipped in the e-print
  (21 items; no `.bib` is included — `\bibliography{ref}` at
  `ictt.tex:1543` resolves through this `.bbl`). Use it to resolve
  the citation keys named in the digests ([cartesian], [cchm],
  [bch14], [blm21], [ch], [chm], [angiuli2019computational],
  [hottbook], [lumsdaine2010weak], …).

## Source provenance

Fetched directly from arXiv by stable identifier, 2026-07-13; the
frontmatter carries the e-print fetch URL, the abs metadata URL,
and the identity hashes (canonical tarball plus the inner-tar
fallback). The canonical hash was checked stable across two
independent arXiv fetches. Version pin **v2** — the latest arXiv
version as of 2026-07-13 (submission history:
`[v1] Wed, 13 Nov 2019 22:31:35 UTC`,
`[v2] Sun, 9 May 2021 21:58:26 UTC`), so the unversioned e-print
URL currently serves v2; should a later version ever appear, pin
explicitly by appending `v2` to the e-print URL.

## Section map

All anchors are into `ictt.tex` (the single source file). Numbering
note: the source's preamble (`ictt.tex:30–34`) declares the theorem
counter per **subsection** (`\newtheorem{theorem}{Theorem}[subsection]`)
with `lemma`/`corollary`/`definition`/`example` sharing it (a
separate `remark` counter exists but no remark environment occurs);
the vendored source prints no numbers, so the numbers below were
computed by counting environments per subsection. The published
journal version may number differently — cite by the line anchors
here.

Notation transcription (used throughout this entry, matching the
source's rendering): the interval is `𝕀` with endpoints `0`, `1`;
universes `𝒰`; `path_A(a,b)` and `pathd_A(a,b)` are the path and
dependent path types; path abstraction is `λi.a`; `refl_a`;
inversion `p⁻¹`; the source's concatenation symbol (a small filled
square, `\sq`) is transcribed `∙`, its whiskerings `\rsq`/`\lsq` as
`∙ᵣ`/`∙ₗ`; the source's transport notation (squiggly arrow, `\lto{i}{j}`)
is transcribed `a^{i⇝j}_A`; the derived meet, halfway meet, and join are
`p(i ∧ j)`, `p(i ∧* j)`, `p(i ∨ j)`; fillers `fill_j(p)`; the
source's `\not\equiv` is transcribed `≢`.

**Front matter:** `:30–35` the `\newtheorem` block; `:115` `\title`;
`:117–120` author and affiliation; `:152–154` abstract.

**§1 Introduction** (`:161`):
- `:164–170` — cubical type theory as the constructive alternative
  to axiomatic HoTT; axioms block computation.
- `:173–177` — the naive type theory program (Halmos; Constable;
  Altenkirch): informal but in-principle formalizable.
- `:179–187` — the two expected benefits (accessibility;
  informal-proof practice closer to mathematicians', easier
  mechanization).
- `:189–191` — the HoTT book as the naive presentation of
  axiomatic HoTT.
- `:193–199` — the paper's goal: a comparably rigorous naive
  presentation of cubical type theory; path induction deliberately
  avoided in favor of purely cubical arguments.
- `:201` — the foundation: cartesian cubical type theory
  [cartesian], on the free finite-product category on an interval
  object [awodey2018cubical] — faces, degeneracies, symmetries,
  diagonals; no connections or reversals (unlike De Morgan
  [cchm, chm]).
- `:203–205` — paper outline; self-contained, HoTT familiarity
  assumed.

**§2 The cubical point of view** (`:208`):
- `:211–224` — cubes as the basic shapes; the homotopical-intuition
  dictionary (`:213`); the interval type (`:218`); paths as
  functions out of the interval (`:222–224`).
- **§2.1 The type of paths** (`:227`): line type `𝕀 → A` (`:232`);
  path type formation (`:234`; terminology endnote `:234–235`);
  application and endpoint equalities (`:237–239`); abstraction
  (`:241`); β (`:245–247`); η (`:250–252`, flagged crucial for path
  induction at `:256`).
- **§2.2 How we should think of paths** (`:258`): visualization —
  points, lines (`:265–271`), squares with the face conventions
  (`:275–285`), cubes and hypercubes (`:289`); applies to types,
  which are terms of universes (`:289`).
- **§2.3 How can we use paths?** (`:291`): Lemma 2.3.1 (reflexivity
  path) `:301`; Lemma 2.3.2 (function application, ap) `:314`;
  strict functoriality of ap `:336–345`; Theorem 2.3.3 (function
  extensionality) `:351`.

**§3 There are enough paths** (`:367`):
- `:370–384` — why Kan operations: path induction is rejected as
  the fundamental cubical reasoning principle; transport and
  composition imposed as primitives [cartesian, afh]; each type
  computes them on its own constructors.
- **§3.1 Transportation along paths** (`:388`): the transport
  primitive and strict static transport (`:395`); non-strictness
  along degenerate lines (`:398–402`); Lemma 3.1.1 (transport along
  a path, `p_*`) `:406`; Lemma 3.1.2 (`(refl_a)_*` is the identity
  up to a path) `:425`.
- **§3.2 Composition of paths** (`:440`): the composition primitive
  — open boxes, composite, filler, cap/tube vocabulary, composition
  scenarios (`:442–461`); Lemma 3.2.1 (path inversion) `:469`;
  Definition 3.2.2 (filler notation `fill_j`) `:498`; Lemma 3.2.3
  (path concatenation) `:508`; cartesian diagonal specification
  remark (`:536–538`).
- **§3.3 The interval is not Kan** (`:540`): `λi.i : path_𝕀(0,1)`
  (`:544`); the interval as a pretype; the antecedent-only
  convention (`:546–548`).

**§4 Two-dimensional constructions** (`:551`):
- Standing proof-reading convention (`:687`): from here on the
  source "may omit uses of path abstraction without further
  comment" and leaves cap/tube adjacency checks to the reader —
  the composition scenarios transcribed from §4.2 on elide
  abstraction steps and adjacency conditions by this declared
  policy (§4.1's proofs precede the declaration and are spelled
  out in full).
- **§4.1 Weak connections** (`:557`): Lemma 4.1.1 (Meet) `:564`;
  two-extent composition mechanics (`:580–582`); the
  cube-seen-from-above diagram convention (`:584–598`); the
  halfway-meet + correction-cube proof (`:602–641`); the
  diagonal-improvement remark (`:643`); Lemma 4.1.2 (Join) `:645`.
- **§4.2 The groupoid laws** (`:690`): the globular representation
  of path equality (`:693–703`); Lemma 4.2.1 (right unit, `ru`)
  `:707`; Lemma 4.2.2 (left unit, `lu`; the helper square γ)
  `:719`; the right-vs-left asymmetry discussion (`:778–792`);
  Lemma 4.2.3 (right inverse, `rc`) `:796`; Lemma 4.2.4 (left
  inverse, `lc`) `:833`; Lemma 4.2.5 (involution, `inv`) `:870`;
  Lemma 4.2.6 (associativity, `assoc`) `:909`; higher-groupoid
  remark (`:981–983`).

**§5 Dependent paths** (`:988`):
- `:991` — type lines `A : 𝕀 → 𝒰`; the non-dependent restriction.
- **§5.1 The dependent path type** (`:993`): the `pathd` rules
  (`:995–1005`); the meet's exact dependent type, worked
  (`:1009–1034`); the extension-types remark (`:1036`).
- **§5.2 Heterogeneous composition** (`:1038`): type-line inversion
  and its typing inferences (`:1047–1073`); Lemma 5.2.1 (dependent
  path inversion) `:1077`; heterogeneous composition defined from
  composition + transport (`:1139`); the two-dimensional
  concatenation example and its failure under the non-dependent
  operation (`:1143–1183`); type-line concatenation (`:1184–1204`);
  Lemma 5.2.2 (dependent path concatenation) `:1210`; the `α?β` vs
  `α∙β` remark (`:1223`).
- **§5.3 The groupoid laws for dependent paths** (`:1226`): how
  dependent laws are stated (`:1229–1246`); Lemma 5.3.1 (dependent
  involution) `:1248`; the general pattern, remaining laws omitted
  in the source (`:1256`).

**§6 Notable properties of paths** (`:1259`):
- **§6.1 Path induction** (`:1265`): Theorem 6.1.1 (path induction,
  `pathrec`) `:1270`; the η-rule's essential role (`:1318`);
  non-strict computation (`:1320–1324`); Lemma 6.1.2 (path
  computation) `:1328`; the Angiuli-attribution remark (`:1416`);
  the inductive-path-type-as-HIT remark (`:1418`).
- **§6.2 The Eckmann–Hilton argument** (`:1421`): loop spaces
  (`:1424`); Theorem 6.2.1 (Eckmann–Hilton) `:1429`; right and left
  whiskering (`:1441`, `:1471`); the interchange-shaped path by
  path induction (`:1499–1503`); the De Morgan purely-cubical
  comparison [blm21] (`:1510–1517`).

**§7 Directions for future work** (`:1522`): named future topics —
higher groupoid structure of type formers, univalence, higher
inductive types, homotopy n-types, mathematics (`:1525`); partial
formalizations in Cubical Agda and redtt, with URLs (endnote,
`:1527–1528`).

**Bibliography:** resolved in `ictt.bbl` (21 items).

## Content digests

Statement-level digests of the paper's technical content, in the
source's own terms and notation (transcribed per the note above),
each anchored into the vendored `ictt.tex` at the same lines as the
section map. Depth is uniform and full — every definition, lemma,
theorem, primitive specification, and worked derivation, with its
hypotheses; only §1 and §7 (non-technical front/back matter) stay
at map depth. Digests state, never prove; every claim is the
source's, and proof clauses record the source's composition
scenario, not a verification.

### §2 The cubical point of view

- **The homotopical intuition** (`ictt.tex:213`) — the dictionary: a type `A` is a space; a term `a : A` a point; a function `f : A → B` a continuous map; a path `p : path_A(a,b)` a path from `a` to `b` in `A`; a universe `𝒰` a space whose points are spaces; a type family `P : A → 𝒰` a fibration; homotopy-equivalent spaces are equal up to a path (`:215`).
- **The interval type `𝕀`** (`ictt.tex:218`) — an abstraction of the unit interval: a space consisting of only two points `0` and `1`; an interval variable `i : 𝕀` abstracts a point varying continuously in the unit interval; paths are represented as functions out of the interval (`:222–224`), generalizing the point-set-topological description.
- **Line type** (`ictt.tex:232`) — `𝕀 → A` is the line type; its terms are lines (paths with arbitrary endpoints).
- **Path type formation** (`ictt.tex:234`) — for `A : 𝒰` and `a, b : A`, the type `path_A(a,b)` of paths from `a` to `b` in `A`: an internalization of functions from the interval making the endpoints fully explicit. (Endnote `:235`: deliberately called "path type", not "identity type"; HoTT's inductively defined one is referred to as the "inductive path type".)
- **Path application and endpoint equalities** (`ictt.tex:237–239`) — `p : path_A(a,b)` and `i : 𝕀` give `p(i) : A`; definitionally `p(0) ≡ a : A` and `p(1) ≡ b : A`.
- **Path abstraction** (`ictt.tex:241`) — given `a : A` possibly depending on `i : 𝕀`, `λi.a` is a path from `a[0/i]` to `a[1/i]` in `A`; the binder's scope extends to the right unless parenthesized.
- **β-rule** (`ictt.tex:247`) — `(λi.a)(j) ≡ a[j/i]`.
- **η-rule** (`ictt.tex:252`) — `p ≡ λi.(p(i))` when `i` does not occur in `p` ("every path is a path abstraction"); flagged crucial to the derivation of path induction (`:256`).
- **Cubical visualization** (`ictt.tex:260–289`) — a term is a point; `p : 𝕀 → A` a line from `p(0)` to `p(1)` in direction `i`; `h : 𝕀 → 𝕀 → A` a homotopy of paths, a square whose `i`-direction faces are the lines `h(0)` (bottom) and `h(1)` (top) and whose `j`-direction faces are `λj.h(j,0)` (left) and `λj.h(j,1)` (right); at dimension `n+1`, hypercubes with `2(n+1)` faces formed by `n`-cubes; the structure applies to types too, since types are terms of a universe.
- **Lemma 2.3.1, reflexivity path** (`ictt.tex:301`) — for every type `A` and every `a : A`, there is a path `path_A(a,a)`, called the reflexivity path of `a`, denoted `refl_a`; construction: `λi.a` for a fresh `i : 𝕀` on which `a` does not depend.
- **Lemma 2.3.2, function application** (`ictt.tex:314`) — for `f : A → B` and `a, b : A`, an operation `ap_f : path_A(a,b) → path_B(f(a), f(b))` such that `ap_f(refl_a) ≡ refl_{f(a)}`; construction `ap_f(p) :≡ λi.f(p(i))`. Credited [bch14, cchm].
- **Strict functoriality of ap** (`ictt.tex:336–345`) — definitional equalities `ap_{id_A}(p) ≡ p`, `ap_{f∘g}(p) ≡ ap_f(ap_g(p))`, `ap_{λ_.a}(p) ≡ refl_a` [bch14, cchm]; in HoTT these hold only up to homotopy.
- **Theorem 2.3.3, function extensionality** (`ictt.tex:351`) — for `f, g : Π(x:A) B(x)`, an operation `funext_{f,g} : (Π(x:A) path_{B(x)}(f(x), g(x))) → path_{Π(x:A)B(x)}(f, g)`; construction: from `H`, the term `λi.λx.(H(x)(i))`, whose endpoints are `f` and `g` by η-conversion. Credited [cchm]; obtained without axioms, unlike HoTT.

### §3 There are enough paths

- **Why Kan operations** (`ictt.tex:370–384`) — paths-as-interval-functions alone does not support transporting, inverting, or concatenating; in the cubical setting path induction is not accepted as the fundamental reasoning principle; instead cubically-inspired primitive Kan operations — transport and composition — are imposed on every type [cartesian, afh], and every type comes with its own computation of them on its constructors or eliminators [cartesian].
- **Transport (primitive)** (`ictt.tex:395`) — given a path between types `A : 𝕀 → 𝒰` and a term `a : A(i)`, there is `a^{i⇝j}_A : A(j)`, the transport of `a` from `i` to `j` along `A`; static transport is strict: `a^{i⇝i}_A ≡ a`.
- **Transport along a degenerate line is not strict** (`ictt.tex:398–402`) — in general `a^{i⇝j}_{refl_A} ≢ a`, in contrast with HoTT, where transport along reflexivity is the identity function.
- **Lemma 3.1.1, transport along a path** (`ictt.tex:406`) — for a type family `C : A → 𝒰`, terms `a, b : A`, and `p : path_A(a,b)`, a function `p_* : C(a) → C(b)`; construction: the type line `D(p) :≡ λi.C(p(i)) : 𝕀 → 𝒰` from `C(a)` to `C(b)`, and `p_*(c) :≡ c^{0⇝1}_{D(p)}`.
- **Lemma 3.1.2, transport along refl is the identity up to a path** (`ictt.tex:425`) — for `C : A → 𝒰` and `a : A`, a path `path_{C(a)→C(a)}((refl_a)_*, id_{C(a)})`; construction: by funext reduce to `c : C(a)`; `(refl_a)_*(c) ≡ c^{0⇝1}_{λ_.C(a)}`, and `λi.c^{i⇝1}_{λ_.C(a)}` is the required path, its `1`-endpoint strict by static transport.
- **Composition (primitive)** (`ictt.tex:442–461`) — every open cube in a type can be filled: at dimension one, adjacent lines `p, q, r : 𝕀 → A` with `q(0) ≡ p(0)` and `p(1) ≡ r(0)` — cap `p`, left tube `q`, right tube `r` — have a composite line from `q(1)` to `r(1)`; composition asserts the whole filler square: at `j=1` the filler is the composite, at `j=0` the cap `p`, at `i=0`/`i=1` the tubes `q`/`r`. Any open shape satisfying the adjacency conditions is a *composition scenario* (`:461`).
- **Lemma 3.2.1, path inversion** (`ictt.tex:469`) — for every `A` and `a, b : A`, a function `path_A(a,b) → path_A(b,a)`, `p ↦ p⁻¹`; scenario: left tube `p(j)`, cap `refl_a(i)`, right tube `refl_a(j)` (both degenerate); the composite is an `i`-line from `b` to `a`. (Cartesian setting: no primitive reversal, unlike De Morgan systems, `:465`.)
- **Definition 3.2.2, fillers** (`ictt.tex:498`) — given a composition scenario, `i, j : 𝕀`, and a composite `p` for an open cube in the `i` direction, `fill_j(p)` is its filler in the `j` direction; written `fill(p)` when unambiguous — e.g. `fill(p⁻¹(i))` is the square from Lemma 3.2.1's proof (`:502`).
- **Lemma 3.2.3, path concatenation** (`ictt.tex:508`) — for every `A` and `a, b, c : A`, a function `path_A(a,b) → path_A(b,c) → path_A(a,c)`, `p ↦ q ↦ p∙q`, the concatenation; scenario: cap `p(i)`, left tube degenerate `a`, right tube `q(j)`; the composite is an `i`-line from `a` to `c`.
- **Cartesian diagonals** (`ictt.tex:536–538`) — in a cartesian setting composition also admits the specification of diagonals, the filler's diagonal being definitionally the designated one [cartesian, afh]; not used in the paper.
- **The interval is not Kan** (`ictt.tex:540–548`) — the interval supports no Kan operations: `λi.i : path_𝕀(0,1)` would have an inverse if `𝕀` were Kan, impossible in the cartesian setting; `𝕀` is a pretype; convention: the interval occurs only as the antecedent of a function type.

### §4 Two-dimensional constructions

- **Two-extent composition** (`ictt.tex:580–582`) — to fill an open `(i,j,k)`-cube in the `j` direction: determine its `(i,k)`-face (bottom), two `(k,j)`-faces (left and right), and two `(i,j)`-faces (back and front), all adjacent up to definitional equality; the composite is an `(i,k)`-square. An `n`-extent composition requires an `(n+1)`-cube. Diagram convention (`:584–598`): a cube drawn from above — center square = top (composite), outer square = bottom (filler base), top/bottom trapezoids = back/front faces, left/right trapezoids = left/right faces.
- **Lemma 4.1.1, weak meet** (`ictt.tex:564`) — for every `A` and `a, b : A`, an operation `-(-∧-) : path_A(a,b) → 𝕀 → 𝕀 → A` such that for `p : path_A(a,b)` and `i, j : 𝕀` the square `p(i∧j)` has faces: bottom (`j=0`) and left (`i=0`) degenerate at `a`, top (`j=1`) `p(i)`, right (`i=1`) `p(j)`. Proof (`:602–641`): first a one-step composition yields the *halfway meet* `p(i ∧* j)` — bottom/left degenerate `a`, right `p(j)`, top a composition-produced path `p*(i)` not definitionally `p(i)`; then a two-extent composition on an otherwise degenerate open cube with `p(-∧*-)` as back and right faces corrects `p*` to `p`.
- **Weakness; diagonal improvement** (`ictt.tex:560–562`, `:643`) — connections are built-in in De Morgan systems [cchm, chm]; derived here in the cartesian setting, where some computation rules hold only up to a path (hence "weak"). The derived connections could be improved by attaching squares to the diagonal face of their open cubes, making the connection's diagonal definitionally equal to `p`.
- **Lemma 4.1.2, weak join** (`ictt.tex:645`) — for `A` and `a, b : A`, an operation `-(-∨-) : path_A(a,b) → 𝕀 → 𝕀 → A` such that the square `p(i∨j)` has faces: bottom (`j=0`) `p(i)`, left (`i=0`) `p(j)`, top (`j=1`) and right (`i=1`) degenerate at `b`. Proof (`:660–685`): a two-extent composition with halfway meets as front and left faces (`p(i∧*j)`, `p(k∧*j)`), `p*(j)` as back and right, degenerate bottom.
- **Globular representation** (`ictt.tex:693–703`) — cubically, path equality is always relative: a square identifies two lines modulo an identification of two others; a *globular* identification of `p, q : path_A(a,b)` is a square with `p(i)` bottom, `q(i)` top, and degenerate left/right faces. The groupoid laws are stated in this representation.
- **Lemma 4.2.1, right unit** (`ictt.tex:707`) — for every `A` and `a, b : A`: `ru_p : path_{path_A(a,b)}(p, p∙refl_b)` for any `p : path_A(a,b)`; immediate from the filler of concatenation (Lemma 3.2.3) with `q :≡ refl_b`.
- **Lemma 4.2.2, left unit** (`ictt.tex:719`) — `lu_p : path_{path_A(a,b)}(p, refl_a∙p)` for any `p : path_A(a,b)`. Proof (`:727–775`): first a helper square `γ` — faces: bottom `p⁻¹(i)`, top degenerate `b`, left degenerate `b`, right `p(k)` — by two-extent composition from the filler of `p`'s inversion (front), the meet (right), and degenerate squares/points elsewhere; then a second two-extent composition with `γ` at the right, the filler of `refl_a ∙ p` at the back, and the filler of `p`'s inversion at the bottom.
- **Right-vs-left asymmetry** (`ictt.tex:778–792`) — the concatenation filler is a simultaneous identification readable as "a path from `p` to `p∙q` just in case `q` is refl", so the right unit is immediate; this parallels HoTT's transitivity by path induction on the second argument [hottbook lem. 2.1.2], and inversion's filler ("a path from `p⁻¹` to `refl_a` just in case `p` is `refl_a`") parallels symmetry by induction on `p` [lem. 2.1.1].
- **Lemma 4.2.3, right inverse** (`ictt.tex:796`) — `rc_p : path_{path_A(a,a)}(refl_a, p∙p⁻¹)` for any `p : path_A(a,b)`; two-extent composition on an open `(i,j,k)`-cube whose back and front faces are the fillers of inversion and concatenation, other faces degenerate (`:804–828`).
- **Lemma 4.2.4, left inverse** (`ictt.tex:833`) — `lc_p : path_{path_A(b,b)}(refl_b, p⁻¹∙p)` for any `p : path_A(a,b)`; two-extent composition with the `γ` square (from Lemma 4.2.2's proof) as the back face (`:841–861`).
- **Lemma 4.2.5, involution** (`ictt.tex:870`) — `inv_p : path_{path_A(a,b)}(p, (p⁻¹)⁻¹)` for any `p : path_A(a,b)`; by a two-extent composition using meets, joins, and `γ` (`:878–900`).
- **Lemma 4.2.6, associativity** (`ictt.tex:909`) — `assoc_{p,q,r} : path_{path_A(a,d)}((p∙q)∙r, p∙(q∙r))` for `p : path_A(a,b)`, `q : path_A(b,c)`, `r : path_A(c,d)`. Proof (`:916–978`): two squares with the same three faces have a square identifying their fourth faces; take `α` := the filler of `p∙(q∙r)` and build `β` — bottom `p(i)`, top `((p∙q)∙r)(i)`, left degenerate, right `(q∙r)(j)` — by a two-extent composition from the filler of `(p∙q)∙r` (cap `(p∙q)(i)`, right tube `r(j)`) and `q∙r`'s filler data.
- **Higher structure** (`ictt.tex:981–983`) — the section establishes a 1-groupoid structure up to homotopy; the laws these identifications satisfy in turn are not covered; conjectured derivable by an approach like [lumsdaine2010weak].

### §5 Dependent paths

- **Type lines** (`ictt.tex:991`) — `path_A(a,b)` is well-formed only when `a` and `b` have exactly the type `A`; this excludes paths over `A : 𝕀 → 𝒰` (*type lines*), types that change along the interval.
- **The dependent path type** (`ictt.tex:995–1005`) — for a type line `A : 𝕀 → 𝒰`, `a : A(0)`, `b : A(1)`: the type `pathd_A(a,b)` of dependent paths from `a` to `b`. Over a constant line, `pathd_{λ_.A}(a,b) ≡ path_A(a,b)` — the non-dependent path type is *defined* in terms of the dependent one (`:1001`). Elimination: `p(i) : A(i)`. Constructor: `λi.a : pathd_A(a[0/i], a[1/i])` for `a : A(i)` in context `i : 𝕀`. Boundary: `p(0) ≡ a : A(0)`, `p(1) ≡ b : A(1)`; uniqueness (η): `λi.(p(i)) ≡ p` when `i` does not occur in `p`.
- **The meet's exact type, worked** (`ictt.tex:1009–1034`) — the meet of Lemma 4.1.1, typed three ways: `λj.λi.p(i∧j) : 𝕀 → 𝕀 → A`; `λj.(λi.p(i∧j)) : Π(j:𝕀) path_A(a, p(j))`; and as a dependent path `λj.λi.p(i∧j) : pathd_{λi.path_A(a,p(i))}(refl_a, p)` — endpoints `λi.p(i∧0) ≡ λi.a ≡ refl_a` and `λi.p(i∧1) ≡ λi.p(i) ≡ p` (the last step by η).
- **Extension types** (`ictt.tex:1036`) — in HoTT dependent paths are definable from the inductive path type; cubically they are naturally built-in; multi-dimensional extension types [angiuli2019computational, p. 67] are an alternative generalization avoiding iterated path types.
- **Type-line inversion** (`ictt.tex:1047–1073`) — a type line `A : 𝕀 → 𝒰` is a non-dependent path `A : path_𝒰(A(0), A(1))`, since universes never depend on interval variables; Lemma 3.2.1 then gives `A⁻¹ : path_𝒰(A(1), A(0))`, with the typing inferences `a : A⁻¹(1)` iff `a : A(0)` and `a : A⁻¹(0)` iff `a : A(1)` (`:1071`); hence `pathd_{A⁻¹}(b,a)` is well-formed whenever `pathd_A(a,b)` is (`:1073`).
- **Lemma 5.2.1, dependent path inversion** (`ictt.tex:1077`) — for every `A : 𝕀 → 𝒰`, `a : A(0)`, `b : A(1)`: a function `pathd_A(a,b) → pathd_{A⁻¹}(b,a)`, `p ↦ p⁻¹`. Proof (`:1086–1137`): the non-dependent scenario is ill-formed (`p(j) : A(j)` and `a : A(0)` differ in type); instead compose in `A⁻¹`, adjusting each face by transport along `λj.fill_j(A⁻¹(i))` (the filler of `A`'s inversion): cap `a^{0⇝1}_{λj.fill_j(A⁻¹(i))} : A⁻¹(i)`, left tube (`i=0`) `(p(j))^{j⇝1}_{λj.fill_j(A⁻¹(0))}`, right tube (`i=1`) `a^{j⇝1}_{λj.fill_j(A⁻¹(1))}`; adjacency and the endpoints `b`, `a` are checked definitionally via `fill_1(A⁻¹(i)) ≡ A⁻¹(i)` and static transport.
- **Heterogeneous composition** (`ictt.tex:1139`) — a composition in which the types of the cap and composite may differ; obtained from composition + transport: in a type line `A : 𝕀 → 𝒰`, a heterogeneous composition with cap `a : 𝕀 → A(0)` and tubes `a₀, a₁ : Π(i:𝕀) A(i)` abbreviates the composition with cap `λi.(a(i))^{0⇝1}_A : 𝕀 → A(1)` and tubes `λj.(a₀(j))^{j⇝1}_A`, `λj.(a₁(j))^{j⇝1}_A : 𝕀 → A(1)`; the composite is a term of `𝕀 → A(1)`.
- **Two-dimensional concatenation, the failure mode** (`ictt.tex:1143–1183`) — squares `α : pathd_{λj.path_A(s(j),t(j))}(p,q)` and `β : pathd_{λj.path_A(u(j),v(j))}(q,r)` should concatenate vertically to a `j`-dependent path `α?β` from `p` to `r` in `path_A((s∙u)(j), (t∙v)(j))`, built by a two-extent composition whose left and right faces come from the fillers of concatenation and inversion, meets, and joins (`:1157–1177`); the non-dependent operation (Lemma 3.2.3) cannot do this: it requires `α`, `β` to share one type that is a degenerate line, but `path_A(s(j),t(j)) ≢ path_A(u(j),v(j))` in general and both depend on `j` (`:1180–1183`).
- **Type-line concatenation** (`ictt.tex:1184–1204`) — for `A, B : 𝕀 → 𝒰` with `A(1) ≡ B(0)`: `A∙B : path_𝒰(A(0), B(1))` by Lemma 3.2.3, with the typing inferences `a : (A∙B)(0)` iff `a : A(0)` and `b : (A∙B)(1)` iff `b : B(1)` (`:1204`).
- **Lemma 5.2.2, dependent path concatenation** (`ictt.tex:1210`) — suppose `A, B : 𝕀 → 𝒰` with `A(1) ≡ B(0)`; given `a : A(0)`, `b : A(1)`, `c : B(1)`, a function `pathd_A(a,b) → pathd_B(b,c) → pathd_{A∙B}(a,c)`, written `p ↦ q ↦ p∙q`; proof: heterogeneous composition on the open box from Lemma 3.2.3.
- **`α?β` vs `α∙β`** (`ictt.tex:1223`) — dependent concatenation concatenates the example's `α`, `β`, but the result need not be definitionally the two-dimensional operation `α?β`; they are equal up to globular identification, shown by path induction.
- **Stating dependent groupoid laws** (`ictt.tex:1229–1246`) — the involution law for dependent `p : pathd_A(a,b)` needs a non-degenerate type line: `(p⁻¹)⁻¹ : pathd_{(A⁻¹)⁻¹}(a,b)` and in general `(A⁻¹)⁻¹ ≢ A`; the non-dependent involution path `inv_A` (printed at `:1244` as `path_{path_𝒰(A(0),A(1))}((A⁻¹)⁻¹, A)` — see Source notes on its orientation) supplies the connecting line.
- **Lemma 5.3.1, dependent involution** (`ictt.tex:1248`) — for every `A : 𝕀 → 𝒰` with `a : A(0)` and `b : A(1)`: `pathd_{λj.pathd_{λi.inv_A(j)(i)}(a,b)}((p⁻¹)⁻¹, p)` for any `p : pathd_A(a,b)`. Proof stated (`:1256`): heterogeneous composition on the open cube from Lemma 4.2.5's proof; all dependent counterparts of the §4.2 laws follow the same pattern (stated via the non-dependent law's path, proven by heterogeneous filling of the same open cubes) and are omitted in the source.

### §6 Notable properties of paths

- **Theorem 6.1.1, path induction** (`ictt.tex:1270`) — given `A : 𝒰`, `a : A`, and a type family `C : Π(x:A) path_A(a,x) → 𝒰`, a function `pathrec : Π(x:A) Π(p:path_A(a,x)) Π(c:C(a,refl_a)) C(x,p)` (based path induction). Construction (`:1276–1314`): the type line `D :≡ λi.C(p(i∧*1), λj.p(i∧*j)) : 𝕀 → 𝒰` over the halfway meet of `p` satisfies `D(0) ≡ C(a, refl_a)` and `D(1) ≡ C(x, p)` — the latter requiring the η-rule (`λj.p(j) ≡ p`; flagged essential at `:1318`); transport `c` from `0` to `1` along `D`.
- **Non-strict computation** (`ictt.tex:1320–1322`) — for fixed `C`, `a : A`, `c : C(a,refl_a)`: in general `pathrec(a, refl_a, c) ≢ c`, unlike the eliminator of HoTT's inductive path type.
- **Lemma 6.1.2, path computation** (`ictt.tex:1328`) — for every `a : A` and `c : C(a,refl_a)`, a path of type `path_{C(a,refl_a)}(pathrec(a,refl_a,c), c)`. Credited [angiuli2019computational]. Proof (`:1333–1410`): `pathrec(a,refl_a,c) ≡ c^{0⇝1}_{λi.C(refl_a(i∧*1), λj.refl_a(i∧*j))}`; the transport-induced line `λi.c^{i⇝1}` has the right endpoints but lives in the line `C(refl_a(i∧*1), λj.refl_a(i∧*j))`, not `C(a, refl_a)`; the mismatch is fixed by a heterogeneous composition over `D_i :≡ λk.C(α(k)(i), λj.fill_j(α(k)(i)))`, where `α` is an auxiliary square built by composition with `refl_a(k∧*1)` as its right face and degenerate faces elsewhere (`:1360–1382`); the endpoint checks `D_i(0) ≡ C(a, λj.a) ≡ D_i(1)`, `D_0 ≡ λk.C(refl_a(k∧*1), λj.refl_a(k∧*j))`, `D_1 ≡ λk.C(a, λj.a)` close the proof. The argument is inspired by Angiuli [pp. 54–56], whose variant uses contractibility of `Σ(x:A) path_A(a,x)` with center `⟨a, refl_a⟩` (`:1416`).
- **The inductive path type as a HIT** (`ictt.tex:1418`) — with higher inductive types [ch, chm], HoTT's inductive path type is recovered as the HIT freely generated by reflexivity; its eliminator computes strictly on refl; it is equivalent to the path type [ch], hence by univalence equal to it up to a path.
- **Loop spaces** (`ictt.tex:1424`) — for `A` and `a : A`: `Ω(A,a) :≡ path_A(a,a)`; the second loop space `Ω²(A,a) :≡ path_{path_A(a,a)}(refl_a, refl_a)`.
- **Theorem 6.2.1, Eckmann–Hilton** (`ictt.tex:1429`) — for any `α, β : Ω²(A,a)`, a path `path_{Ω²(A,a)}(α∙β, β∙α)`. Proof (adapting HoTT's path-induction proof [hottbook thm. 2.1.6]; `:1435–1508`): for the general globular `α : path_{path_A(a,b)}(p,q)` and `β : path_{path_A(b,c)}(r,s)`, define right whiskering `α∙ᵣr : path_{path_A(a,c)}(p∙r, q∙r)` by a two-extent composition with `α` at the bottom (`:1447–1465`) and left whiskering `p∙ₗβ : path_{path_A(a,c)}(p∙r, p∙s)` by a similar cube with `β` at the right (`:1477–1495`); by path induction on `α`, `β`, `p`, and `r` there is a path from `(α∙ᵣr)∙(q∙ₗβ)` to `(p∙ₗβ)∙(α∙ᵣs)` in `path_{path_A(a,c)}(p∙r, q∙s)` (`:1499–1503`); setting `p ≡ q ≡ r ≡ s ≡ refl_a` and applying the unit laws (Lemmas 4.2.1, 4.2.2) yields the claim.
- **De Morgan comparison** (`ictt.tex:1510–1517`) — [blm21] proves Eckmann–Hilton purely cubically (no path induction) for De Morgan cubes, transporting from `0` to `1` along a `j`-line of paths from `α_r(j)∙β_l(j)` to `β_l(j)∙α_r(j)` in `Ω(A,a)`, where `α_r(j) :≡ ap_{λp.ru_p⁻¹(j)}(α)` and `β_l(j) :≡ ap_{λp.lu_p⁻¹(j)}(β)`; well-formedness there rests on `ru_{refl_x} ≡ lu_{refl_x}`, which holds for built-in connections acting strongly on reflexivity but fails for cartesian weak connections — a direct cartesian cubical proof would need a different strategy.

## What the source establishes

Everything below records what the source states; every mathematical
claim is CONJECTURED until machine-checked.

Positioned by its author as "a first step toward" a cubical
alternative to the HoTT book's informalization program (`:153`,
`:193`): a *naive* (informal but in-principle formalizable)
presentation of **cartesian cubical type theory** [cartesian —
Angiuli, Brunerie, Coquand, Favonia, Harper, Licata].
Its deliverables are elementary results proven almost entirely by
explicit cubical composition scenarios rather than path induction:
the path type as internalized interval functions with strict
endpoint, β, and η laws; strictly functorial `ap` and axiom-free
function extensionality; the Kan primitives (transport with strict
static transport only — transport along a degenerate line is not
strictly trivial — and composition with fillers); the derivation of
**weak connections** (meet and join) in a cartesian setting without
built-in connections or reversals; the **1-groupoid laws** for
paths (units, inverses, involution, associativity) as globular
squares built by two-extent composition; **dependent paths** with
type-line inversion/concatenation and **heterogeneous composition**
(composition + transport combined), extending the groupoid laws to
dependent paths; a derivation of **based path induction** whose
computation rule holds up to a path (following Angiuli); and the
**Eckmann–Hilton duality** for the second loop space, proven via
path induction, with an explicit obstruction analysis of why the
purely-cubical De Morgan proof [blm21] does not transfer to
cartesian weak connections (`ru_refl ≡ lu_refl` fails). Univalence
appears as motivating background (`ictt.tex:393`), in the §6.1 HIT
remark's appeal (`:1418`), and, with higher inductive types, as
named future work (`:1525`) — the paper does not develop cubical
univalence. Partial formalizations in
Cubical Agda and redtt are cited as available online (endnote,
`:1527–1528`).
