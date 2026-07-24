---
artifact: sterling-reflexive-graph-lenses.tar.gz
sha256: aa1de068a801153887635dbc87e2fa893c81fc30ee8b4c743cb435b4d30f23ed
format: latex-source
fetch-url: https://arxiv.org/e-print/2404.07854
metadata-url: https://arxiv.org/abs/2404.07854
doi: 10.1017/S0960129526100565
version: v2
fetched: 2026-07-22
sha256-inner: 597f174069e19049f370142b17cd1b243884b1f3c0b76eefba9d4d7cad6cd18a
---

# Sterling — Reflexive graph lenses in univalent foundations

A theory of *reflexive graph lenses*: intermediate abstractions
between families of reflexive graphs and displayed reflexive graphs,
organized to simplify the characterisation of identity types of
complex structures in univalent foundations. The paper develops
reflexive graphs and displayed reflexive graphs, the univalence
condition on a reflexive graph (fans propositional — such graphs are
called *path objects*), oplax covariant / lax contravariant / unbiased
dependent lenses with their display and flattening constructions, a
definitional-lens refinement, propositionality of the univalence and
lens-structure predicates, classifying path objects for graphs and
lenses (structure-identity-principle case studies), and an equivalence
between reflexive graph fibrations and univalent lenses via two
round-trip theorems. Works in intensional MLTT with no global
universes, function extensionality, or univalence — each assumed
locally where needed.

Load declaration: design-reference tier for notation and record
stratification. The map is line-anchored across the whole paper;
digests run at statement level over the graph/path-object layer and
the lens layer (§§3–5, §8), one-line elsewhere.

## Citation

Jonathan Sterling. *Reflexive graph lenses in univalent foundations*.
arXiv:2404.07854 [cs.LO], v2, 19 January 2026 (v1: 11 April 2024).
<https://arxiv.org/abs/2404.07854>. Journal reference (per the abs
page, opened 2026-07-22): *Mathematical Structures in Computer
Science*, 36 (2026) e21, DOI 10.1017/S0960129526100565 (Cambridge
University Press). Subjects: cs.LO; math.CT; math.LO.

## Vetting

PROVISIONAL. Ingested 2026-07-22 by Claude (Fable 5) at Lane's
direction, from a Lane-supplied tarball verified byte-identical to
the live arXiv e-print (sha256 match against a fresh fetch of
`fetch-url`, same session). The sections digested below were read in
the vendored `paper.tex` during ingestion; no independent statement
audit has been run.

## Files

- `sterling-reflexive-graph-lenses.tar.gz` — the arXiv e-print
  (v2), the canonical artifact. Contains `paper.tex`, `paper.bbl`,
  `00README.json` (toplevel `paper.tex`, TeX Live 2025, pdflatex),
  and seven local style files (`jms-operators.sty`,
  `jmsdelim.sty`, `jms-sections.sty`, `local-abbrv.sty`,
  `local-jmsdelim.sty`, `local-tikz.sty`, `iblock.sty`).
- `paper.tex` — extracted markup, the file the reader greps; all
  line anchors below index into it. The paper's notation macros
  are defined in its own preamble (l.90–250).
- `paper.bbl` — extracted bibliography.

## Source provenance

The tarball was supplied by Lane at the repository root on
2026-07-22 for the Cat.Logic notation-design inquiry. During
ingestion the same session, a fresh fetch of
`https://arxiv.org/e-print/2404.07854` produced a byte-identical
file (sha256 `aa1de068…`), so the vendored copy is authenticated as
the current arXiv-served e-print; the abs page listed v2 (19 Jan
2026, "Revised with many clarifications and typo fixes") as current
at that time. Internal file dates (19–20 Jan 2026) and the
`00README.json` TeX Live 2025 pin are consistent with the v2
submission date.

## Section map

Jump note: `sed -n 'A,Bp' paper.tex`.

- l.252–851 — Introduction: identity types and identification
  induction (l.254), characterising identity types with (displayed)
  reflexive graphs (l.351), transport via lenses (l.571),
  identification induction via dependent lenses (l.644), related
  work incl. the SIP (l.818) and delta lenses (l.825).
- l.853–905 — Reflexive graphs and path objects: reflexive graph
  (l.857), homomorphism (l.863), displayed reflexive graph (l.872),
  component (l.886), diagonal family notation (l.899).
- l.907–1105 — Basic constructions: discrete △A (l.910), codiscrete
  ▽A (l.916), total graph 𝒜.ℬ (l.932), binary/indexed products
  (l.950, l.956), coproduct (l.976), tensor/cotensor (l.995),
  constant displayed graph (l.1014), subgraph comprehension
  (l.1038), restriction of iterated displayed graphs (l.1062).
- l.1107–1157 — Duality involution: opposite graph (l.1109),
  involution (l.1127), total opposite of a displayed graph (l.1131),
  displayed duality (l.1153).
- l.1159–1422 — Path objects and univalence: fans/co-fans (l.1160),
  fan⟺co-fan propositionality (l.1164), idToEdge ⌊−⌋ (l.1217),
  edgeToId ⟦−⟧ via propositional fans (l.1247), equivalence
  criterion (l.1389), univalent reflexive graph = path object
  (l.1399), univalent displayed graph (l.1418).
- l.1424–1490 — Path algebra in a path object: toolkit (l.1429),
  pre-concatenation equivalence (l.1479).
- l.1492–1546 — Univalent families and reflexive graph images
  (l.1493, l.1507, l.1522, l.1542).
- l.1548–1996 — Closure properties of path objects: opposite
  (l.1549), total (l.1557), constant displayed (l.1638), product =
  function extensionality (l.1655), coproduct (l.1659), codiscrete
  (l.1794), path subobject comprehension (l.1822).
- l.1998–2512 — Lenses: oplax covariant lens (l.2008), lax
  contravariant lens (l.2023), displays disp⁺/disp⁻ (l.2041,
  l.2064) with component computations (l.2087, l.2110) and
  univalence preservation (l.2134, l.2142); unbiased dependent lens
  (l.2157), its display (l.2178) and the one-unitor remark
  (l.2203), univalence of the display (l.2209), biased→unbiased
  upgrades (l.2215); duality involution for lenses: total opposite
  (l.2344), involution observation (l.2378), display of total
  opposites (l.2382).
- l.2514–2820 — Definitional lenses (l.2517), examples (univalent
  families l.2589, finite ordinals l.2637), definitional
  replacement (l.2706) with flattening 𝒜↓ℬ (l.2710) and its
  univalence (l.2751).
- l.2822–3052 — Polynomials and partial products (cleavings l.2833,
  l.2851; partial products of definitional lenses l.2868).
- l.3054–3427 — Coherence: univalence is a proposition (l.3055),
  displayed univalence is a proposition (l.3069), covariant lens
  structure on path objects is a proposition (l.3083),
  contravariant mate (l.3197), unbiased mate (l.3206).
- l.3429–4024 — Case study: path objects classifying reflexive
  graphs (l.3433), displayed graphs over a fixed base — SIP
  (l.3580), variable base (l.3767), families and lenses of graphs
  (l.3893) incl. the lens-of-lenses LensStr⁺ (l.3949) and its
  classifying path object (l.4006).
- l.4026–end — Fibred reflexive graphs (duality l.4044, univalence
  l.4054); fibrations from lenses (l.4143): universal
  pushforwards/pullbacks (l.4147), roundtrip for fibrations
  (l.4621), roundtrip for lenses (l.4894).

## Content digests

Notation, fixed in the preamble (l.90–250) and used throughout:
vertices `vrt 𝒜`, edges `x ≈_𝒜 y`, reflexivity `rx_𝒜 x`; displayed
edges `u ≈_ℬ[p] v` with `rx` superscripted; fan `{x}⁺_𝒜`, co-fan
`{x}⁻_𝒜`; covariance marks `+` (covariant), `−` (contravariant),
`±` (unbiased) on displays `disp⁺/disp⁻/disp^±`, flattenings
`𝒜↓ℬ^±`, upgrades `[ℬ]₊^±`; `⌊p⌋_𝒜` (idToEdge), `⟦e⟧_𝒜` (edgeToId);
path composition `∙` with left/right variants `∙ₗ/∙ᵣ` (defined
l.146–148, unused in the body); `𝒜^op` and total opposite `𝒜^õp`.

- **Reflexive graph** (l.857): a type of vertices, a two-sided
  family of edge types, and a reflexivity datum `rx_𝒜 x : x ≈ x`.
  **Displayed reflexive graph** over 𝒜 (l.872): vertex families
  over vertices, edge families over edges between lifted vertices,
  reflexivity over reflexivity. Its **component** at x (l.886) is
  the reflexive graph of lifts of x with edges over `rx x`.
- **Fans** (l.1160): `{x}⁺ = Σ y, x ≈ y`, co-fan `{x}⁻ = Σ y,
  y ≈ x`. Lemma (l.1164): all fans propositional ⟺ all co-fans
  propositional.
- **idToEdge/edgeToId** (l.1217, l.1247): `⌊−⌋ : x = y → x ≈ y` by
  identification induction from `rx`; when fans are propositional,
  a quasi-inverse `⟦−⟧` exists (built through a generalisation
  anticipating fan contractibility), so ⌊−⌋ is an equivalence; the
  converse also holds (l.1389).
- **Univalent reflexive graph = path object** (l.1399): five
  equivalent conditions — fans propositional, co-fans
  propositional, fans (resp. co-fans) contractible with centre
  `(x, rx x)`, idToEdge an equivalence. Displayed version (l.1418)
  is componentwise, base not required univalent.
- **Path algebra toolkit** (l.1429): in a path object, edges
  concatenate (`∙`) and invert, with runit/lunit/rsym/lsym/assoc;
  pre-concatenation is an equivalence (l.1479). The section's
  stated thesis: careful choice of path-object structure avoids
  path algebra.
- **Lenses** (l.2008, l.2023): over 𝒜, an oplax covariant lens is
  a family of graphs ℬ(x) with `push_ℬ(p) : vrt ℬ(x) → vrt ℬ(y)`
  for `p : x ≈ y` and a *lax unitor edge* `pushRx : push(rx x)u ≈ u`
  in ℬ(x); the lax contravariant lens dually carries `pull` and
  `pullRx : u ≈ pull(rx x)u`. Displays (l.2041, l.2064): edges over
  p are `push(p)u ≈ v` (resp. `u ≈ pull(p)v`), reflexivity the
  unitor. Componentwise univalence transfers to the display
  (l.2134, l.2142).
- **Unbiased dependent lens** (l.2157): family ℬ(p) indexed by
  *edges*, with `lext_ℬ(p)u : ℬ(p)` from u over the source,
  `rext_ℬ(p)u : ℬ(p)` from u over the target, a mid unitor
  `extRx : lext(rx)u ≈ rext(rx)u`, and a lax unitor
  `rextRx : u ≈ rext(rx)u`. Display (l.2178): edges over p are
  `lext(p)u ≈ rext(p)v` in ℬ(p). Remark (l.2203): only `extRx` is
  needed for the display; exactly one of the lax/oplax unitors may
  be included — including both breaks propositionality of
  fiberwise-univalent unbiased lens structure (compared to
  half-adjoint equivalences omitting one snake identity). Both
  biased kinds upgrade to unbiased with definitionally equal
  displays (l.2215).
- **Duality for lenses** (l.2344–2412): the total opposite swaps
  push↔pull and pushRx↔pullRx over 𝒜^op; an oplax covariant lens
  over 𝒜 *is* a lax contravariant lens over 𝒜^op (l.2378), and
  displays commute with the involution definitionally (l.2382).
- **Coherence** (l.3055–3210): assuming dependent function
  extensionality — univalence of a (displayed) reflexive graph is
  a proposition; over a path object with path-object fibers, the
  types of oplax covariant, lax contravariant, and unbiased
  dependent lens structures are propositions.
- **Fibrations from lenses** (l.4143–end): universal
  pushforwards/pullbacks (l.4147) are fan-propositionality of
  pushed/pulled fans; roundtrip theorems — a covariant fibration is
  recovered from the display of its underlying lens (l.4621), and
  a lens of path objects is recovered from the diagonal of its
  display (l.4894) — establishing the fibration ⟺ univalent-lens
  equivalence.

Sections not digested above (basic constructions l.907–1105,
closure properties l.1548–1996, definitional lenses l.2514–2820,
polynomials l.2822–3052, classifying case studies l.3429–4024) are
mapped one-line in the section map; their statements were not
read at digest depth during ingestion.

## What the source establishes

A complete elementary theory of reflexive graph lenses in
intensional MLTT with locally-assumed extensionality principles:
the lens notions with their displays and flattenings; the
propositionality (coherence) of the univalence and lens-structure
predicates; classifying path objects implementing the structure
identity principle for graphs, displayed graphs, families, and
lenses; and the equivalence between reflexive graph fibrations and
univalent lenses. Published in Math. Struct. Comp. Sci. 36 (2026)
e21. Every mathematical claim recorded here is CONJECTURED until
machine-checked in this repository.
