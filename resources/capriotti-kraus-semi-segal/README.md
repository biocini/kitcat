---
artifact: capriotti-kraus-semi-segal.tar.gz
sha256: 6f738dbaceceae22ae42de85259b4d0d0111468b57d80a7d6e9457fbf4e07908
format: latex-source
fetch-url: https://arxiv.org/e-print/1707.03693v4
metadata-url: https://arxiv.org/abs/1707.03693
doi: 10.48550/arXiv.1707.03693
version: v4
fetched: 2026-07-24
sha256-inner: 1ea0b516a851fc61d7a199fd5d4a3f07b61ed960945f2a18622f73677b186ef5
---

# Capriotti & Kraus — Univalent Higher Categories via Complete Semi-Segal Types

Category theory in homotopy type theory by the simplicial strategy:
semi-simplicial types carrying Segal conditions, with identities
recovered rather than assumed. The paper develops wild semicategorical
structures (transitive graph, wild semicategory, wild 2-semicategory)
and their identity structures, proves that identity structure and
degeneracy structure correspond, settles when the type of identity
structures is a proposition, and defines univalent *n*-categories as
complete semi-Segal *n*-types, proving the definition agrees with
univalent (Rezk-complete) *n*-categories for *n* ∈ {0,1,2}. This is
the full version, with all proofs; an abridged version appeared at
POPL 2018. Formalised in Agda by the authors.

Load declaration: unit-tier reference, held at statement depth over
the identity/degeneracy and completeness material (§4–§5) — the
source for how a unit structure can and cannot be made propositional
in an untruncated setting. §2–§3 (semi-simplicial preliminaries, horn
fillers) are mapped at outline depth.

## Citation

Paolo Capriotti and Nicolai Kraus. *Univalent Higher Categories via
Complete Semi-Segal Types*. arXiv:1707.03693 [math.CT], v4, 29 October
2017 (v1: 12 July 2017). <https://arxiv.org/abs/1707.03693>. MSC
18A15. The paper's own front matter (`clean-arxiv.tex:22`) records it
as the full version of a paper presented at the 45th ACM SIGPLAN
Symposium on Principles of Programming Languages (POPL 2018).

## Vetting

PROVISIONAL. Ingested 2026-07-24 by Claude (Fable 5) at Lane's
direction, from a Lane-supplied tarball verified byte-identical to the
live arXiv e-print (sha256 match against a fresh fetch of `fetch-url`,
same session). §4.4 and §5 were read in the vendored `clean-arxiv.tex`
during ingestion; no independent statement audit has been run.

## Files

- `capriotti-kraus-semi-segal.tar.gz` — the arXiv e-print (v4), the
  canonical artifact. Contains `clean-arxiv.tex`, `clean-arxiv.bbl`,
  and two figure sources (`figure_balanced_cube.tex`,
  `figure_uni_compl.tex`).
- `clean-arxiv.tex` — extracted markup, the file the reader greps; all
  line anchors below index into it.
- `clean-arxiv.bbl` — extracted bibliography.

## Source provenance

Supplied by Lane at the repository root on 2026-07-24 for the
deductive-system unit-tier design question. During ingestion the same
session, a fresh fetch of `https://arxiv.org/e-print/1707.03693v4`
produced a byte-identical file (sha256 `6f738dba…`), authenticating
the vendored copy as the arXiv-served v4 e-print; the abs page listed
four versions, v4 (29 Oct 2017) being current at that time.

## Section map

Jump note: `sed -n 'A,Bp' clean-arxiv.tex`.

- l.307–388 — Introduction, including the statement (l.359, l.363)
  that identity structure corresponds to degeneracy structure and
  that having it is *not* a proposition in general.
- l.389–543 — §2 Type theory, univalent categories, semisimplicial
  types: HoTT conventions (l.397), univalent categories after
  Ahrens–Kapulkin–Shulman (l.405, definition l.430), semi-simplicial
  types (l.434).
- l.544–1025 — §3 Composition structure and horn fillers: wild
  semicategorical structure (l.549, definition l.554), semi-Segal
  types (l.601), horns/spines/tetrahedra (l.693), equivalence of the
  two presentations (l.805).
- l.1026–1634 — §4 Identity and degeneracy structure: identities for
  wild structures (l.1031, definition l.1033), degeneracies (l.1201),
  the correspondence (l.1270, theorem l.1282), **uniqueness of the
  identity structure** (l.1345, theorem l.1373), univalence (l.1496,
  isomorphism l.1511, theorem l.1607).
- l.1635–1849 — §5 Completeness: **neutral edges** (definition
  l.1640), the Yoneda-style characterisation (lemma l.1674), neutral
  ⟺ iso and its propositionality (lemma l.1681), higher outer horns
  (l.1693), **completeness** (definition l.1703), completeness ⟺
  univalence (lemma l.1714), degeneracies from completeness (lemmas
  l.1740, l.1751, l.1801).
- l.1850–end — §6 Conclusions, with the final definition of a complete
  semi-Segal *n*-type (l.1855).

## Content digests

- **Wild structures** (l.554): a transitive graph is objects, a Hom
  family, and composition; a wild semicategory adds an associator α; a
  wild 2-semicategory adds a pentagon. "Wild" marks that higher levels
  are uncontrolled — the structures are not preserved by slicing
  (l.1345–1352).
- **Identity structure** (l.1033): a reflexive-transitive graph adds
  `Ids : Π x, Hom(x,x)`; a *wild precategory* adds the unit laws
  `λ : Ids_y ∘ f = f` and `ρ : f ∘ Ids_x = f`; a wild 2-precategory
  adds the three unit triangles `t₁` (l.1040), `t₀`, `t₂` (l.1066),
  relating λ and ρ through the associator. Remark (l.1101): these are
  *structure*, not laws, so the type with the derivable triangles need
  not be equivalent to the type without them.
- **Identities ⟺ degeneracies** (theorem l.1282): equipping wild
  semicategories with identity structure amounts exactly to equipping
  semi-Segal types with degeneracies.
- **Uniqueness of identity structure** (l.1367–1368 and theorem
  l.1373): "Even if it is possible to find an identity structure,
  there is in general not a *unique* way of doing it. In other words,
  the type of identity structures is not a proposition." It *is* a
  proposition once morphisms are truncated at the appropriate level:
  for a transitive graph extending to a preordered set, Hom
  propositional; for a wild semicategory extending to a precategory,
  Hom a family of sets — the argument being the classical
  `Ids = Ids' ∘ Ids = Ids'` plus the observation that λ, ρ then
  inhabit propositions; for a wild 2-semicategory extending to a
  2-precategory, Hom a family of 1-types (l.1400–1456).
- **Neutral edges** (definition l.1640): an edge `e : A₁(a,b)` is
  right-neutral when every outer horn `Λ²₀` with `u₀₁ ≡ e` has
  *contractible* filling, left-neutral for the dual outer horn, and
  neutral when both; `isneut(e)` is a proposition by construction.
  Yoneda form (lemma l.1674): `f` is right-neutral iff composing with
  `f` gives an equivalence `Hom(y,z) → Hom(x,z)` for every `z`, and
  left-neutral iff `Hom(w,x) → Hom(w,y)` is an equivalence — the fibre
  of the composition map over `h` being exactly the type of horn
  fillers. In a wild precategory (lemma l.1681) `isneut(f)` and
  `isIso(f)` are equivalent, and `isIso(f)` is therefore a
  proposition.
- **Completeness** (definition l.1703): an *n*-restricted semi-Segal
  type is complete when `Π (x : A₀), isContr (Σ (y : A₀), (e :
  A₁(y,x)), isneut(e))` — there is a unique neutral morphism with
  codomain `x`. Lemma l.1714: for a 3- or 4-restricted semi-Segal type
  with degeneracies, completeness holds iff the structure is univalent
  as a wild precategory. Lemmas l.1740–1849: a degeneracy structure
  can always be *constructed* for a complete semi-Segal type.

## What the source establishes

A simplicial route to higher categories in HoTT: the equivalence
between wild semicategorical structure and semi-Segal types, the
correspondence between identity and degeneracy structure, an exact
account of when unit structure is property rather than structure (only
under truncation), and complete semi-Segal *n*-types as a definition
of univalent *n*-category agreeing with the established one for
*n* ≤ 2. Authors report an Agda formalisation. Presented at POPL 2018.
Every mathematical claim recorded here is CONJECTURED until
machine-checked in this repository.
