---
artifact: mellies-ribbon-tensorial-logic.pdf
sha256: b7a423d5e5412ab621ff44fdee27f0046dfbcd6a6bf7a6559b20181b8c285f87
format: pdf
fetch-url: none
doi: 10.1145/3209108.3209129
fetched: 2026-06-18
---

# Melliès — Ribbon Tensorial Logic

## Citation

Paul-André Melliès. *Ribbon Tensorial Logic*. In LICS '18: 33rd
Annual ACM/IEEE Symposium on Logic in Computer Science, July 9–12,
2018, Oxford, United Kingdom. ACM, New York, NY, USA, 10 pages.
DOI 10.1145/3209108.3209129.

## Vetting

PROVISIONAL — directed agent ingestion, 2026-07-21, at Lane's
direction (user-supplied file placed in the repository root for
vendoring). The statement audit has not been run; the entry
supports no load-bearing citation until it is.

## Files

- `mellies-ribbon-tensorial-logic.pdf` — canonical artifact (the
  format is `pdf`; no source markup is available).
- `mellies-ribbon-tensorial-logic.pdftext` — greppable extraction,
  1995 lines, native text layer (no OCR). Provenance:
  `pdftotext mellies-ribbon-tensorial-logic.pdf
  mellies-ribbon-tensorial-logic.pdftext`, pdftotext 26.06.0
  (poppler-utils 26.06.0), run inside the repository's
  `nix develop` shell. The paper is two-column; the extraction
  linearizes column by column per page, so running section numbers
  occasionally interleave out of order. Definition and theorem
  statements extract intact at the anchors below; sequent-calculus
  figures and string/tangle diagrams do not survive extraction —
  audits of those read the PDF pages directly. No correction patch:
  the load-bearing statements are legible as extracted.

## Source provenance

The vendored file was supplied by Lane, present on the machine as
`2018-Melliès-ribbon-tensorial-logic.pdf` with a file date of
2026-06-18 (recorded as `fetched:`; the ultimate origin — ACM
Digital Library or elsewhere — is not known). The author's IRIF
tensorial-logic page hosts a copy at
<https://www.irif.fr/~mellies/tensorial-logic/7-ribbon-tensorial-logic.pdf>,
but at ingestion time (2026-07-21) that copy hashed differently
from the vendored artifact — a different compile of the same paper
— so no public URL is recorded as retrieving this exact document
and `fetch-url` is `none`. A re-fetcher can obtain *a* copy from
the IRIF URL or via the DOI (ACM, paywalled), then authenticate
against the recorded hash or re-ingest.

## Section map

Line anchors into `mellies-ribbon-tensorial-logic.pdftext`; jump
with `sed -n 'A,Bp' mellies-ribbon-tensorial-logic.pdftext`.

- l.1–18 — title, abstract, CCS concepts, keywords, ACM reference
  (DOI l.14–17).
- §1 Introduction (l.21):
  - l.22–200 — proofs and counter-proofs as interactive protocols;
    particles vs moves; the axiom and cut combinators as sequents;
    the proof-net identification problem for MLL.
  - l.201 — **Definition 1 (proof structure)**: MLL proof
    structures over atoms X, as morphisms in a freely generated
    compact-closed category.
  - l.565–599 — balanced dialogue categories announced; l.571 —
    **Definition 2 (dialogue categories)**: monoidal C, object ⊥,
    functors x ↦ (x ⊸ ⊥) and x ↦ (⊥ ⟜ x), natural isomorphisms
    φ_{x,y} : C(x ⊗ y, ⊥) ≅ C(y, x ⊸ ⊥) and
    ψ_{x,y} : C(x ⊗ y, ⊥) ≅ C(x, ⊥ ⟜ y).
  - l.691 — **Definition 3 (proof nets)**: a tensorial proof net is
    a morphism of the free balanced dialogue category.
  - l.693 — **Definition 4 (proof structures, tensorial)**: a
    tensorial proof structure A → B is a morphism [A] → [B] of the
    free ribbon category.
  - l.696 — **Theorem (proof-as-tangle, intro form)**: the functor
    [−] from tensorial proof nets to tensorial proof structures is
    faithful; discussion l.700–730 (each strand a pair of
    Opponent/Player moves; topological foundation for game
    semantics).
  - l.755 — **Theorem (symmetric variant)**: the canonical functor
    [−] : symmetric-dialogue(X) → compact-closed(X + 1) is
    faithful; commutative tensorial logic obtained by forgetting
    topology.
- §2 Balanced dialogue categories (l.783):
  - l.790–938 — monoidal recap (MacLane pentagon and triangle,
    l.793–830); l.798 — **Definition 5 (braiding)**: σ_{A,B} with
    the two hexagons.
  - l.939 — **Definition 6 (balanced category)**: a braided
    monoidal category with a natural twist θ_A : A → A satisfying
    **θ_I = id_I** and the compatibility square
    θ_{A⊗B} = σ ∘ (θ_B ⊗ θ_A) ∘ σ (Joyal–Street).
  - l.1023 — **Definition 7 (ribbon category)**: a balanced
    category where every object has a right dual A ⊣ A∗.
  - l.1031 — **Definition 8 (balanced dialogue categories)**: a
    dialogue category whose underlying monoidal category is
    balanced; l.1034–1036 — **no coherence relation is required
    between the dialogue structure and the balanced structure**.
  - l.1037–1058 — illustration: Mod(H) for a ribbon Hopf algebra H
    as a balanced dialogue category; its rigid full subcategory
    (e.g. Mod_f(H)) is a ribbon category.
- §3 Ribbon tensorial logic (l.1095):
  - l.1096–1442 — the sequent calculus: formulas, two negations,
    sequents with braided contexts, introduction rules, exchange as
    braiding, twist rules (figures partially garbled in
    extraction; read pages directly for the rules).
  - l.1455 — **Theorem 1 (cut-elimination)**: every derivation tree
    is equivalent to a cut-free one modulo commuting conversions.
  - l.1498 — **Theorem 2 (focusing)**: every derivation tree is
    equivalent, modulo commuting conversions, to a focused normal
    form built in construction cycles (cycle discipline
    l.1460–1497).
  - l.1509 — **Theorem 3 (soundness)**: derivation trees of
    A₁ ⊗ ⋯ ⊗ Aₙ ⊢ B interpret as morphisms in any balanced
    dialogue category D under a functor X → D.
- §4 Proof-as-tangle (l.1575):
  - l.1603 — **Theorem 4 (proof-as-tangle)**: [−] is faithful.
    Proof via the focusing theorem: two cut-free derivations with
    the same ribbon tangle modulo topological deformation are
    connected by commuting conversions (l.1606–1823).
- §5 (l.1824) — closing discussion; references l.1955.

## Content digests

- **Definition 2 (dialogue categories), l.571.** Monoidal C with
  pole ⊥ and *both* negations as data — functors x ⊸ ⊥ and ⊥ ⟜ x
  with the two representation isomorphisms φ, ψ of C(x ⊗ y, ⊥). The
  same both-negations pole as the manuscript presentations
  ([mellies-dialogue-deformation](../mellies-dialogue-deformation/)
  Definition 2 there).
- **Definition 6 (balanced category), l.939.** Braided monoidal
  plus natural θ_A : A → A with θ_I = id_I and the θ_{A⊗B}
  compatibility. The unit clause θ_I = id_I is stated as part of
  the definition, not derived.
- **Definition 8 (balanced dialogue categories), l.1031.** The
  juxtaposition is free: dialogue structure and balanced structure
  coexist with *no* imposed coherence between them. This
  independence is flagged by the author as an interesting aspect of
  the definition.
- **Theorems 1–3 (cut-elimination, focusing, soundness),
  l.1455/1498/1509.** The sequent calculus of ribbon tensorial
  logic normalizes: cut-free forms exist modulo commuting
  conversions; focusing organizes cut-free derivations into
  construction cycles; derivations interpret soundly in any
  balanced dialogue category.
- **Theorem 4 (proof-as-tangle), l.1603.** The functor [−] from
  the free balanced dialogue category on X to the free ribbon
  category on X + 1 is faithful: a derivation tree modulo commuting
  conversions *is* its ribbon tangle modulo topological
  deformation. Formulas transport to signed sequences of ⊥'s and
  atoms; proofs to framed tangles. The symmetric degeneration
  (l.755) replaces balanced dialogue by symmetric dialogue and
  ribbon by compact-closed.

## What the source establishes

The topological completion of tensorial logic: a braided-and-
twisted sequent calculus (ribbon tensorial logic) whose categorical
semantics is balanced dialogue categories, together with a
proof-as-tangle theorem — the interpretation functor into the free
ribbon category is faithful, so proof equality modulo commuting
conversions coincides with topological deformation of framed
tangles. This resolves the proof-net identification problem for
the logic and gives game semantics a topological foundation (each
strand a pair of Opponent/Player moves). Cut-elimination, focusing,
and soundness support the main theorem; the symmetric/compact-
closed degeneration holds by the same route. Every mathematical
claim here is CONJECTURED until machine-checked.
