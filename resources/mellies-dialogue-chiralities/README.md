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
PROVISIONAL: agent-vetted; Lane's confirmation of this entry is
pending.

## Document hash

Two copies are vendored; they are different compiles of the paper.

- `2-dialogue-categories-and-chiralities.pdf` — the **citation
  copy**: the revised manuscript hosted at the IRIF URL above,
  59-page compile carrying the journal record line "Communicated by
  M. Hasegawa. Received December 2, 2012. Revised August 6, 2014".
  Bit-identity with the IRIF URL verified by sha256 on 2026-07-11.

  ```
  3e74e139035f46434651d34649dce168e68c68224cea67a996efe2a3dfb5c071  2-dialogue-categories-and-chiralities.pdf
  ```

- `Dialogue_Categories_and_Chiralities.pdf` — an **earlier
  preprint** (50-page compile, ANR RECRE support footnote, older
  abstract wording: "refutations" where the revision has
  "counter-proofs"). Origin of this copy unpinned: it matches no
  canonical URL tested (IRIF, arXiv); its filename matches the
  ResearchGate slug. Kept as the file originally supplied; do not
  cite section numbers from it.

  ```
  f685daecb6c4fb69f43e47d0d0fdde176e2ac5a1cd524b60931d27894ca64e5e  Dialogue_Categories_and_Chiralities.pdf
  ```

## Summaries

Everything below records what the source states (checked against
the citation copy); every mathematical claim is CONJECTURED until
machine-checked.

**Abstract.** A two-sided notion of dialogue category — *dialogue
chirality* — formulated as an adjunction between a monoidal
category A of proofs and a monoidal category B of counter-proofs
equivalent to its opposite category A^op(0,1). The two-sided
formulation is compared to the original one-sided formulation of
dialogue categories by a 2-dimensional equivalence between a
2-category of dialogue categories and a 2-category of dialogue
chiralities; the resulting coherence theorem clarifies in what
sense every dialogue chirality may be strictified to an equivalent
dialogue category.

**Section map.** §1 Introduction; §2 The basic case: categories
and chiralities; §3 Monoidal categories and chiralities; §4
Dialogue categories; §5 Dispute chiralities; §6 Dialogue
chiralities; §7 The coherence theorem; §8 Back to dispute
chiralities and categories; §9 Final remarks.

**Key definitions and theorems** (locations in the citation copy):

- Definition 1 (chirality, §2): a pair (A, B) of categories
  equipped with an equivalence of categories between B and the
  opposite of A. Theorem 1 (§2): coherence theorem for the basic
  case — a pair of 2-functors F, G exhibits the 2-dimensional
  equivalence between categories and chiralities.
- Definition 3 (monoidal chirality, §3); Theorem 2 (§3): the
  monoidal coherence theorem, same F/G pattern one level up.
- Definition 4 (tensorial pole, §4); Definition 5 (dialogue
  category, §4): a monoidal category equipped with a tensorial
  pole.
- Definition 6 (dispute chirality, §5); Definition 7 (dialogue
  chirality, §6): a pair of monoidal categories with the adjunction
  and monoidal-equivalence data of the abstract.
- Theorem 3 (§7.5): the paper's main result — the 2-dimensional
  equivalence between the 2-category of dialogue categories and
  the 2-category of dialogue chiralities.
- Definition 9 (exponential ideal, §8).

**Framing.** The Forewords situate the paper in the tensorial-logic
program: the interactive nature of continuations, with a dialogue
category recast as a category of proofs confronted with a category
of refutations. The introduction states MacLane's coherence theorem
as the paradigm being generalized (a category is equivalent to a
strict monoidal category precisely when it is monoidal).
