# Petrakis — Categories with dependent arrows

## Citation

Iosif Petrakis. *Categories with dependent arrows*.
arXiv:2303.14754v1 [math.CT] (secondary: math.LO), 26 March 2023.
<https://arxiv.org/abs/2303.14754>.
Author affiliation (per the paper): Department of Computer Science,
University of Verona.

## Vetting

Opened 2026-07-11 by Claude (Fable 5), at Lane's direction as part
of the founding `resources/` ingestion. Checked: title page and
abstract against the arXiv abstract page (title, author, subjects,
v1 submission date 26 Mar 2023); the section map below against the
paper's own §1 overview; the definition/theorem inventory extracted
from the full text (pdftotext). Bit-identity of the vendored file
with the arXiv v1 PDF (`arxiv.org/pdf/2303.14754v1`) verified by
sha256 on 2026-07-11. PROVISIONAL: agent-vetted; Lane's
confirmation of this entry is pending.

## Document hash

20-page arXiv v1 compile.

```
2298bc0e6878f09146d2c1b3a015fdee6cdb0ec729b98972ea26cf0dc8557983  cat-dep-arrows.pdf
```

## Summaries

Everything below records what the source states; every mathematical
claim is CONJECTURED until machine-checked.

**Abstract.** An abstract categorical formulation of dependent
functions, fundamental and independent of the Sigma-construction.
The paper defines categories with family-arrows (*fam-categories*)
and fam-categories with Sigma-objects ((fam, Σ)-categories) — a
(fam, Σ)-category with a terminal object is exactly a type-category
of Pitts, equivalently a category with attributes of Cartmell — and
then categories with dependent arrows (*dep-categories*). Every
(fam, Σ)-category is a dep-category in a canonical way; the notion
of Sigma-object is affected by the existence of dependent arrows,
and every (fam, Σ)-category is a (dep, Σ)-category canonically.

**Motivating question** (§1): what is the fundamental categorical
generalisation of a family of sets and of a dependent function?
The building blocks become objects, arrows, family-arrows,
dependent arrows — mirroring MLTT's types, functions,
type-families, dependent functions and Bishop Set Theory's sets,
functions, families of sets, dependent functions. Dependency is
captured as a primitive notion, not through the Sigma-type.

**Section map with key items:**

- §2 Categories with family-arrows: Definition 2.1
  (fam-category — to every object a corresponds a collection
  fHom(a) of family-arrows); examples; Definition 2.8.
- §3 fam-categories with Sigma-objects: Definition 3.1
  ((fam, Σ)-category); Proposition 3.7 (in a (fam, Σ)-category with
  terminal object 1, transport arrows witnessing equality of
  Sigma-objects over 1 are recovered for equal global elements).
  Relation to Pitts' type-categories (his main example being the
  classifying category of a dependently typed algebraic theory).
- §4 Categories with dependent arrows: Definition 4.1
  (dep-category — to every a and λ ∈ fHom(a) a collection
  dHom(a, λ) of dependent arrows over λ); Theorem 4.6 (every
  (fam, Σ)-category is a dep-category in a canonical way);
  Definition 4.8.
- §5 dep-categories with Sigma-objects: Definition 5.1
  ((dep, Σ)-category — the Sigma-object definition now uses the
  second-projection arrow as a dependent arrow, as in MLTT/BST);
  Theorem 5.4 (every (fam, Σ)-category is a (dep, Σ)-category
  canonically); Proposition 5.6.
