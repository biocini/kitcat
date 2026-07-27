# Stage 3: frontend, `Cat.Logic`

The virtual-graph and deductive-system machinery over the backend.
The record shapes are ruled by
`notes/2026-07-22-deductive-system-design.md` and by the 2026-07-24
rulings ([README](README.md)). The design note is the foundation.
Its obligations O1–O6 and rulings are not duplicated here. The compatibility ruling
binds every item: domain vocabulary is free, definitions must reduce
to their `Core.Rx` counterparts, and this layer re-derives no lemma
`Core.Rx` proves.

## 3.1 `virtual-graph`, bundled

A field carrying the reflexive graph, plus `emb`: ruled bundled,
with the domain names re-exported. The probe shape
(`Test.RxVirtual`):

```agda
record virtual-graph v e : Type₊ (v ⊔ e) where
  field graph : reflexive-graph v e
  open reflexive-graph graph public
  field emb : {x y : vtx} → edge x y
            → ∀ w → edge w x → ∀ z → edge y z → edge w z
```

(`emb`'s currying is decision D3. Uncurried through the judgment
type makes representability a one-liner.)

Re-export minding the clash: opening the backend interface wholesale
re-imports the graph's own fields:

```agda
open reflexive-graph graph public
  renaming (vtx to ob; edge to hom; rx to idn)
open rx graph public
  using (cofan; fan; cofan-center; fan-center)
  renaming (cofan to term; fan to coterm;
            cofan-center to var; fan-center to covar)
```

Note the inversion: terms are the *cofan*, coterms the *fan*. The
fans-are-propositions condition therefore lands on coterms. The
backend theorem that the two variances coincide
(`is-univalent→op`/`is-univalent-op→`) is a cross-hand fact the
record never asserts.

Inference discipline (measured, `Test.RxBundle`): the bundled graph
is projection-reached and unrecoverable at display-keyed sites. The
interface therefore keys off a module parametrized by the
structure, and cross-module signatures name it, already the ruled
convention for family-keyed signatures.

## 3.2 Retarget `Cat.Logic.Type`

Its `term`/`coterm`/`var`/`covar` are domain vocabulary landing on
the backend forms. With D2 ruled, `is-representable` and
`hom≃total-representable` are the backend theorem restated in the
sequent vernacular (definitional restatements, not new proofs).
`reflect` carries the backend action as the record's field.
`judgment`, `argument`, `conclusion` remain frontend vocabulary with
no backend counterpart. Cheap only while the module is small. Do it
first.

## 3.3 `is-deductive-system`, tiers in dependency order

| tier | statement | is-prop by | cost |
| --- | --- | --- | --- |
| `is-composable` | both fibration conditions at the term and coterm displays | `fibration-is-prop` (0.2) | free |
| `is-unital` | per hand: `is-equiv` of the two emb-actions at `idn`, plus `idem` | **O1** | real work |
| `is-stable` | `is-contr` of the flank-restriction fiber | `is-contr-is-prop` | free |

The order is forced: the unit coherences are associator-shaped, so
they mention the composition operation, the composability tier's
projected fiber center. Honest type-former dependence.

The boundary, VERIFIED in `Test.RxVirtual`: `push` and `pull` are
definable from `emb` alone (and pull over the graph *is* push over
the opposite graph, definitionally). But packaging terms and coterms
as displayed *reflexive* graphs, which is what buys `total`,
`component`, `total-path-object`, requires the unit laws. The
displayed reflexivity field is exactly
`emb (rx x) w u x (rx x) ≡ u`, per hand. The backend closure
calculus comes online on the unital side only.

## 3.4 O1

Not discharged by the gist
(`notes/2025-06-03-coherent-unit-gist.md`): its
`idem-equiv→contr-idn` consumes both coherences as hypotheses, while
O1 requires propositionality over the graph and composability tier
only. The work:

1. Transposition to the emb-action forms: the gist's `is-iso` is
   composition-action, which the unit tier excludes on
   stability-circularity grounds.
2. The coherences from per-hand associativity plus `idem`:
   CONJECTURED. At the path-groupoid instance the derivation is one
   line (`assoc i i f ∙ ap (_∙ f) idem`, checked 2026-07-24 in a
   session probe). The per-hand emb-action form is the open part.
3. The round trips of `is-coherent-unit ≃ is-idem-equiv`: the gist
   has both maps and neither composite.

The fiber-center construction needs no new Kan machinery:
`Core.Kan.cone w0 w1 : Square w0 (w0 ∙ sym w1) w1 refl` is the
gist's `ι` in kitcat vocabulary. Typing checked 2026-07-24 in a
session probe. **The certificate lands with this item.**

Whether O1 is in scope for this arc or 3.5 ships with the unit
tier's propositionality as a stated obligation is decision D4.

## 3.5 `is-deductive-system-is-prop`

`Σ-is-prop` twice over 0.2's lemma, O1, and `is-contr-is-prop`.
Helpers on the shelf: `is-contr-is-prop` and `is-prop-is-prop`
(`Core.Transport.Properties`), `Π-is-prop`, `Σ-is-prop`, and
`is-prop-equiv` (`Core.HLevel.Base`), and `is-equiv-is-prop`
(`Core.Equiv.Properties`).

## 3.6 The `deductive-system` bundle

Per the design note's record sketch. Morphisms (lax/colax
hand-flavors) and SIP/moduli statements follow its mechanical
roadmap.

## 3.7 `Cat.Logic.Univalent`

On `--cubical`, by the segmentation rule: the record's
propositionality collapses identity of deductive systems to identity
of virtual graphs. The reflexive-graph half needs `ua`
(`Core.Rx.Univalent` after Stage 1).

Then the roadmap-0–7 content: the two-handed calculus, the
associahedron towers (per-hand, paths in contractible iterated
fibers, no interchange consumed), mediation and Med(D), duploids.
