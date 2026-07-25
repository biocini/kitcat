# The displays over the graph

A virtual graph carries five displayed reflexive graphs over its own
underlying graph. Four are indexed by vertices and each picks a hand;
the fifth is indexed by edges and is the only one that sees both.

| index | `D.vtx` | `D.edge` over `p` | condition | transport |
| --- | --- | --- | --- | --- |
| vtx | `term x` | `act p t ≡ t′` | free | `act` |
| vtx | `coterm x` | `u ≡ coact p w` | free | `coact` |
| vtx | `hom a z` | `reflect w ≡ composite⁻ u p` | `is-composable` | `_⨾⁻ p` |
| vtx | `hom x c` | `reflect u ≡ composite⁺ p w` | `is-composable` | `p ⨾⁺_` |
| edge | `judgment x x` | `inj⁻ α p ≡ inj⁺ p β` | — | `inj⁻`, `inj⁺` |

The first four are the subject of [actions.md](actions.md) and
[composability.md](composability.md). This document is about the
fifth, and about what the whole family of displays does and does not
reach.

## Vertex-indexed is one-handed

A vertex-indexed display's edge over `p : x → y` relates a fiber datum
at `x` to one at `y`. Both data sit on the same side of the argument,
so no such display can compare the two hands. That is why the four
above come in mirror pairs and why `opⱽ` generates each from its
partner: the development is one hand's text instantiated twice.

An edge-indexed family is different. At each edge sits a component,
and *two* injections land in it — `linj` covariantly out of the
source's diagonal, `rinj` contravariantly out of the target's. The
involution swaps those two, so an unbiased lens is **fixed** by `opⱽ`
where a biased one is exchanged by it.

That fixes the formalism's role in this theory: a cross-hand statement
is an unbiased-lens datum, and a one-handed statement is a biased one.

## Judgments as an edge family

`judgment` weakens over the edges running between its two indices,
with identifications as component edges:

```agda
judgment± : rx.efam graph (o ⊔ h) (o ⊔ h)
judgment± x y _ = discrete (judgment x y)
```

The endpoints are named and the edge is not consulted — the same
weakening `cov-lens-to-unbiased` performs in `Cat.Graph.Refl.Lens`.
The diagonal is the endo-judgments, `rx.diag graph judgment± x =
discrete (judgment x x)`.

The two injections are the composite operations with the head left
general, and both are definable on a bare virtual graph:

```agda
inj⁻ : ∀ {x y z} → judgment x y → hom y z → judgment x z
inj⁻ α p γ = α (argue (γ .fst) (coact p (γ .snd)))

inj⁺ : ∀ {x y z} → hom x y → judgment y z → judgment x z
inj⁺ p β γ = β (argue (act p (γ .fst)) (γ .snd))
```

`inj⁻ (reflect f) p ≡ composite⁻ f p` and `inj⁺ p (reflect g) ≡
composite⁺ p g`, both by `refl`. The lens sees these only where the
head is an endo-judgment; off the diagonal they are the operations the
composites specialise.

VERIFIED in `Test.SpikeJudgmentLens`; the operations themselves are
`Cat.Logic.Base`.

## The unitors, and what they consume

A lens over `graph` states its unitors at that graph's own reflexive
edge, which is `idn`. The unit tier's absorptions hold at the units it
*projects* and say nothing about `idn`; readback bridges them. That is
the whole of what the unitors consume:

```agda
module unital (unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd))
              (unit-fiber⁺ : ∀ x → is-contr (fiber (act-π   {x} {x}) snd))
              (rb : readback) where
  absorb⁻ : ∀ {x} (α : judgment x x) → inj⁻ α (idn x) ≡ α
  absorb⁺ : ∀ {x} (α : judgment x x) → inj⁺ (idn x) α ≡ α

  judgment-lens .munitor _ α = absorb⁻ α ∙ sym (absorb⁺ α)
  judgment-lens .runitor _ α = sym (absorb⁺ α)
```

The two unit fibers together with a bare `readback` family inhabit the
whole lens — no contractibility over readback, no `absorb-coh`. The
spike takes them as parameters rather than as an `is-unital`, so that
what each result consumes is visible in its telescope; `flanks-agree`
is *stated* in the same module and used nowhere. VERIFIED in
`Test.SpikeJudgmentLens`.

So the flank coherence is not lens data, and cannot be: the mid unitor
is an identification of judgments, the flank coherence an
identification of identifications in a hom type. An unbiased lens'
unitors are edges of a component, and the components here are
discrete. The reflexive-graph vocabulary reaches the first two tiers
and stops there — a measurement of the one-dimensional formalism, not
a defect in the tier.

`munitor` is nonetheless the first place in the development where a
`⁻` fact and a `⁺` fact compose into a single path.

## Where Sterling omits, this theory contracts

An unbiased lens must carry the mid unitor and *at most one* of the
oplax and lax unitors. Carrying both costs propositionality of the
structure over a path-object base, and Sterling draws the analogy with
half-adjoint equivalences himself, which are coherent by virtue of
omitting one snake identity
(`resources/sterling-reflexive-graph-lenses`, `paper.tex:2203`;
SOURCE-CHECKED).

This family carries both. `absorb⁻` is the oplax unitor and `absorb⁺`
the lax one, and neither is optional: they are the two hands'
absorptions, and the theory is two-handed by construction. Omission is
therefore unavailable on principle rather than by accident.

What stands in its place is the ladder's own discipline.
`half-adjoint-forces-truncation` (`Test.SpikeUnitCanonical`) shows the
bare pair of a readback family with its coherence is not propositional
— a twist supported away from the endomorphisms carries one inhabitant
to another — so the fix is the `is-contr` wrapper, not a dropped
field. The two are the same phenomenon met twice, and the resolution
is the same each time: **where a formalism keeps propositionality by
omitting one of a symmetric pair, this theory keeps it by contracting.
The hands are never broken to buy coherence.**

## The univalence boundary is two boundaries

`rx.is-univalent graph` asks every fan to be a proposition — every
coterm type. A deductive system does not satisfy this. But the results
that hypothesise it are not all of the suite, and the line falls in a
useful place:

| hypothesises | reaches the fragment |
| --- | --- |
| `rx.is-univalent` of the **base** — `cov-`/`ctrv-`/`unb-lens-structure-is-prop`, `total-path-object`, the flattening and classifying certificates | no |
| path objects of the **components** — `cov-`/`ctrv-`/`unb-disp-path-object` | yes |

So no *uniqueness* or *totalisation* result reaches the theory, and
every *fiberwise* one does. Both new displays have discrete components
and are univalent outright:

```agda
judgment-disp-path-object = unb-disp-path-object judgment-lens (λ _ → disc-path-object _)
hom-disp-path-object      = unb-disp-path-object hom-lens      (λ _ → disc-path-object _)
```

VERIFIED in `Test.SpikeJudgmentLens`. The moduli direction escapes the
caveat for a different reason: it displays over a *classifying* graph
like `RxGph`, which is a path object, not over the deductive system's
own graph. Two bases, two regimes.

## The lens on homs

Beneath the judgment lens is one on the hom family, whose injections
are the two compositions and whose unitors are the two unit laws:

```agda
hom-lens .linj    _ _ p e = e ⨾⁻ p
hom-lens .rinj    _ _ p e = p ⨾⁺ e
hom-lens .munitor _   e   = unitr⁻ e ∙ sym (unitl⁺ e)
hom-lens .runitor _   e   = sym (unitl⁺ e)
```

Each hand absorbs `idn` into the slot its second factor enters, and
only there, so the `⁻` hand has a right unit law and the `⁺` hand a
left one. Neither has the other's; that asymmetry is what a one-handed
composition means, and it is why the two unitors of this lens are not
the same law twice.

Reflection carries the hom display's edges to the judgment display's:
over `p`, from `d` to `e`, `d ⨾⁻ p ≡ p ⨾⁺ e` reflects to `inj⁻
(reflect d) p ≡ inj⁺ p (reflect e)`.

## What the displays classify

A **section** of a displayed reflexive graph chooses a displayed
vertex over every base vertex and a displayed edge over every base
edge, agreeing with displayed reflexivity at the chosen edges
(`rx.section`, `Cat/Graph/Refl/Base.lagda.md`). It is `rx.hom` in
displayed form: a section of a constant display is a graph morphism,
definitionally both ways.

Read through that notion the displays are not bookkeeping. A section
of `hom-disp` is a family `d : ∀ x → hom x x` with `d x ⨾⁻ p ≡ p ⨾⁺
d y` for every `p` — an endomorphism of the identity, the **centre**
of the deductive system. Its reflexivity obligation is the mid unitor,
so it costs nothing. CONJECTURED; the section notion is checked, the
reading of it is not.

The biased displays classify the actions instead, and there the
statement is weaker in an informative way: they are graphs of
functions that already exist, so their fibration conditions hold
outright and all their content sits in `rx`, which is the unit tier.

## What no display of judgments is

None of these is the `judgment[_]` a *displayed* deductive system
needs. A displayed virtual graph over `G` is a displayed reflexive
graph — `ob[_]`, `hom[_]`, `idn[_]` — together with

```agda
reflect[_] : ∀ {f : hom x y} {x' y'} → hom[ f ] x' y' → judgment[ reflect f ] x' y'
```

which is the shape of `virtual-graph` itself, one level up. The
sequent vocabulary displaces mechanically because every piece of it is
built from `ob` and `hom` by `Σ` and `×`; `judgment` is the only `Π`,
and it is a `Π` over those. So `term[_]`, `coterm[_]`, `argument[_]`,
`conclusion[_]` and `judgment[_]` are the Σ-by-Σ displacements, with
no lens involved, and the displaced actions and injections are
projections of `reflect[_]`.

The lens displays are indexed by base objects and have judgments for
vertices; `judgment[_]` is indexed by a base judgment together with a
displayed object over each endpoint. Displaying and displacing are
different operations. Sketched in `Test.SpikeJudgmentLens`.
