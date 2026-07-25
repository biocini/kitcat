# Unitality

A unit is an edge whose action is the identity action. The tier says
such an edge exists and is unique — per hand, and without mentioning
the graph's chosen edge at all.

```agda
record is-unital : Type (o ⊔ h) where
  field
    unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
    unit-fiber⁺ : ∀ x → is-contr (fiber (act-π {x} {x}) snd)
```

Recall `coact-π {x} {x} : hom x x → (γ : coterm x) → hom x (γ .fst)`:
it sends an endo-edge to the map it induces on the coterms at `x`,
each coterm going to an edge rather than to another coterm. Its
fiber over `snd` — the map returning a coterm's own edge — is the
type of pairs `(e , proof that e acts as the identity)`, and the
field says that type is contractible.

The endomorphism is forced here and nowhere else. `snd` inhabits
`coact-π`'s codomain only when source and target agree, so *acting
as the identity* is a condition that typechecks for an endo-edge
alone; the action itself is general.

## Why the shape matters

The naive form of this tier — a chosen unit together with its unit
laws — is *not* a proposition when homs are untruncated. Capriotti
and Kraus prove that the type of identity structures is propositional
exactly under truncation (hom a family of sets for a precategory,
1-types for a 2-precategory), and state that it is not so in general
(`resources/capriotti-kraus-semi-segal`, `clean-arxiv.tex:1367`,
Theorem at `:1373`; SOURCE-CHECKED). Since the library never truncates
homs, that road is closed.

What survives is a fiber. `is-contr` is a proposition for any type
whatever, so:

```agda
is-unital-is-prop : is-prop is-unital
```

VERIFIED in `Cat.Logic.Base`. This is the same discipline
the library uses elsewhere for unit data: the representable-embedding
development takes `unital : ∀ {x} → fiber (yon {x}{x}) (λ _ → id)` as
its field and projects `idn = unital .fst`
(`reference/representable-embedding/Base.lagda.md:78,123`), and a
Kraus-style chain shows the corresponding bundled type collapses to
`is-eqv idn` (`reference/ternary-composition/VirtualAlt.lagda.md:573`).

## What the tier projects

The unit and its absorption are the center's two components:

```agda
unit⁻ x = unit-fiber⁻ x .center .fst
unit⁻-absorb x γ i = unit-fiber⁻ x .center .snd i γ
    -- coact-π (unit⁻ x) γ ≡ γ .snd
```

and dually `unit⁺`, `unit⁺-absorb`. Absorption is readback-free: it
comes out of the tier alone, which is what keeps the stability tier
below from being circular over it.

Absorption is also the displayed reflexivity of the two displays in
[actions.md](actions.md). Their vertices and edges exist on a bare
virtual graph; what a display lacks until this tier is its `rx`.
Reading the tier that way: **`is-unital` is the assertion that the
term and coterm actions carry displayed reflexive graph structure**,
stated as a fiber so that the unit itself is projected rather than
chosen.

## Uniqueness

A candidate unit is an edge together with a proof that its action is
the identity action — that is, an element of the very fiber the tier
contracts. So contractibility *is* uniqueness, and the identification
carries the witness, not only the element:

```agda
unit⁻-unique-σ : ∀ x (e : hom x x) (p : coact-π e ≡ snd)
               → (e , p) ≡ unit-fiber⁻ x .center
unit⁻-unique-σ x e p = sym (unit-fiber⁻ x .paths (e , p))

unit⁻-unique x e p = ap fst (unit⁻-unique-σ x e p)   -- e ≡ unit⁻ x
```

with a pointwise variant `unit⁻-unique-pt` taking the hypothesis as
`∀ γ → coact-π e γ ≡ γ .snd` and converting by `funext`. All VERIFIED
in `Cat.Logic.Base`.

The `ap fst`-of-a-contraction move is the one `rx.univalence.to-id`
makes in the reflexive-graph suite (`Cat/Graph/Refl/Base.lagda.md:187`),
which recovers a vertex identification as the shadow of a fan
contraction; here the contracted fiber is the unit fiber instead of a
fan, and the σ-form keeps what the shadow discards.

## The chosen edge

The tier says nothing about `idn`. That the graph's own reflexive
edge is *the* unit is a theorem, and readback is what proves it —
see [stability.md](stability.md). The two statements meet at the
identity because evaluation at the axiom is the action applied to
`idn`:

```
    eval (reflect e)  ≡  coact-π e x (idn x)      definitionally
```

so a candidate's absorption, instantiated at `idn`, and readback at
that candidate, are two paths with a shared endpoint. Composing them
identifies the candidate with `idn`.

## Neutrality is a different condition

An edge is *neutral* when composing with it is an equivalence — in
horn form, when the relevant outer horns have contractible fillers
(Capriotti–Kraus, `clean-arxiv.tex:1640`, with the Yoneda-style
characterisation at `:1674`; SOURCE-CHECKED). Neutrality of `idn` is
also a proposition, and the library has it in the magmoid setting as
`is-neutral-is-prop` (`src/Cat/Depreciated/Magmoid/Base.lagda.md:155`).

It is not the same statement as unitality, and it does not replace
it: neutrality gives *cancellation* — a divisor is unique — while
what the theory runs on is *absorption*, that the action is the
identity. The tier above asserts the latter, in the only form that
stays propositional.
