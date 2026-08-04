# The mathematical standpoint

`Core.Kan` today *constructs* (`hcom`/`hfil`/`com`/`fil` plus ~1,300
lines of consequences) and then states its own uniqueness theory ad
hoc (`Total-sys-contr`, `HComposite.unique`, four `*-unique` lemmas,
`pcom.contr`). The Composite standpoint: every one of those is
contractibility of a fan, and the Rx vocabulary owns that statement.
The identification comes in three tiers of descending definitional
strength, and the tiering is the plan's safety case. The tiers
executed early are conversions the typechecker enforces. The one
tier that is genuine mathematics comes last, behind a gate.

## Tier 1: one theorem, four costumes (refl)

VERIFIED, `Test.KanIdentities`, probes 1–6.

| | the space | center | contraction |
| --- | --- | --- | --- |
| `Core.Kan` | `Total-sys φ s = Σ x , sys-composite φ s ≡ x` | `(composite , plid)` | `p i , λ j → p (i ∧ j)` |
| reference | `Comp φ u = Σ s , composite φ u ≡ s` | `(composite , plid)` | `p i , λ j → p (i ∧ j)` |
| `Core.Transport.Base` | `Singl x = Σ y , x ≡ y` | `(x , refl)` | `q i , λ j → q (i ∧ j)` |
| `Core.Rx` | `rx.fan (discrete A) x` | `fan-center x` | via `prop-inhabited→is-contr` |

Not an analogy: `Total-sys φ s` is
`rx.fan (discrete A) (sys-composite φ s)` and `Total-sys-contr φ s`
is `Singl-contr (sys-composite φ s)`, both by `refl`. At the type
level, `Sys` is `PartialsP` at a constant family and `HSys` is
`PartialsP` verbatim (checked by retyping, these land in `Exo`).
Restating this tier is conversion, not proof: a wrong execution step
fails to typecheck, so there is no drift channel.

Reading: a Kan operation is a choice of center in a contractible
fan. `hcom` picks the center, `hfil` is the contraction, and every
uniqueness lemma in `Core.Kan` is `is-contr→is-prop` at some fan.

## Tier 2: the fibration reading (refl, the tier the plan rests on)

VERIFIED, `Test.KanIdentities`, probe 7. For `P : A → Type v`, the
displayed graph over `discrete A` with

```agda
edge x y p a b = PathP (λ i → P (p i)) a b
```

has `SysP.SysLift p a` as its displayed fan on the nose, and
`SinglP-contr` witnesses `rx.is-cov-fibration`:

| fibration interface | its value at a type family |
| --- | --- |
| `push` | `transport` |
| `lift` | `transport-filler` |
| `lift-unique` | `SinglP-contr .paths` |

Every type family is both a covariant and a contravariant fibration
over `discrete A`, and that is the content of `transp`. This
restores the contractibility half (the reference's
`LiftP-is-contr`) that the in-tree port dropped, and it is the tier
the plan rests on. After it, `transp` *means* "discrete families are
bifibrations": the identical shape, certified in `Test.RxVirtual`,
as the frontend's `is-composable` at the term and coterm displays.
`Core.Kan` becomes the worked Core-level instance of the deductive
system's composability tier.

Supporting fact already in-tree: the library's `J` is
`Total-sys-contr .paths` plus a transport
(`Core.Transport.J.J-sys`): Kan and Transport are one development at
the root, and the discipline makes the library say so.

A precision that Stage 2.1 depends on: the identification
`SysP.fillerP ~ cov-fibration.lift` is **propositional, not
definitional**: the com-tower and the transp-filler are two centers
of one contractible space, not one term. The one-construction
principle resolves it as a choice, not a bridging lemma. See
[stage-2-discipline](stage-2-discipline.md).

## Tier 3: `HComposite` as an unbiased lens (propositional, deferred)

`HComposite p q r = Σ s , HCell p q r s` has a left leg, a right
leg, a middle, and a composite. `unbiased-lens` has `linj`/`rinj`/
`munitor`/`runitor` over an edge-indexed family:

| unbiased lens | `Core.Kan` | `Core.Groupoid` |
| --- | --- | --- |
| edge-indexed family | `HCell p q r`, indexed by the middle | `emb`, indexed by the tight cell |
| `linj` | `pcom.lsplit` | `yon` |
| `rinj` | `pcom.rsplit` | `noy` |
| `munitor` | `pcom.unit` | `emb-parametric` |
| `runitor` | `pcom.ideml`/`idemr` | `yon-comp`/`noy-comp` |
| `unb-lens-structure-is-prop` | `pcom.contr` | `representable-contr` |

The correspondence is real but consists of theorems, not
conversions: the one tier where restatement is mathematics rather
than renaming, and the only tier that would require the lens record
below `Core.Kan` (decision D7). It waits for Stage 5. Stage 2 states
the reading in `Core.Kan`'s prose and stops there.

Adjacent fact (Stage 2.4): the three representability developments
are three curryings of one ternary operation. They are
`Core.Groupoid.emb` (left leg), `Core.Groupoid.Virtual.repr.emb`
(middle, refl-equal to the first: VERIFIED, `Test.KanIdentities`
probe 8), and `Core.Path.Composition.Repr` (a third copy of the
middle), with two full `iso→equiv` proofs (~110 lines) for one
operation and a consumer-less alias `yon-unbiased = repr`. Under
ruled D2 they collapse to the discrete instance of the backend's
general form: the latent virtual-graph theory of the cubical
machinery made explicit
([stage-2-discipline](stage-2-discipline.md)).
`Lens.unb-lens-structure-is-prop` exhibits the general route:
uncurry over the fan, collapse at the center with `Π-contr-dom`,
read off the residual fan or cofan.

## The Exo boundary

`Sys` lands in `Exo`. Reflexive graphs are `Type`-valued. The Rx
articulation therefore reaches exactly the Σ-typed layer (fans of
composites, lifts, representability) and cannot descend to the
partial-element plumbing. The discipline's opening prose states the
boundary: *the plumbing constructs centers. The Rx layer states what
they are centers of.* Within `Core.Composite` the same boundary
falls between `SysLift`/`syslift-center` (path-shaped lifts:
Rx-articulable) and `SysOver`/`fillerP` (systems with walls over the
filler: plumbing).

## The strata

Reflexive-graph *structure* needs no Kan primitive: pure interval
and Σ (VERIFIED, `Test.RxTier1`: the whole Tier-1 layer compiles on
`Core.Type` + `Core.Base` + `Core.Data.Sigma`). The *theory* needs a
Kan primitive, and the primitives split. `is-contr→is-prop` is
provable from `transp` alone:

```agda
is-contr→is-prop′ c x y =
  primTransp (λ i → c .paths x i ≡ y) i0 (c .paths y)
```

(checked 2026-07-24 in a session probe on the Tier-1 imports plus
the primitive, certificate lands if D6 goes forward). The
composition calculus needs `hcom`. Three strata:

| stratum | carries |
| --- | --- |
| interval/Σ (`Core.Base`) | structure: graphs, fans, displays, fibration *conditions* |
| `transp` | transport theory: `is-contr→is-prop`, singleton lifts, path-object proofs that consume only these |
| `hcom` | composition theory: `_∙_`, `pcom`, the coherence calculus |

The module cut currently bundles `transp` and `hcom` in `Core.Kan`,
so both flavors of theory sit above one line. Whether the `transp`
stratum ever reifies is decision D6, and no stage depends on the
answer.
