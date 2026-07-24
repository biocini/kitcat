# Cat.Graph.Refl — what is implicit, and why

The convention governing two questions the suite's signatures face repeatedly.
When a parameter `A` precedes an argument whose type mentions `A`, is `A` implicit?
And when `{x y}` precedes `(p : edge x y)`, are the endpoints implicit? Both reduce
to one test — can every use site recover it — and both answers are consequences of
how `reflexive-graph.edge` and the family types reduce, not preferences.

## Structure parameters

A parameter is implicit exactly when every use site recovers it. Recoverability
falls into three tiers, each with a decidable test.

**Tier 1 — record-headed.** The parameter sits in a parameter position of a record
type heading a later explicit argument's type: `rx.disp G v' e'` (that is,
`reflexive-graphᴰ v' e' G`), `oplax-cov-lens G B`, `lax-ctrv-lens G B`,
`unbiased-lens G B`. Unification solves it from the argument's type before anything
else is checked, in inferring and checking position alike. **Implicit.**

So the base is implicit wherever a display or a lens is the principal argument:
`total-path-object`, `cov`/`ctrv`/`unb-disp-path-object`, the flattenings, the
total-opposite family, `is-displayed-univalent`, and the whole of `Fibration`'s
lens block and its `(D)` blocks.

**Tier 2 — Π-domain.** The parameter is the domain of a later explicit argument's
function type: `B : A → Type ℓ'`, or `B : dep-rx w z A`, which unfolds to
`A → reflexive-graph w z`. Rigid, so it solves when the argument is a term with a
declared type — a named definition, a variable, a projection. It does **not** solve
when the argument is a bare lambda and the result type buries the parameter under
projections.

`image`, `is-univalent-family`, `is-path-objects`, `Classify`'s `U` and `Poly`'s
`S` hide theirs; their families are always named. `product`, `coproduct` and their
path-object certificates cannot, and the failure is not repaired by supplying the
result type, since `rx.is-univalent` unfolds and leaves `product ?A ?B` under
projections:

```agda
prod-po' : ∀ {ℓ w z} {A : Type ℓ} {B : dep-rx w z A}
         → is-path-objects B → rx.is-univalent (product A B)

_ : rx.is-univalent (product Nat (λ n → discrete (Fin n)))
_ = prod-po' (λ n → disc-path-object (Fin n))    -- unsolved metavariables
```

**Tier 3 — projection-reached.** The parameter is reachable only through a field
projection. `rx.vfam G w z` and `rx.efam G w z` both unfold to function types whose
domain is `reflexive-graph.vtx G`, a stuck projection on a variable, and no unifier
solves `reflexive-graph.vtx ?G ≐ X`. **Explicit, always** — a family never
determines its base, so every family-keyed signature names it.

```agda
vfam-probe : ∀ {v e w z} {G : reflexive-graph v e} → rx.vfam G w z → Type v
vfam-probe {G = G} _ = reflexive-graph.vtx G

_ = vfam-probe 𝔉        -- unsolved metavariable
```

The tier is a property of the *later* argument, so a declaration with no principal
term argument has nothing to recover from and keeps its parameters explicit: the
lens type formers, and `cov`/`ctrv`/`unb-lens-structure-is-prop`, whose hypotheses
are all unfolding predicates.

Levels lead and are explicit exactly where un-inferable: `vfam`/`efam`/`disp`,
`dep-rx`, and `Univalent`'s four `*-of-path-objects` types.

This is the convention the reference tree carries:
`module _ {o h} {C : category o h} (D : categoryᴰ C o' h')`,
`module _ {o h} {C : category o h} {M : monoidal C} (B : braided M)`, against
`module _ {o h} (C : category o h)` where `C` is itself the subject.

## Endpoints

Whether an implicit endpoint solves is a property of the *base*, not of the
signature. `reflexive-graph.edge G x y` reduces whenever `G` is concrete — the same
transparency that carries the definitional unit laws — so unification meets the
reduced edge type, and the endpoint survives only if that type mentions it in a
solvable position.

| Base | Endpoint recovered |
| --- | --- |
| `discrete A` | yes — edge is `x ≡ y` |
| `image B` | yes — `B x ≃ B y`, rigid-rigid on `B` |
| `product` / `rx.cotensor` | yes — `(a : A) → edge (f a) (g a)`, a Miller pattern |
| `rx.op G` | yes — inherited |
| `AugSpx` | yes — `Fin m ≃ Fin n`, rigid-rigid on `Fin` |
| `coproduct` / `rx.tensor` | no — the source fibre vertex appears only under `transport` |
| `rx.comprehension` | no — the predicate components are discarded |
| `codiscrete A` | no — the edge type is `⊤` |
| `rx.total G D` | no in general — inherited from either factor |

The suite's own bases fall on the wrong side. Every classifier is a `rx.total` and
`𝔹Σ₂` is a `rx.comprehension`, so `Gph`, `RxGph`, `DGph`, `DRxGphOver`, `Magma`,
`cov-lens-over`, both polynomials, `List⁺`, `List⁻`, `pmc±` and `hUP±` all lose an
endpoint; `AugSpx` and `𝒰` are the only constructed bases that do not. Over `Gph`
the target is the lost one — `gph-lens` reindexes it through `has-pull`, so it
appears applied to `p .fst x` rather than to a bound variable, and no Miller
pattern is available.

The failure is asymmetric in a way no signature discloses: with endpoints implicit,
`has-pull` solves over `Gph` while `has-push` does not, from the same lens over the
same graph, because `has-pull`'s vertex argument happens to pin the endpoint the
base loses. Making `edge` opaque would fix it at the root and is unavailable — the
definitional unit laws rest on that transparency.

So the whole edge-indexed API names endpoints explicitly: `reflexive-graphᴰ.edge`,
`rx.hom.emap`, `rx.efam`, `rx.is-cov`/`ctrv-fibration` with their push/lift and
pull/colift operations, `rx.univalence.to-id`/`concat`/`inv`, the `push`/`pull`
synonyms behind `oplax-cov-lens.has-push` and `lax-ctrv-lens.has-pull`,
`universal-push`/`universal-pull`, `cov-straightening`'s `edge-ids`,
`straighten-equiv`, `straighten` and `unstraighten`, `component-path-object`, and
`unbiased-lens`' `linj`/`rinj`/`munitor`/`runitor`. A field additionally cannot do
otherwise: a type-synonym field auto-introduces its implicits and cannot be re-bound
by name.

Endpoints stay implicit exactly where another argument pins them rigidly:
`reflexive-graphᴰ.rx` and both lens unitors, pinned by `vtx x`; and `rx.to-edge`,
whose argument is a path and so rigid in the vertices at every base.

Total opposition exchanges the endpoints: `tot-op-lens L .has-pull x y p` is
`has-push L y x p`, and `fibration-duality` transposes the same way.

## The two axes are independent

Structure parameters are about what a *later argument's type* determines;
endpoints are about what a *base's edge type* retains. A signature can be right on
one and wrong on the other, and the tests are separate. When adding to the suite,
run both: give the new declaration its principal argument and ask whether the
parameter solves, and instantiate it at a `rx.total` and ask whether the endpoint
does.
