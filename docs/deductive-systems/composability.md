# Composability

The first tier says each composite judgment is represented, uniquely.

```agda
record is-composable : Type (o ⊔ h) where
  field
    contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
           → is-contr (is-representable (composite⁻ f g))
    contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
           → is-contr (is-representable (composite⁺ f g))
```

Both hands are fields of one record, so an instance supplies one
`is-composable` and a consumer never handles the hands separately.

Unfolding a field: `is-representable α` is `fiber reflect α`, so
`contr⁻ f g` says the type of pairs `(s , reflect s ≡
composite⁻ f g)` is contractible. There is an edge representing the
composite judgment, and it is unique together with its witness.

## Composition is a projection

Nothing is declared. The composition is the center's first
component, and the path that makes it a composite is the center's
second:

```agda
_⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
f ⨾⁻ g = contr⁻ f g .center .fst

reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
           → reflect (f ⨾⁻ g) ≡ composite⁻ f g
reflect-⨾⁻ f g = contr⁻ f g .center .snd
```

and identically `_⨾⁺_`, `reflect-⨾⁺` on the other hand. The two
compositions are genuinely different operations on the same graph;
the theory never identifies them.

`reflect-⨾⁻` is the workhorse. Every later fact about `⨾⁻` is
obtained by rewriting a head with it and reading the result at a
chosen argument — there is no separate equational theory to carry.

Because the fields are contractibility statements, the tier is a
proposition immediately:

```agda
is-composable-is-prop : is-prop is-composable
```

VERIFIED in `Cat.Logic.Base`, by `is-contr-is-prop` under
the quantifiers.

## The slice and the coslice

The tier has an exact reading in `Cat.Graph.Refl`. Fix an object `a`
and take the edges out of it as a family over the graph's vertices;
a displayed edge over `p` records that its target is a composite:

```agda
coslice a .reflexive-graphᴰ.vtx z          = hom a z
coslice a .reflexive-graphᴰ.edge y z p u w = reflect w ≡ composite⁻ u p
coslice a .reflexive-graphᴰ.rx u           = coslice-rx u
```

Against that display, this hand's field *is* the covariant fibration
condition, and the fibration's operations are the composition and its
witness — all definitional:

```agda
coslice-is-fibration _ _ _ p u = contr⁻ u p          -- rx.is-cov-fibration
push-is-comp _ _ _ _ _ = refl                        -- cov.push  ≡ _⨾⁻_
```

The mirror is the slice at a fixed target, `slice c .vtx x = hom x c`,
with displayed edges `reflect u ≡ composite⁺ p w`; there the field is
`rx.is-ctrv-fibration` and the pullback is `_⨾⁺_`. VERIFIED in
`Test.SpikeDeductiveSystem` (appendix) and `Test.SpikeRxDict`.

This is where the crossing of the two vocabularies shows. The hand
whose composite judgment is built with `coact` is the hand whose
*coslice* is fibered *covariantly*; hands are named for the slot they
consume, so that neither name has to lie, and `push`/`pull` keep
their reflexive-graph meaning as the transports of a display.

```
    ⁻ hand   coslice a = hom a −    covariant     rx.cov-fibration.push  = _⨾⁻_
    ⁺ hand   slice   c = hom − c    contravariant rx.ctrv-fibration.pull = _⨾⁺_
```

These displays are the ones with content. The term and coterm
displays of [actions.md](actions.md) are graphs of functions that
already exist, so their fibration conditions hold outright; here the
displayed edge says a target *represents a composite*, which is not
the graph of anything, and the condition is the tier.

One layering fact is worth stating precisely, because it explains why
the displays appear later than the tier. The fibration *condition*
mentions only vertices and edges, so it is statable on a bare virtual
graph — which is why `is-composable` is a predicate on one. Packaging
the family as a `reflexive-graphᴰ` needs the displayed reflexivity
`coslice-rx : reflect u ≡ composite⁻ u (idn y)`, and that is a flank
absorption, supplied by the tiers above. So Sterling's fibration and
lens API becomes literally available at the unit tier, not before.

## Each action distributes over its own hand

The head-rewriting witness is the whole proof, and the anonymous
endpoint is handed back untouched, so each identification is that
witness read at one argument:

```agda
act-⨾⁺   p q t i = t .fst , reflect-⨾⁺ p q i (argue t (covar z))
coact-⨾⁻ p q e i = e .fst , reflect-⨾⁻ p q i (argue (var x) e)
```

giving `act (p ⨾⁺ q) t ≡ act q (act p t)` and `coact (p ⨾⁻ q) e ≡
coact p (coact q e)`. VERIFIED in `Cat.Logic.Base`, as projections of
the tier.

Each hand distributes over its *own* composition and no other. That is
the whole of what this tier says about the two operations interacting
with the actions, and it is what makes the two-sided transport of
[mediation.md](mediation.md) compose along one composition per
coordinate rather than one throughout.

## Associativity, and what it costs

Associativity is not an axiom and not a separate coherence. Both
bracketings of three edges represent judgments related by rewriting a
head with `reflect-⨾⁻`, so both are points of one contractible fiber,
and the identification is the `fst`-shadow of the contraction. The
higher cells continue the same way: any two routes between placed
points agree because the ambient fiber is contractible, which is the
associahedron tower for that hand.

Nothing in this consumes the other hand, and nothing consumes an
interchange. Each hand carries its own tower.
