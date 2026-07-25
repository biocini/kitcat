# The two-sided base, and what a mediation is

Mixed variance is a property of the display, not of `judgment`. Over
the graph paired with its own opposite the family transports
covariantly in a single move, and the unbiased apparatus of
[displays.md](displays.md) collapses to one ordinary covariant lens.

That base is where the two composite judgments become two pushforwards
into a common fiber, so interchange is the agreement of a cospan; and
where the failure of a lens to be functorial is exactly the gap
between the two compositions.

## The base

Nothing new builds it — it is the suite's binary product of the
underlying graph with its opposite:

```agda
two-sided = rx.binary-product (rx.op graph) graph
```

A vertex is a pair of objects; an edge into `(x′ , y′)` from `(x , y)`
is `hom x′ x × hom y y′`, backward on the first coordinate and forward
on the second; reflexivity is `(idn x , idn y)`. All by `refl`.

## `judgment` is covariant over it

Both slots travel at once, the term slot by `act` and the coterm slot
by `coact`, and the conclusion's endpoints are untouched because each
action preserves the anonymous endpoint on the nose:

```agda
bipush : ∀ {x y x' y'} → hom x' x → hom y y' → judgment x y → judgment x' y'
bipush a b α γ = α (argue (act a (γ .fst)) (coact b (γ .snd)))
```

That is axiom-free. With a deductive system it becomes the transport
of an *oplax covariant* lens on the discrete judgment family, with one
unitor `bipush (idn x) (idn y) α ≡ α` and a univalent display via
`cov-disp-path-object`. VERIFIED in `Test.SpikeTwoSided`.

So the two formalisms are two readings of one object. Displayed over
the objects, `judgment` needs the unbiased lens and its two
injections; displayed over the objects paired twice, it is a covariant
lens with one transport and one unitor. **The choice of base is what
selects them,** and the difference between the two bases is `rx.op`.

## Interchange is a cospan

Held at one leg's reflexivity and applied to one factor's reflection,
`bipush` is a composite judgment:

```agda
bipush (idn x) g (reflect f) ≡ composite⁻ f g
bipush f (idn z) (reflect g) ≡ composite⁺ f g
```

Both land in the fiber at `(x , z)`, and they come from *different*
vertices:

```
        (x , y)                       (y , z)
            \                            /
       (idn x , g)                (f , idn z)
              \                        /
                  ‾‾‾‾ (x , z) ‾‾‾‾
```

Neither leg is the other's reversal and the two sources are distinct,
so the configuration is a cospan. Interchange is the statement that
its two pushforwards agree, and the identification is exact in both
directions (`interchange-is-cospan`, `cospan-is-interchange`; VERIFIED
in `Test.SpikeTwoSided`).

## Why no display has interchange as an edge

A displayed edge relates data over the *two ends of one base edge*,
and an unbiased lens' injections source at **diagonal** components.
`reflect f` and `reflect g` sit at `(x , y)` and `(y , z)`. A base
making both of those diagonal would have to make the composability
relation reflexive — a pair `(f , f)` would have to be composable —
and it is not.

That is the semi-Segal obstruction, met inside the lens vocabulary.
Capriotti and Kraus record that adapting Segal spaces to type theory
forces one to *give up degeneracies* — the resulting structures are
the semisimplicial types — and that degeneracies are what encode the
identity part of a categorical structure
(`resources/capriotti-kraus-semi-segal`, `clean-arxiv.tex:334`;
SOURCE-CHECKED). Reflexive-graph language is on the other side of that
line: `rx` *is* the degeneracy, and every lens datum is stated at it.
Composable pairs are the first place a degeneracy fails to exist, so
they are the first place the vocabulary cannot reach. That the
diagonal constraint on `linj`/`rinj` and their obstruction are the
same wall is CONJECTURED.

## Each action distributes over its own hand

Composability alone gives this, per hand and with no mediation. The
head-rewriting witness is the entire proof and the anonymous endpoint
never moves:

```agda
act-⨾⁺   p q t i = t .fst , reflect-⨾⁺ p q i (argue t (covar z))
coact-⨾⁻ p q e i = e .fst , reflect-⨾⁻ p q i (argue (var x) e)
```

so `act (p ⨾⁺ q) t ≡ act q (act p t)` and `coact (p ⨾⁻ q) e ≡ coact p
(coact q e)`. In `Cat.Logic.Base`, as projections of `is-composable`.

## A mediation is the lens's missing functoriality

A lens carries a transport and a unitor and asks nothing about
composites of base edges. Ask it anyway. The two-sided action *does*
compose — but look at the base edge it lands on:

```agda
bipush a' b' (bipush a b α) ≡ bipush (a' ⨾⁺ a) (b ⨾⁻ b') α
```

**The backward coordinate wants `_⨾⁺_` and the forward coordinate
wants `_⨾⁻_`.** The two-sided base carries no single composition for
which the lens is functorial. A mediation is precisely what makes
those one operation; with it the composite edge is formed by one
composition throughout and the lens becomes a functor over a base that
now has a composition of its own.

The two conditions are not independent — interchange delivers the
mediation, by reflecting both compositions onto the same judgment and
reading the result back:

```agda
interchange→mediation I f g =
  sym (unit (f ⨾⁻ g)) ∙ ap eval (reflect-⨾⁻ f g ∙ I f g ∙ sym (reflect-⨾⁺ f g)) ∙ unit (f ⨾⁺ g)
```

`interchange` and `mediation` are named in `Cat.Logic.Base` for this
purpose: so that what lies outside the theory can be stated in the
theory's own vocabulary rather than by pointing elsewhere. Neither is
asserted anywhere.

## What this says about the fragment

A lens is exactly the amount of structure that survives without a
mediation: transport and a unitor, no functoriality. That the
interchange-free fragment is expressible in reflexive-graph language,
and interchange is not, is one statement and not two.

It also sharpens what a mediation *is*, against the reading in
[the-bundle.md](the-bundle.md). It is not merely an identification one
may or may not adjoin. It is the datum that turns a reflexive graph
carrying a lens into a base carrying a composition and a functor over
it — which is why a deductive system with one point of that space is a
category, and why the space itself is where braiding and chirality
live.
