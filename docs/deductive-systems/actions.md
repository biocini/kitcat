# The two actions, and the two cuts

Holding one half of an argument at its axiom leaves the edge-valued form
of that hand; bundling the far endpoint back in gives the family
transport.

```agda
coact-π f γ = reflect f (var x , γ)      -- coterm hand: holds the future
act-π   f t = reflect f (t , covar y)    -- term hand:   holds the buffer

coact f γ = γ .fst , coact-π f γ         -- coterm y → coterm x   (contravariant)
act   f t = t .fst , act-π   f t         -- term   x → term   y   (covariant)
```

Both are fibrewise over the anonymous endpoint — the first component is
returned untouched — which is what lets them be applied without
transport.

## As displayed graphs

`term` and `coterm` are families over the objects, and `act` and `coact`
are lens data on them: `act` a covariant action on the term family,
`coact` a contravariant action on the coterm family. In the language of
`Cat.Graph.Refl` these are the displayed structures over the underlying
graph, and each hand's composability is a fibration condition on its own
display.

One thing the framing changes. A displayed *reflexive* graph asks its
lift over reflexivity to be trivial. Here it is not: the action of a
twist is one cancellation, not the identity — see
[unitality.md](unitality.md). So the two displays are reflexive **up to
one transmission**, and that is where the framing lives in the lens
language.

## Composing terms with terms, coterms with coterms

The term hand composes a term with a term, closing the far end with the
buffer; the coterm hand composes a coterm with a coterm, holding the
future. Carried into one slot of a reflected head, these give the two
composite judgments — the two **cuts**.

```agda
inj⁻ α p γ = α (γ .fst , coact p (γ .snd))
inj⁺ p β γ = β (act p (γ .fst) , γ .snd)

composite⁻ f g = inj⁻ (reflect f) g
composite⁺ f g = inj⁺ f (reflect g)
```

`composite⁻` cuts through a **pending read**: `g` is taken from a future
at the junction. `composite⁺` cuts through a **pending write**: `f` is
put into a buffer there. Each carries exactly one twist at its junction,
of opposite sign, and by the winding count of
[framing.md](framing.md) no cut of two edges can avoid carrying one.

Nothing in this theory identifies the two. That identification is a
mediation; [mediation.md](mediation.md) says what it buys.
