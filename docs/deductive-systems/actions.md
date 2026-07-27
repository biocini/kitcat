# The two actions, and the two cuts

Holding one half of an argument at its axiom leaves the edge-valued
form of that side. Bundling the far endpoint back in gives the
family transport.

```agda
coact-π f γ = reflect f (var x , γ)      -- holds the future  (twist⁻)
act-π   f t = reflect f (t , covar y)    -- holds the buffer  (twist⁺)

coact f γ = γ .fst , coact-π f γ         -- coterm y → coterm x   (contravariant)
act   f t = t .fst , act-π   f t         -- term   x → term   y   (covariant)
```

Both are fiberwise over the anonymous endpoint (the first component
comes back untouched), which lets them apply without transport.

## As displayed graphs

`term` and `coterm` are families over the objects, and `act` and
`coact` are lens data on them: `act` a covariant action on the term
family, `coact` a contravariant action on the coterm family. Each
cut's composability is a fibration condition on one of these
displays.

A lens states its unitor at its base's reflexive edge, and each
action holds one twist at its own axiom half. So a family's lens
sits over the graph of the twist its action does *not* hold, and the
unitor is a cancellation rather than an identity. VERIFIED
(`Cat.Logic.Display`):

```agda
term-lens   : oplax-cov-lens (graph⁻ G) (term-fam   G)   -- unitor = absorb⁺
coterm-lens : lax-ctrv-lens  (graph⁺ G) (coterm-fam G)   -- unitor = absorb⁻
```

That is where the framing lives in the lens language, and
[displays.md](displays.md) carries the rest: the coslice display,
each cut as a lift, and the two-sided base.

## The two cuts

Each cut absorbs one factor into an argument half and keeps the
other reflected. The positive absorbs its second into the coterm,
holding the future. The negative absorbs its first into the term,
holding the buffer. These are the two composite judgments, the two
**cuts**.

```agda
inj⁺ α p γ = α (γ .fst , coact p (γ .snd))
inj⁻ p β γ = β (act p (γ .fst) , γ .snd)

composite⁺ f g = inj⁺ (reflect f) g
composite⁻ f g = inj⁻ f (reflect g)
```

`composite⁺` cuts through a **pending read**: it takes `g` from a
future at the junction. `composite⁻` cuts through a **pending
write**: it puts `f` into a buffer there. Each carries exactly one
twist at its junction, of opposite sign. By the winding count of
[framing.md](framing.md), no cut of two edges can avoid carrying
one.

Nothing in this theory identifies the two. That identification is a
mediation. [mediation.md](mediation.md) says what it buys.
