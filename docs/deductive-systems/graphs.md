# The framing as two reflexive graphs

A twist is a reflexivity datum, so a framing is a pair of reflexive-graph
structures on one underlying graph. `Cat.Logic.Graph` is where the theory
names `Cat.Graph.Refl`, and nothing in it consumes an axiom.

```agda
graph⁺ G .rx = twist⁺ G          graph⁻ G .rx = twist⁻ G
```

The two share vertices and edges. A virtual graph is therefore not a
reflexive graph with extra data on the side; it is the *pair*, together with
`reflect`.

## The dictionary

Fans and cofans name no reflexivity, so the two argument families are read
off either graph.

VERIFIED (`Cat.Logic.Graph`), all `refl`:

```agda
term-is-cofan   x : term x   ≡ rx.cofan (graph⁺ G) x
coterm-is-fan   y : coterm y ≡ rx.fan   (graph⁺ G) y
```

The centres are not shared. Each argument half is the centre of *its own*
graph, and the axiom pairs one from each:

```agda
var-is-cofan-center   x : var x   ≡ rx.cofan-center (graph⁻ G) x
covar-is-fan-center   y : covar y ≡ rx.fan-center   (graph⁺ G) y
```

This is where the crossing that runs through the whole theory comes from. It
is not a convention about which sign goes where: the term half's centre lives
in one graph and the coterm half's in the other, so any statement pairing
them reads one graph against the other. The cells are exactly that
comparison — each is one graph's reflexivity read through the other graph's
action — and each reflexivity is the unique edge whose action lands on the
cell of the other side.

## Univalence

Univalence is a condition on fans, which name no reflexivity. VERIFIED
(`Cat.Logic.Graph`): `univalence-shared` is `refl` — the two graphs are path
objects together, and the framing does not enter the condition.

So being a path object is a property of the underlying graph alone. What the
framing then contributes, over a path object, is a shift: `to-edge` is built
from a reflexivity datum, so the two graphs present the same identity system
with basepoints displaced by the twists.

## The opposite

Reversing edges exchanges the twists, so the opposite is not the
reflexive-graph opposite of a single graph. VERIFIED (`Cat.Logic.Graph`),
both `refl`:

```agda
op-graph⁺ G : graph⁺ (opⱽ G) ≡ rx.op (graph⁻ G)
op-graph⁻ G : graph⁻ (opⱽ G) ≡ rx.op (graph⁺ G)
```

The involution is the swap of the two graphs composed with `rx.op`. That both
components are fields is what makes it strict — see
[the-package.md](the-package.md).

## The two-sided base

A judgment is contravariant in the term index and covariant in the coterm
index. The base carrying that pair of variances is built from the suite's own
operations:

```agda
base = rx.binary-product (rx.op (graph⁻ G)) (graph⁺ G)
```

VERIFIED (`Cat.Logic.Graph`): `base-rx-is-axiom` is `refl` —

```agda
rx base (x , y) ≡ (var x .snd , covar y .snd)
```

The reflexive edge of the two-sided base **is** the framing, and at a
diagonal vertex it is the axiom rule read as a single edge. Over this base
the judgment family transports in one move, by `bipush`, and what needs the
unbiased lens over the one-sided base needs only a covariant one here — see
[displays.md](displays.md).
