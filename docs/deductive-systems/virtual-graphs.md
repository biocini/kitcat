# Virtual graphs

The carrier is `Cat.Logic.Type`.

## Terms, coterms, arguments

Objects and edges come first, and everything else is built from them.

```agda
term x   = Σ w ∶ ob , hom w x        -- an edge into x, with its source named
coterm y = Σ v ∶ ob , hom y v        -- an edge out of y, with its target named
argument x y = term x × coterm y
conclusion γ = hom (γ .fst .fst) (γ .snd .fst)
judgment x y = (γ : argument x y) → conclusion γ
```

A term at `x` is a proof landing at `x`. A coterm at `y` is a
continuation leaving `y`. An argument pairs one of each, and a
judgment concludes an edge between the two anonymous endpoints for
every argument it receives. Nothing here mentions an identity:
`judgment` is a function of objects and edges alone.

## The embedding

```agda
reflect : hom x y → judgment x y
```

Every proof is a sufficient condition to derive the judgment its
argument denotes. Read as a string, `reflect f (t , k)` is the
ternary composite of `t .snd`, `f` and `k .snd`: the edge, the
argument's two halves, and nothing else. The reading is a gloss,
not a constraint. Models whose `reflect` is not a composite exist
(VERIFIED `Bb.OneTwist.Cancel`, a reflection twisted by a
permutation). They are what keeps the framing's two cancellations
independent.

## Representability

```agda
is-representable = fiber reflect
normal f : is-representable (reflect f)
```

A judgment is representable when some edge reflects to it. `normal`
says every reflected judgment is representable by the obvious
witness. `hom≃total-representable` says an edge is the same thing as
a judgment together with a representation of it.

Representability is the engine. The theory reads composition,
associativity and the coherence tower off contractible fibers of
`reflect`. It never declares them.

## Arity, and what it forbids

From `reflect` alone the formable composites have **odd** arity. A
ternary composite `⟨u , f , p⟩` is one application. Nesting gives
five, seven, and so on. Appending a single factor is impossible: it
would need a coterm at the far end, and the only source of one is a
chosen endo-edge.

Counted exactly, an expression built from `n` applications of
`reflect` has `2n + 1` leaves, so with `k` payload edges it carries
`2n + 1 − k` twists. The parity of the twist count is the parity of
`k + 1`. This governs what can be said at all, and it is why the
framing is not optional. See [framing.md](framing.md).

## The opposite

Reversing edges exchanges the two argument halves, hence the two
twists. Both are fields, so the exchange is a swap.

```agda
opⱽ G .hom x y     = hom G y x
opⱽ G .reflect f γ = reflect G f (γ .snd , γ .fst)
opⱽ G .twist⁺      = twist⁻ G
opⱽ G .twist⁻      = twist⁺ G
```

VERIFIED (`Cat.Logic.Base`): `opⱽ-invol G = refl`, doing it twice
returns the record on the nose. And `op-eval G f = refl`: the
opposite does not move evaluation at the axiom, so a cancellation
looks the same from either end.

Every construction below is one hand's text. The other is its image
under `opⱽ`, and the duality is a checked fact, not an assumption.
