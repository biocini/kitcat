# The two actions

```agda
act   : ∀ {x y} → hom x y → term x   → term y
coact : ∀ {x y} → hom x y → coterm y → coterm x
```

`term` and `coterm` are families over the objects, and each is the
vertex family of a **displayed reflexive graph over the virtual
graph's underlying reflexive graph**. `act` is the covariant
transport of the first display; `coact` is the contravariant
transport of the second.

Both come from `reflect` by holding one slot of an argument at its
axiom half:

```agda
act   {y = y} f t = intro (reflect f (argue t (covar y)))
coact {x}     f e = elim  (reflect f (argue (var x) e))
```

`reflect` itself has no variance — it consumes both slots at once.
Variance appears only once a slot is fixed, and which variance
appears is not a choice; see *Why the variance is forced* below.

Holding a slot at its axiom half and leaving the *other slot
packaged* gives the edge-valued form, whose value's far endpoint is
read off the argument:

```agda
act-π   : ∀ {x y} → hom x y → (t : term x)   → hom (t .fst) y
coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
```

These are `reflect f` itself, partially applied — `act-π f t` is
`reflect f ⟨ t ∣ covar y ⟩` — so they are more primitive than the
family transports, which are their bundlings:

```agda
act   f t = t .fst , act-π   f t
coact f γ = γ .fst , coact-π f γ
```

which is why each transport preserves the anonymous endpoint by
`refl`: the endpoint is the pair's first component, handed straight
back.

The tiers are stated over the edge-valued form. Its value is an edge
rather than a member of a family, so absorption is a path in a hom
type with no `Σ` whose first component could wander, and a path into
the target costs one `funext` rather than a nested pair. Two
identities hold by `refl` and carry much of what follows:

```agda
eval (reflect e) ≡ coact-π e (covar x)     -- e : hom x x
eval (reflect e) ≡ act-π   e (var x)
```

## The displays

The rest of each display is determined. A displayed edge over
`p : hom x y` says the transport was taken, and displayed
reflexivity is then absorption:

```agda
term-disp   .vtx  x         = term x
term-disp   .edge x y p t t′ = act p t ≡ t′
term-disp   .rx   t          = act (idn x) t ≡ t

coterm-disp .vtx  x         = coterm x
coterm-disp .edge x y p u w  = u ≡ coact p w
coterm-disp .rx   u          = u ≡ coact (idn x) u
```

Being a fibration adds nothing to these: the lift spaces are
singletons, so `rx.is-cov-fibration term-disp` holds outright and its
pushforward is `act` on the nose. VERIFIED in
`Test.SpikeDeductiveSystem` (appendix), by `refl`.

So all the content of these displays sits in `rx` — the absorptions —
which is exactly what the unit tier supplies
([unitality.md](unitality.md)). A display of this kind is the graph
of a function that already exists.

That is worth contrasting with the display composition comes from.
Vertices `hom a z`, displayed edge `reflect w ≡ composite⁻ u p`: not
the graph of anything, so its fibration condition is not free. It is
`is-composable`, and its transport is the composition
([composability.md](composability.md)).

| `D.vtx` | `D.edge` over `p` | fibration | transport |
| --- | --- | --- | --- |
| `term x` | `act p t ≡ t′` | free | `act` |
| `coterm x` | `u ≡ coact p w` | free | `coact` |
| `hom a z` | `reflect w ≡ composite⁻ u p` | `is-composable` | `_⨾⁻ p` |
| `hom x c` | `reflect u ≡ composite⁺ p w` | `is-composable` | `p ⨾⁺_` |

These four are indexed by vertices, and each picks a hand. There is a
fifth, indexed by edges, which is the only one that sees both;
[displays.md](displays.md) is about it.

## Why the variance is forced

A covariant action on coterms over the same graph would be
`hom x y → coterm x → coterm y`. It is not definable. A coterm at `x`
is `(v , b : hom x v)`; landing in `coterm y` needs something out of
`y`, and `reflect f` consumes only a term at `x` paired with a coterm
at `y` — `b` is neither. It would take an inverse of `f`. Terms admit
no contravariant transport over a fixed base for the same reason.

The variance of each family is therefore fixed by which endpoint the
family is indexed at: `term x` collects arrows *into* `x`, so an edge
out of `x` extends them forward; `coterm y` collects arrows *out of*
`y`, so an edge into `y` extends them backward.

One can make `coact` covariant by moving the base — it is covariant
over the opposite virtual graph — but then the two displays sit over
different graphs, and since an argument pairs a term at `x` with a
coterm at `y`, one drawn from each, the pairing becomes heterogeneous
and any statement mentioning both needs an op-transport before it can
be stated.

The same move made on `judgment` rather than on either slot succeeds,
because a judgment consumes both slots and can absorb an edge at each.
Over `rx.binary-product (rx.op graph) graph` the family transports
covariantly in one step, so mixed variance is a property of the
display and not of `judgment`; [mediation.md](mediation.md) works out
what that base makes visible.

## The mixed variance is what makes the composites typecheck

Each hand keeps one factor reflected as the head; the argument is
stated at the outer endpoints and must be brought to the head's
boundary. Which end has to travel determines which action is used.

```
  x ──f──▸ y ──g──▸ z         argument at the outer endpoints:
                                        term x × coterm z

  ⁻  head f : hom x y   needs   term x × coterm y
                        the term is already there;
                        the coterm travels z ⇝ y  ──  coact g

  ⁺  head g : hom y z   needs   term y × coterm z
                        the coterm is already there;
                        the term travels x ⇝ y   ──  act f
```

```agda
composite⁻ f g γ = reflect f (argue (γ .fst) (coact g (γ .snd)))
composite⁺ f g γ = reflect g (argue (act f (γ .fst)) (γ .snd))
```

So the two hands are not an arbitrary pair. A *hand* is named for the
slot the second factor enters — `⁻` for the coterm slot, `⁺` for the
term slot — and which action it consumes is forced by which factor it
keeps as head.

## Judgments have the variance of homs

Because `judgment x y` is a function type out of `term x × coterm y`,
the domain's variances invert: `term x` covariant in `x` makes
`judgment` contravariant in `x`, and `coterm y` contravariant in `y`
makes it covariant in `y`. That is the variance profile of `hom`
itself.

This is what lets `reflect : hom x y → judgment x y` be a map between
two families of the same shape, and hence what lets the tiers be
fibers of it. Two covariant actions would not have this property.

A family covariant in one index and contravariant in another is the
situation Sterling introduces *unbiased dependent lenses* for — his
stated motivation is characterising identity types of structures with
mixed variance (`resources/sterling-reflexive-graph-lenses`;
SOURCE-CHECKED), and `Cat.Graph.Refl.Classify`'s magma case study
makes the same point, its homomorphism edge being mixed-variance and
coming from neither biased lens. Displaying `judgment` itself, rather
than its two slots separately, is that formalism, and the two
injections it asks for are `inj⁻` and `inj⁺` —
[displays.md](displays.md).

## The involution

The two actions exchange on the nose: what the opposite virtual graph
calls acting on a term is what the base calls coacting on a coterm,
and conversely (VERIFIED, `Test.SpikeRxDict`). The composites
exchange with them, against the swap of the argument pair.

## Names

`push` and `pull` are reserved for the reflexive-graph suite's
transport vocabulary, where they name the pushforward and pullback of
*any* displayed family — which in this theory includes the
compositions, since those are the transports of the slice and coslice
displays. `act` and `coact` name the two actions by the slot they
consume, a fact about the sequent structure rather than about a
choice of base.

Where `push` and `pull` do appear — `rx.cov-fibration.push`,
`rx.ctrv-fibration.pull`, and the lemmas `push-is-comp` and
`pull-is-comp` identifying them with the compositions — they are the
reflexive-graph suite's own names, used in its own sense.
