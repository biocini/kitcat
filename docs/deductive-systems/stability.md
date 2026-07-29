# Stability

Representation is unique where it occurs.

```agda
is-stable = ∀ {x y} (α : judgment x y) → is-prop (is-representable α)
```

## Why it lives here and nowhere else

The statement names no twist and touches no argument half. By the
count of [framing.md](framing.md) it is winding-neutral in the
strongest sense (the framing does not appear in it at all), so the
framing cannot move it. It says something about `reflect` and
nothing about the graph's framing or its units.

VERIFIED (`Cat.Logic.Base`):

- `is-stable-is-prop`: a proposition, because being a proposition is
  one. No h-level hypothesis.
- `reflect-lc : is-stable → reflect m ≡ reflect n → m ≡ n`, the
  cancellation every derived composition runs on.
- `contr-from-stable`: an inhabited fiber of `reflect` is
  contractible.

Stability is not a field of the record. Each cut arrives with a
contractible representability fiber, and the negative composite at
the twist is a reflection, so that contractibility transports to
every image fiber of `reflect`. VERIFIED (`Cat.Logic.Base`):
`composite⁻-twist`, then `contr-cut⁻.stable-from-contr-cut⁻` through
`image-fibers-contr→is-embedding`, and `axioms→stable` for the
package. See [the-package.md](the-package.md).

## It is an embedding condition

Propositional fibers is what an embedding is, so the tier is
`reflect` being one at every pair of objects. VERIFIED
(`Cat.Logic.Base`): `stable-is-embedding` is `refl`.

Where the edges form sets so do the judgments, and an embedding into
a set is an injection. The tier then reduces to injectivity of
**transmission**, the edge surrounded by one twist of each sign, the
winding-neutral form of [framing.md](framing.md):

```agda
stable-from-hom-sets
  : (∀ {x y} → is-set (hom x y))
  → (∀ {x y} {m n : hom x y} → eval (reflect m) ≡ eval (reflect n) → m ≡ n)
  → is-stable
```

VERIFIED (`Cat.Logic.Base`). So in the truncated regime the tier is
not an extra hypothesis about representation but a statement about
the framing: whether surrounding an edge by the two twists loses
information.

## Crossing the opposite

Stability crosses, though not on the nose. The opposite reindexes a
judgment along the exchange of the two argument halves, and
reindexing along a bijection is an equivalence on fibers.

VERIFIED (`Cat.Logic.Base`):
`op-stable G : is-stable G → is-stable (opⱽ G)`.

## What it does not assert

Stability does not say that any judgment *is* representable. It says
representations, where they exist, are unique. Existence is
[composability.md](composability.md)'s business, and the split is
what lets that tier be pure existence.
