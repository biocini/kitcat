# Virtual graphs

The carrier of the whole theory is a reflexive graph together with
one further datum saying how an edge acts on the arrows around it.

```agda
record virtual-graph o h : Type₊ (o ⊔ h) where
  field
    ob  : Type o
    hom : ob → ob → Type h
    idn : (x : ob) → hom x x
```

`Cat.Logic.Type` is the module; the names below are all its own.

## Terms and coterms

Fix an object. The arrows *into* it and the arrows *out of* it are
both worth naming, together with their anonymous far endpoints.

```agda
term   : ob → Type (o ⊔ h)
term   x = Σ w ∶ ob , hom w x

coterm : ob → Type (o ⊔ h)
coterm y = Σ v ∶ ob , hom y v
```

In the reflexive-graph vocabulary these are the **cofan** and the
**fan** of the object, and the two distinguished elements built from
reflexivity are their centers:

```agda
var   : (a : ob) → term a     ;  var a   = a , idn a
covar : (y : ob) → coterm y   ;  covar y = y , idn y
```

VERIFIED in `Test.SpikeRxDict`: `term x ≡ rx.cofan graph x`,
`coterm y ≡ rx.fan graph y`, `var x ≡ rx.cofan-center graph x`,
`covar y ≡ rx.fan-center graph y` — all by `refl`, where `graph` is
the underlying reflexive graph `(ob, hom, idn)`.

The proof-theoretic reading is the one the names carry: a term at `x`
is something proved, with a source; a coterm at `y` is a continuation,
with a target. They are the two sides of a turnstile.

## Arguments and judgments

An argument pairs one of each, and its *conclusion* is the edge type
spanning the two anonymous endpoints:

```agda
argument   : ob → ob → Type (o ⊔ h)
argument x y = term x × coterm y

conclusion : ∀ {x y} → argument x y → Type h
conclusion γ = hom (γ .fst .fst) (γ .snd .fst)
```

```
    w ──a──▸ x                y ──b──▸ v
    └─── term x ───┘          └── coterm y ──┘

                  ⟨ a ∣ b ⟩ : argument x y

    conclusion:   w ──────────────────────▸ v
```

A **judgment** from `x` to `y` is a rule producing a conclusion for
every argument — an arrow from `x` to `y` in continuation-passing
form, abstracted over what surrounds it:

```agda
judgment : ob → ob → Type (o ⊔ h)
judgment x y = (γ : argument x y) → conclusion γ
```

The remaining field of a virtual graph says every edge denotes such a
rule:

```agda
field
  reflect : ∀ {x y} → hom x y → judgment x y
```

Reading `reflect` as soundness: an edge is sufficient to derive the
judgment it denotes. Nothing yet says it is *complete* — that the
rules arising this way are only the ones an edge gives — and the
tiers are what make that precise, fiber by fiber.

## Evaluation and representability

Applying a judgment at the two axiom halves evaluates it, and the
fibers of `reflect` are the representability data:

```agda
eval : ∀ {x y} → judgment x y → hom x y
eval {x} {y} α = α (var x , covar y)

is-representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
is-representable = fiber reflect

normal : ∀ {x y} (f : hom x y) → is-representable (reflect f)
normal f = f , refl
```

One fact needs no axioms at all: an edge is the same thing as a
judgment together with a proof that it is representable.

```agda
hom≃total-representable
  : ∀ {x y} → hom x y ≃ (Σ α ∶ judgment x y , is-representable α)
```

That equivalence is in `Cat.Logic.Type`, and it is the reason the
tiers can be stated as contractibility of fibers of `reflect` without
any of them presupposing the others.

## Duality

Reversing the edges and reading `reflect` against the swapped
argument gives the opposite virtual graph:

```agda
opⱽ G .virtual-graph.ob          = ob
opⱽ G .virtual-graph.hom x y     = hom y x
opⱽ G .virtual-graph.idn         = idn
opⱽ G .virtual-graph.reflect f γ = reflect f (γ .snd , γ .fst)
```

This is an involution on the nose — `opⱽ (opⱽ G) ≡ G` by `refl`
(VERIFIED, `Test.SpikeRxDict`) — and it exchanges the two
families definitionally, since `term` at the opposite *is* `coterm`:

```agda
rx.fan   (rx.op graph) x ≡ term   x
rx.cofan (rx.op graph) y ≡ coterm y
```

`reflect` itself is symmetric: it is a fixed point of the involution,
consuming both slots at once. What the involution moves is which slot
one holds fixed — and that is the subject of [actions.md](actions.md).

A caution about the direction of travel. Judgments do *not* have
definitionally equal types across the involution: `judgment x z` at
the opposite has domain `coterm x × term z` where the base has
`term z × coterm x`. Elements exchange by conversion, statements
travel along the swap by one `ap`. Both hands' definitions are
therefore written out rather than one being defined as the other's
opposite; only theorems are transported.
