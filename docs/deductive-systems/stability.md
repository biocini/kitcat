# Stability

The last tier is normalisation: reading back the evaluation of a
reflected edge returns that edge.

```agda
readback : Type (o ⊔ h)
readback = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f
```

Bare, this cannot be a tier. Two readback families differ by a loop
at every edge, so the type is a torsor over loop families rather than
a proposition. What makes it one is a coherence, and where the
coherence can be found is the content of this document.

## The flank

At the identity there is a second route to the same endpoints. Since
`eval (reflect e)` is definitionally `coact-π e x (idn x)`, the
projected unit's absorption instantiated at `idn` says
`eval (reflect (unit⁻ x)) ≡ idn x`, while readback at that same unit
says `eval (reflect (unit⁻ x)) ≡ unit⁻ x`. Composing them identifies
the projected unit with the chosen edge, and transporting the
absorption along that identification lands a canonical path at `idn`:

```agda
flank⁻-of : ∀ x → eval (reflect (unit⁻ x)) ≡ unit⁻ x
          → eval (reflect (idn x)) ≡ idn x
flank⁻-of x p =
  ap (λ e → coact-π e (covar x)) (sym (sym p ∙ unit⁻-absorb x (covar x)))
  ∙ unit⁻-absorb x (covar x)
```

Each flank canonical reads exactly one value of the family — the
family's path at that hand's projected unit — which is why it is
stated as a function of that value.

## The coherence and the tier

`absorb-coh` asks the readback family to agree with both flank
canonicals at the identity:

```agda
absorb-coh u =
  ∀ x → (u (idn x) ≡ flank⁻-of x (u (unit⁻ x)))
      × (u (idn x) ≡ flank⁺-of x (u (unit⁺ x)))

is-stable : Type (o ⊔ h)
is-stable = is-contr (Σ {A = readback} absorb-coh)
```

Asking it on both hands makes the two flank canonicals agree with
each other, which is the one cross-hand fact the theory asserts —
`flanks-agree`, a projection. Everywhere else the hands are
independent.

```agda
is-stable-is-prop : ∀ U → is-prop (is-stable U)
is-stable-is-prop U = is-contr-is-prop _
```

## Why the fiber is not decoration

Dropping the `is-contr` wrapper — asking the pair `(readback,
absorb-coh)` to be propositional by itself, in the manner of a
half-adjoint equivalence — does not work, and the reason is internal
to the coherence rather than a want of a better proof.

Every value `absorb-coh` reads lies at an **endomorphism**: `idn x`,
`unit⁻ x`, `unit⁺ x`. So a twist — a loop at every edge, composed
onto the family pointwise — that vanishes on endomorphisms leaves
every value the coherence reads untouched, and carries an inhabitant
to another inhabitant:

```agda
coh-twist u c x .fst =
  agree u x (idn x) ∙ c x .fst
  ∙ sym (ap (flank⁻-of x) (agree u x (unit⁻ x)))
```

Propositionality of the bare pair would therefore force every such
twist to be trivial:

```agda
half-adjoint-forces-truncation
  : is-prop half-adjoint → (S : half-adjoint)
  → (t : twist) (te : ∀ x (e : hom x x) → t e ≡ refl)
  → ∀ {x y} (f : hom x y) → t f ≡ refl
```

which is a truncation condition on the hom types. VERIFIED in
`Test.SpikeUnitCanonical`.

## What stability buys

With the tier in hand the readback family and the coherence are
projections, and the chosen edge is certified:

```agda
unit⁻-is-idn x = sym (unit (unit⁻ x)) ∙ unit⁻-absorb x (covar x)
units-agree  x = unit⁻-is-idn x ∙ sym (unit⁺-is-idn x)
idn-absorb⁻ x v b =
  ap (λ e → coact-π e γ) (sym (unit⁻-is-idn x)) ∙ unit⁻-absorb x γ
```

So both hands' projected units are the graph's own reflexive edge,
they agree with each other, and `idn` inherits both absorptions.
Composability is never consumed: this all sits at the unit and
stability tiers.

Uniqueness against the chosen edge needs no unit tier at all —
readback alone makes any edge acting as the identity equal to `idn`:

```agda
unit⁻-canonical x e abs = sym (unit e) ∙ abs (covar x)
```

## The two routes agree

There are now two ways from a candidate unit to `idn`: through the
projected unit, or directly. They are the same path.

Both are one dependent function on the unit fiber — send a candidate
to its readback point composed with its absorption read at the axiom:

```agda
route⁻ : ∀ x (c : fiber (coact-π {x} {x}) snd) → c .fst ≡ idn x
route⁻ x c = sym (unit (c .fst)) ∙ (λ i → c .snd i x (idn x))
```

`unit⁻-is-idn` is this at the fiber's center and `unit⁻-canonical` is
it at the candidate, both definitionally. Being a function of the
fiber element it is natural in paths between them, which path
induction gives, and the detour then cancels:

```agda
unique-agrees⁻
  : ∀ x (e : hom x x) (abs : ∀ v (b : hom x v) → coact-π e γ ≡ γ .snd)
  → unit⁻-unique-pt x e abs ∙ unit⁻-is-idn x ≡ unit⁻-canonical x e abs
```

VERIFIED in `Cat.Logic.Base`, with the `⁺` mate. No
further coherence is involved: the two sides were already the same
function, which is exactly what the half-adjoint attempt above did
*not* have.

## What is left open

Propositionality of the tier is settled; inhabitation is not. Whether
the stability fiber is contractible in a given regime is per-instance
content, and the certificates for path-presented and truncated
regimes are not part of this theory.
