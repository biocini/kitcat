The fundamental quasigroupoid of a magmoid M.

In a magmoid, composition is total: any composable pair `(f, g)`
produces `f ⨾ g`. But this says nothing about how the composite
interacts with its surroundings. `is-neutral (f ⨾ g)` is the
condition that the pair `(f, g)` is *coherently composable* — not
just that a composite exists, but that the composite participates
meaningfully in the algebra through divisibility. This gives a
hierarchy of composability strength:

1. Bare composability: `f ⨾ g` exists (free in any magmoid).
2. Neutral composability: `is-neutral (f ⨾ g)` — the composite
   has full divisibility, producing local units and division
   operations. A property of the pair, not of `f` or `g`
   individually.
3. Coherent composability: `composable f g` — local
   associativity holds at the pair, so the composite interacts
   equationally with surrounding morphisms.
4. Global associativity: all triples associate.

The fundamental quasigroupoid lives at level 2: it selects the
composable pairs whose composites are neutral, redefining
"composable" to mean "the composite meets the local coherence
threshold." This is analogous to how the core of a category
restricts to isomorphisms — but where the core selects individual
morphisms, the fundamental quasigroupoid selects *pairs* whose
interaction has the right divisibility structure.

There are two presentations:

- `_⇢_` (span): a morphism `x ⇢ z` is a pair `(f, g)` through
  an explicit intermediate object whose composite is neutral.
  This directly captures "coherently composable pair."

- `_∻_` (normalized): forgets the intermediate object but carries
  per-morphism associator data (thunkability, linearity, mediality),
  promoting from level 2 to level 3. This is what lets `Fund`
  compose without global assumptions.

Fund is right adjoint to the inclusion of quasigroupoids into
magmoids: any neutrality-preserving functor from a quasigroupoid
Q into M factors through Fund(M).

The symbol `∻` (U+223B, HOMOTHETIC) turns out to be apt. A
classical homothety is a geometric transformation determined by
local data (center point and ratio), composable, always invertible,
and structure-preserving. A `_∻_` morphism in a magmoid is likewise
determined by local coherence data, composable, always invertible
(`∻-sym`), and structure-preserving (full divisibility). The span
presentation `_⇢_` parallels how a homothety factors through its
center point — `mid` plays the role of the geometric center through
which the transformation is witnessed.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Data.Magmoid

module Cat.Magmoid.Quasigroupoid.Base (M : Magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv

import Cat.Data.Base as B
import Cat.Data.Neutral as N
import Cat.Data.Neutral.Eq as Eq
import Cat.Data.Map as Map

open B M
open N M
open Eq M
```

## Witnessed neutral composites

A morphism `x ⇢ z` is a coherently composable pair: two morphisms
`left : hom x mid` and `right : hom mid z` through an explicit
intermediate object, whose composite `left ⨾ right` is neutral.
The neutrality condition is a property of the pair — neither `left`
nor `right` need be neutral individually. What matters is that their
interaction through composition has full divisibility.

```agda
record _⇢_ (x z : ob) : Type (o ⊔ h) where
  no-eta-equality
  constructor wit
  field
    mid    : ob
    left   : hom x mid
    right  : hom mid z
    is-neu : is-neutral (left ⨾ right)

infix 4 _⇢_
open _⇢_ public
```

## From enriched to span

The map `∻→⇢` factors an enriched neutral morphism `f : x ∻ z` into
a span through `z` itself, using the loop `is-neutral.loop fn` as
the right factor. The composite `f ⨾ loop` is neutral because
`loop-unitr` shows it equals `f`, and we transport the neutrality
of `f` along that path. This does not require global associativity.

```agda
∻→⇢ : ∀ {x z} → x ∻ z → x ⇢ z
∻→⇢ (f , fn , ft , fl , fm) = wit _ f loop neu where
  open is-neutral fn

  neu : is-neutral (f ⨾ loop)
  neu = subst is-neutral
    (sym (loop-unitr ft fl fm f)) fn
```

## The fundamental quasigroupoid

Fund uses the normalized presentation `_∻_`: same objects as M,
but morphisms carry neutrality plus the associator data that
promotes from level 2 (neutral composability) to level 3 (coherent
composability). This is what makes `∻-cat` and `∻-sym` available
without assuming level 4.

```agda
Fund : Magmoids
Fund = str ob _∻_ ∻-cat
```

## Projection functor

The projection forgets the associator data, sending each enriched
neutral morphism to its underlying morphism in M.

```agda
open Map Fund M using (functor)

proj : functor
proj .functor.map x = x
proj .functor.hmap e = e .fst
proj .functor.preserves-iso e _ = e .snd .fst
proj .functor.preserves-comp _ _ = refl
```

## Associative case

When M has global associativity, every neutral morphism can be
promoted to an enriched neutral morphism via `≐→∻`. The
round-trip `∻→≐ ∘ ≐→∻` is the identity definitionally.

The map `⇢→∻` collapses a span to its composite, which is neutral
by the `is-neu` field. The retraction `retract` shows that the
round-trip `∻→≐ ∘ ⇢→∻ ∘ ∻→⇢` recovers the original neutral
morphism, with the first component given by `loop-unitr` and
the second by propositionality of `is-neutral`.

```agda
module with-assoc (assoc : associativity) where
  open from-assoc assoc public

  section
    : ∀ {a b} (e : a ≐ b)
    → ∻→≐ (≐→∻ e) ≡ e
  section _ = refl

  ⇢→∻ : ∀ {x z} → x ⇢ z → x ∻ z
  ⇢→∻ s = ≐→∻ (s .left ⨾ s .right , s .is-neu)

  retract
    : ∀ {x z} (e : x ∻ z)
    → ∻→≐ (⇢→∻ (∻→⇢ e)) ≡ ∻→≐ e
  retract (f , fn , ft , fl , fm) i =
    is-neutral.loop-unitr fn ft fl fm f i
    , is-prop→PathP
        (λ i → is-neutral-is-prop
          (is-neutral.loop-unitr fn ft fl fm f i))
        (subst is-neutral
          (sym (is-neutral.loop-unitr fn ft fl fm f)) fn)
        fn i
```
