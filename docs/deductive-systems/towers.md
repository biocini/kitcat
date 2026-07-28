# The two towers

Everything here is in `Cat.Logic.Base`'s `tower`, over a stability
and the two composabilities.

## The compositions

```agda
f ⨾⁺ g = C⁺ f g .fst          reflect-⨾⁺ f g : reflect (f ⨾⁺ g) ≡ composite⁺ f g
f ⨾⁻ g = C⁻ f g .fst          reflect-⨾⁻ f g : reflect (f ⨾⁻ g) ≡ composite⁻ f g
```

Each is the representative of its own cut, well defined because
representation is unique. The junction's twist is inside the
composition, not applied to it: `⨾⁺` composes through a pending read
and `⨾⁻` through a pending write, and the two differ by two
windings.

## Distributivity and associativity

The coaction distributes over the positive composition and the
action over the negative: each representation witness read at the
axiom half its own hand closes, `var` for the positive and `covar`
for the negative:

```agda
coact-⨾⁺ f g k : coact (f ⨾⁺ g) k ≡ coact f (coact g k)
act-⨾⁻   f g t : act   (f ⨾⁻ g) t ≡ act g (act f t)
```

VERIFIED: `assoc⁺` and `assoc⁻`, both. `assoc⁺` is the projection of
a path in a fiber of `reflect` (the module `tri⁺` names that fiber,
its two bracketings and the path between them), which is what makes
the coherence above it available.

## Mixed words

A word whose two junctions take different hands is well formed, and
the order of its junctions decides its law. Negative then positive is
a theorem: both bracketings represent one judgment, in which the
leading edge acts, the trailing edge coacts, and the middle edge
stays reflected, so stability identifies them.

```agda
mixed-assoc f g h : (f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)
```

Positive then negative shares no judgment between its bracketings:
one closes a junction inside `act`, the other inside `coact`. Whether
such a triple associates is a property, with one universal closure at
each end of the word:

```agda
associates f g h : (f ⨾⁺ g) ⨾⁻ h ≡ f ⨾⁺ (g ⨾⁻ h)
thunkable  f     : ∀ g h → associates f g h
linear     h     : ∀ f g → associates f g h
```

VERIFIED: `mixed-assoc` (the module `mixed` names the common
judgment, the two representatives and the path between them). Nothing
above inhabits `thunkable` or `linear`. A mediation does, since it
makes the two junctions one operation and both bracketings instances
of `assoc⁺`.

The homs are untruncated, so an inhabitant of `associates` is an
associator cell. A proof of `thunkable f` is then a choice of
associators, one per word. Nothing above coheres such choices.
Whether the higher notion is this bare closure or a fiber-shaped
refinement in the style of the tiers is an open line of the theory.

## One unit law per hand

Where the cancellation is the identity (the twists mutually inverse,
the framing itself still free), each hand gains exactly **one** unit
law: the positive a right unit, the negative a left one, each at the
twist of its own sign.

```agda
unitr⁺ f : f ⨾⁺ twist⁺ y ≡ f
unitl⁻ g : twist⁻ x ⨾⁻ g ≡ g
pair⁻ x  : twist⁻ x ⨾⁻ twist⁺ x ≡ twist⁺ x
pair⁺ x  : twist⁻ x ⨾⁺ twist⁺ x ≡ twist⁻ x
```

The pairing crosses, as the tiers predict: the composite of the two
twists in one hand is the *other* hand's unit. The law each hand
lacks is the one a mediation supplies (see
[mediation.md](mediation.md)), so its absence is the theory working
as defined.

## The pentagon

The five bracketings of a four-fold positive cut are five points of
one fiber of `reflect`. Stability makes that fiber a proposition,
hence a set, so any two paths between two of its points agree:

```agda
identity     : pth b₁ b₄ ∙ pth b₄ b₅ ≡ pth b₁ b₂ ∙ (pth b₂ b₃ ∙ pth b₃ b₅)
hom-identity : α₁₄ ∙ α₄₅ ≡ α₁₂ ∙ (α₂₃ ∙ α₃₅)
```

Each classical edge lifts back into that fiber, and the fiber being
a proposition identifies the lift with the canonical path. The two
whiskered edges lift by carrying the triple's own fiber path along.
The three plain ones append the fourth factor's rewriting instead,
so each carries a reassociation, one distributes a wrapping, and one
has two appended steps that commute rather than reassociate. That
last square is the head's own witness read at a moving coterm. Every
correction holds the first component fixed, so none touches the
projection.

VERIFIED: `face₁₂`, `face₂₃`, `face₃₅`, `face₁₄`, `face₄₅`, and

```agda
pentagon : assoc⁺ (f ⨾⁺ g) h k ∙ assoc⁺ f g (h ⨾⁺ k)
         ≡ ap (_⨾⁺ k) (assoc⁺ f g h)
         ∙ (assoc⁺ f (g ⨾⁺ h) k ∙ ap (f ⨾⁺_) (assoc⁺ g h k))
```

No truncation anywhere. The fiber is a proposition because
representation is unique, and that is the whole of the coherence.
The negative tower is the image of this one under the opposite.
