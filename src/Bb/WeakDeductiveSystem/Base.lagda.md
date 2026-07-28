A deductive system is a virtual graph whose framing behaves: each twist
has a uniquely determined one-sided inverse, representation is unique
where it occurs, and both cuts are representable. All of it is property;
the framing is the only structure.

That the two inverses are the twists themselves — the twists mutually
inverse — is not asserted here. It is the balanced layer's condition,
carried as hypotheses by `absorption`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.WeakDeductiveSystem.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Path.Base using (ap-comp)
open import Core.Transport.Properties
  using (is-prop→is-set; is-prop-is-prop; is-contr-is-prop; prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; is-prop-equiv; Π-is-hlevel)
open import Core.Function.Embedding using (is-embedding; injective→is-embedding)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Equiv.Base using (iso→equiv)

open import Bb.WeakDeductiveSystem.Type
```

## The opposite

Reversing edges exchanges the two argument halves, hence the two
twists — both fields, so the exchange is a swap and doing it twice
returns the record on the nose. Evaluation at the axiom is unmoved: a
cancellation looks the same from either end.

```agda
opⱽ : ∀ {o h} → virtual-graph o h → virtual-graph o h
opⱽ G .virtual-graph.ob        = virtual-graph.ob G
opⱽ G .virtual-graph.hom x y   = virtual-graph.hom G y x
opⱽ G .virtual-graph.reflect f γ = virtual-graph.reflect G f (γ .snd , γ .fst)
opⱽ G .virtual-graph.twist⁺    = virtual-graph.twist⁻ G
opⱽ G .virtual-graph.twist⁻    = virtual-graph.twist⁺ G

opⱽ-invol : ∀ {o h} (G : virtual-graph o h) → opⱽ (opⱽ G) ≡ G
opⱽ-invol G = refl

op-eval : ∀ {o h} (G : virtual-graph o h) {x y} (f : virtual-graph.hom G y x)
        → sequents.eval (opⱽ G) (virtual-graph.reflect (opⱽ G) f)
        ≡ sequents.eval G (virtual-graph.reflect G f)
op-eval G f = refl
```

## One cancellation

Each side's cell carries one twist of each sign: the coterm-side cell is
the negative twist read through `act-π`, which holds the positive one,
and the term-side cell is the mirror. So a pending read meets a pending
write, the cancellation performed and never named as an edge of its own.

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G

  cell⁻ : (x : ob) (γ : coterm x) → hom x (γ .fst)
  cell⁻ x γ = act-π (twist⁻ (γ .fst)) (x , γ .snd)

  cell⁺ : (x : ob) (t : term x) → hom (t .fst) x
  cell⁺ x t = coact-π (twist⁺ (t .fst)) (x , t .snd)
```

Each side's tier sits elsewhere: the fiber of that side's action map
over the second projection, asked to be contractible. Its centre is the
uniquely determined edge acting as the identity on that family. Since
`coact-π` holds `var`, the negative centre is what cancels the negative
twist, and the positive centre cancels the positive one — so the tier is
invertibility of the framing, one side each. No twist enters the demand,
and nothing here says a centre is the other twist.

```agda
  is-invertible⁻ : Type (o ⊔ h)
  is-invertible⁻ = ∀ x → is-contr (fiber (coact-π {x} {x}) snd)

  is-invertible⁺ : Type (o ⊔ h)
  is-invertible⁺ = ∀ x → is-contr (fiber (act-π {x} {x}) snd)

  is-invertible⁻-is-prop : is-prop is-invertible⁻
  is-invertible⁻-is-prop = Π-is-prop λ _ → is-contr-is-prop _

  is-invertible⁺-is-prop : is-prop is-invertible⁺
  is-invertible⁺-is-prop = Π-is-prop λ _ → is-contr-is-prop _

  record is-invertible : Type (o ⊔ h) where
    field
      fiber⁻ : is-invertible⁻
      fiber⁺ : is-invertible⁺

  is-invertible-is-prop : is-prop is-invertible
  is-invertible-is-prop U U' i .is-invertible.fiber⁻ =
    is-invertible⁻-is-prop (is-invertible.fiber⁻ U) (is-invertible.fiber⁻ U') i
  is-invertible-is-prop U U' i .is-invertible.fiber⁺ =
    is-invertible⁺-is-prop (is-invertible.fiber⁺ U) (is-invertible.fiber⁺ U') i
```

Pinning each twist to its side's cell and trivialising that cell is two
hypotheses per side, and together they say each centre is the twist
filling the other slot — the twists mutually inverse. That absorption
consumes no tier: neither representation's uniqueness nor either cut's
existence appears in it, and a deductive system does not assert it.

```agda
  module absorption
    (pin⁻ : ∀ x → coact-π (twist⁺ x) ≡ cell⁻ x)
    (pin⁺ : ∀ x → act-π   (twist⁻ x) ≡ cell⁺ x)
    (K⁻ : ∀ x → cell⁻ x ≡ snd) (K⁺ : ∀ x → cell⁺ x ≡ snd) where

    absorb⁻ : ∀ {y} (k : coterm y) → coact (twist⁺ y) k ≡ k
    absorb⁻ {y} k i = k .fst , (pin⁻ y ∙ K⁻ y) i k

    absorb⁺ : ∀ {x} (t : term x) → act (twist⁻ x) t ≡ t
    absorb⁺ {x} t i = t .fst , (pin⁺ x ∙ K⁺ x) i t
```

## Stability

Representation is unique where it occurs. The statement names no twist
and touches no argument half, so it is winding-neutral: a condition on
`reflect` alone, unmoved by the framing.

```agda
  is-stable : Type (o ⊔ h)
  is-stable = ∀ {x y} (α : judgment x y) → is-prop (is-representable α)

  is-stable-is-prop : is-prop is-stable
  is-stable-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → is-prop-is-prop _

  reflect-lc : is-stable → ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-lc S {n = n} p = ap fst (S (reflect n) (_ , p) (normal n))

  contr-from-stable
    : is-stable → ∀ {x y} (α : judgment x y)
    → is-representable α → is-contr (is-representable α)
  contr-from-stable S α = prop-inhabited→is-contr (S α)
```

Propositional fibers is what an embedding is, so stability is `reflect`
being one at every pair of objects. Where the edges form sets the
judgments do too, and an embedding is then an injection: the tier
reduces to injectivity of transmission — evaluation of a reflection,
the edge surrounded by one twist of each sign.

```agda
  stable-is-embedding : is-stable ≡ (∀ {x y} → is-embedding (reflect {x} {y}))
  stable-is-embedding = refl

  stable-from-hom-sets
    : (∀ {x y} → is-set (hom x y))
    → (∀ {x y} {m n : hom x y} → eval (reflect m) ≡ eval (reflect n) → m ≡ n)
    → is-stable
  stable-from-hom-sets hset inj α =
    injective→is-embedding (Π-is-hlevel 2 λ _ → hset) reflect (λ p → inj (ap eval p)) α
```

## The two cuts

A positive cut absorbs its second factor into the coterm and keeps the
first reflected; a negative cut absorbs its first into the term and
keeps the second. Each absorption closes the opposite argument half at
its axiom — the positive through `coact`, which holds `var` and so
carries the negative twist, the negative through `act`, which holds
`covar` and carries the positive one. So the positive cut goes through
a pending read and the negative through a pending write. Their windings
are opposite, and identifying them would be the coherence this fragment
forgets.

```agda
  inj⁺ : ∀ {x y z} → judgment x y → hom y z → judgment x z
  inj⁺ α p γ = α (γ .fst , coact p (γ .snd))

  inj⁻ : ∀ {x y z} → hom x y → judgment y z → judgment x z
  inj⁻ p β γ = β (act p (γ .fst) , γ .snd)

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g = inj⁺ (reflect f) g

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g = inj⁻ f (reflect g)

  is-composable⁺ : Type (o ⊔ h)
  is-composable⁺ = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → is-representable (composite⁺ f g)

  is-composable⁻ : Type (o ⊔ h)
  is-composable⁻ = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → is-representable (composite⁻ f g)
```

Existence only: uniqueness sits in stability and is not restated here,
so each composability tier is a proposition exactly once stability is in
hand.

```agda
  is-composable⁺-is-prop : is-stable → is-prop is-composable⁺
  is-composable⁺-is-prop S =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → S _

  is-composable⁻-is-prop : is-stable → is-prop is-composable⁻
  is-composable⁻-is-prop S =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → S _
```

Composability is stated over a stability: neither cut's existence is a
proposition on its own, and it is the stability the record is indexed by
that makes it one.

```agda
  record is-composable (S : is-stable) : Type (o ⊔ h) where
    field
      contr⁺ : is-composable⁺
      contr⁻ : is-composable⁻

  is-composable-is-prop : (S : is-stable) → is-prop (is-composable S)
  is-composable-is-prop S C C' i .is-composable.contr⁺ =
    is-composable⁺-is-prop S (is-composable.contr⁺ C) (is-composable.contr⁺ C') i
  is-composable-is-prop S C C' i .is-composable.contr⁻ =
    is-composable⁻-is-prop S (is-composable.contr⁻ C) (is-composable.contr⁻ C') i
```

## Deductive systems

```agda
  record is-deductive-system : Type (o ⊔ h) where
    field
      stable     : is-stable
      composable : is-composable stable
      invertible : is-invertible

  is-deductive-system-is-prop : is-prop is-deductive-system
  is-deductive-system-is-prop D D' i .is-deductive-system.stable =
    is-stable-is-prop (is-deductive-system.stable D)
                      (is-deductive-system.stable D') i
  is-deductive-system-is-prop D D' i .is-deductive-system.composable =
    is-prop→PathP
      (λ j → is-composable-is-prop
               (is-stable-is-prop (is-deductive-system.stable D)
                                  (is-deductive-system.stable D') j))
      (is-deductive-system.composable D) (is-deductive-system.composable D') i
  is-deductive-system-is-prop D D' i .is-deductive-system.invertible =
    is-invertible-is-prop (is-deductive-system.invertible D)
                      (is-deductive-system.invertible D') i
```

## Duality

The opposite exchanges the argument halves and the twists, hence the two
action maps, hence the invertibility tiers — on the nose. Stability
crosses by reindexing a judgment along that exchange, which is an
equivalence on fibers.

```agda
op-invertible⁻ : ∀ {o h} (G : virtual-graph o h) → is-invertible⁻ (opⱽ G) ≡ is-invertible⁺ G
op-invertible⁻ G = refl

op-invertible⁺ : ∀ {o h} (G : virtual-graph o h) → is-invertible⁺ (opⱽ G) ≡ is-invertible⁻ G
op-invertible⁺ G = refl

op-invertible : ∀ {o h} (G : virtual-graph o h) → is-invertible G → is-invertible (opⱽ G)
op-invertible G U .is-invertible.fiber⁻ = is-invertible.fiber⁺ U
op-invertible G U .is-invertible.fiber⁺ = is-invertible.fiber⁻ U

op-stable : ∀ {o h} (G : virtual-graph o h) → is-stable G → is-stable (opⱽ G)
op-stable G S α =
  is-prop-equiv
    (iso→equiv (λ w → w .fst , λ i δ → w .snd i (δ .snd , δ .fst))
               (λ w → w .fst , λ i γ → w .snd i (γ .snd , γ .fst))
               (λ _ → refl) (λ _ → refl))
    (S (λ δ → α (δ .snd , δ .fst)))
```

Each cut crosses to the other: the opposite's positive composite is the
negative composite of the same pair, in the other order, read backwards
— so a representative transports by exchanging the argument halves.

```agda
op-composable : ∀ {o h} (G : virtual-graph o h) (S : is-stable G)
              → is-composable G S → is-composable (opⱽ G) (op-stable G S)
op-composable G S C .is-composable.contr⁺ f g =
    is-composable.contr⁻ C g f .fst
  , λ i γ → is-composable.contr⁻ C g f .snd i (γ .snd , γ .fst)
op-composable G S C .is-composable.contr⁻ f g =
    is-composable.contr⁺ C g f .fst
  , λ i γ → is-composable.contr⁺ C g f .snd i (γ .snd , γ .fst)

op-axioms : ∀ {o h} (G : virtual-graph o h)
          → is-deductive-system G → is-deductive-system (opⱽ G)
op-axioms G D .is-deductive-system.stable =
  op-stable G (is-deductive-system.stable D)
op-axioms G D .is-deductive-system.composable =
  op-composable G _ (is-deductive-system.composable D)
op-axioms G D .is-deductive-system.invertible =
  op-invertible G (is-deductive-system.invertible D)
```

## The package

Structure and property, one field each.

```agda
record deductive-system o h : Type₊ (o ⊔ h) where
  field
    graph  : virtual-graph o h
    axioms : is-deductive-system graph

opᴰ : ∀ {o h} → deductive-system o h → deductive-system o h
opᴰ D .deductive-system.graph  = opⱽ (deductive-system.graph D)
opᴰ D .deductive-system.axioms = op-axioms _ (deductive-system.axioms D)
```

The carrier returns on the nose, and the axioms are a proposition, so
the opposite is an involution on the whole package.

```agda
opᴰ-invol : ∀ {o h} (D : deductive-system o h) → opᴰ (opᴰ D) ≡ D
opᴰ-invol D i .deductive-system.graph = deductive-system.graph D
opᴰ-invol D i .deductive-system.axioms =
  is-deductive-system-is-prop _
    (deductive-system.axioms (opᴰ (opᴰ D)))
    (deductive-system.axioms D) i
```

## The two towers

Each hand's composition is the representative of its own cut; stability
makes it well defined without composability restating uniqueness. The
coaction distributes over the positive composition and the action over
the negative — each witness read at the axiom half its own hand closes,
`var` for the positive and `covar` for the negative — and associativity
follows from a fiber path.

```agda
module tower {o h} {G : virtual-graph o h}
  (S : is-stable G) (C⁺ : is-composable⁺ G) (C⁻ : is-composable⁻ G) where
  open virtual-graph G
  open sequents G

  lc : ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  lc = reflect-lc G S

  _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁺ g = C⁺ f g .fst

  _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁻ g = C⁻ f g .fst

  reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁺ g) ≡ composite⁺ G f g
  reflect-⨾⁺ f g = C⁺ f g .snd

  reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁻ g) ≡ composite⁻ G f g
  reflect-⨾⁻ f g = C⁻ f g .snd

  coact-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z) (k : coterm z)
           → coact (f ⨾⁺ g) k ≡ coact f (coact g k)
  coact-⨾⁺ f g k i = k .fst , reflect-⨾⁺ f g i (var _ , k)

  act-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z) (t : term x)
         → act (f ⨾⁻ g) t ≡ act g (act f t)
  act-⨾⁻ f g t i = t .fst , reflect-⨾⁻ f g i (t , covar _)

  module tri⁺ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z) where
    E : judgment w z
    E γ = reflect f (γ .fst , coact g (coact h (γ .snd)))

    a₁ a₂ : is-representable E
    a₁ = (f ⨾⁺ g) ⨾⁺ h
       , reflect-⨾⁺ (f ⨾⁺ g) h
       ∙ (λ i γ → reflect-⨾⁺ f g i (γ .fst , coact h (γ .snd)))
    a₂ = f ⨾⁺ (g ⨾⁺ h)
       , reflect-⨾⁺ f (g ⨾⁺ h)
       ∙ (λ i γ → reflect f (γ .fst , coact-⨾⁺ g h (γ .snd) i))

    σ : a₁ ≡ a₂
    σ = S E a₁ a₂

  assoc⁺ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
         → (f ⨾⁺ g) ⨾⁺ h ≡ f ⨾⁺ (g ⨾⁺ h)
  assoc⁺ f g h = ap fst (tri⁺.σ f g h)

  assoc⁻ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
         → (f ⨾⁻ g) ⨾⁻ h ≡ f ⨾⁻ (g ⨾⁻ h)
  assoc⁻ f g h = lc
    ( reflect-⨾⁻ (f ⨾⁻ g) h
    ∙ (λ i γ → reflect h (act-⨾⁻ f g (γ .fst) i , γ .snd))
    ∙ sym ( reflect-⨾⁻ f (g ⨾⁻ h)
          ∙ (λ i γ → reflect-⨾⁻ g h i (act f (γ .fst) , γ .snd)) ) )
```

## Mixed words

A three-factor word whose two junctions take different hands is well
formed, and the order of its junctions decides its law. Where they run
negative then positive, the two bracketings represent one judgment —
the leading edge acting on the term half, the trailing edge coacting
on the coterm half, the middle edge reflected — so stability
identifies them and the word is a theorem.

```agda
  module mixed {w x y z} (f : hom w x) (g : hom x y) (k : hom y z) where
    E : judgment w z
    E γ = reflect g (act f (γ .fst) , coact k (γ .snd))

    a₁ a₂ : is-representable E
    a₁ = (f ⨾⁻ g) ⨾⁺ k
       , reflect-⨾⁺ (f ⨾⁻ g) k
       ∙ (λ i γ → reflect-⨾⁻ f g i (γ .fst , coact k (γ .snd)))
    a₂ = f ⨾⁻ (g ⨾⁺ k)
       , reflect-⨾⁻ f (g ⨾⁺ k)
       ∙ (λ i γ → reflect-⨾⁺ g k i (act f (γ .fst) , γ .snd))

    σ : a₁ ≡ a₂
    σ = S E a₁ a₂

  mixed-assoc : ∀ {w x y z} (f : hom w x) (g : hom x y) (k : hom y z)
              → (f ⨾⁻ g) ⨾⁺ k ≡ f ⨾⁻ (g ⨾⁺ k)
  mixed-assoc f g k = ap fst (mixed.σ f g k)
```

Where the junctions run positive then negative, the bracketings share
no judgment: one closes its first junction inside `act`, the other its
second inside `coact`. Whether such a triple associates is a property
of the triple, and its two universal closures — at the edge that leads
the word, and at the edge that trails it — are thunkability and
linearity.

```agda
  associates : ∀ {w x y z} → hom w x → hom x y → hom y z → Type h
  associates f g h = (f ⨾⁺ g) ⨾⁻ h ≡ f ⨾⁺ (g ⨾⁻ h)

  thunkable : ∀ {w x} → hom w x → Type (o ⊔ h)
  thunkable {x = x} f = ∀ {y z} (g : hom x y) (h : hom y z) → associates f g h

  linear : ∀ {y z} → hom y z → Type (o ⊔ h)
  linear {y = y} h = ∀ {w x} (f : hom w x) (g : hom x y) → associates f g h
```

## The unit laws

Where the cancellation is the identity — the twists mutually inverse,
the framing itself still free — each hand gains exactly one unit law:
the positive a right unit at `twist⁺`, the negative a left unit at
`twist⁻`. The edge each gains is the *other* hand's composite of the
pair. The missing law per hand is the one the forgotten coherence would
supply.

```agda
  module unital
    (pin⁻ : ∀ x → coact-π (twist⁺ x) ≡ cell⁻ G x)
    (pin⁺ : ∀ x → act-π   (twist⁻ x) ≡ cell⁺ G x)
    (K⁻ : ∀ x → cell⁻ G x ≡ snd) (K⁺ : ∀ x → cell⁺ G x ≡ snd) where

    open absorption G pin⁻ pin⁺ K⁻ K⁺ public

    unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ twist⁺ y ≡ f
    unitr⁺ f = lc
      ( reflect-⨾⁺ f (twist⁺ _)
      ∙ (λ i γ → reflect f (γ .fst , absorb⁻ (γ .snd) i)) )

    unitl⁻ : ∀ {x y} (g : hom x y) → twist⁻ x ⨾⁻ g ≡ g
    unitl⁻ g = lc
      ( reflect-⨾⁻ (twist⁻ _) g
      ∙ (λ i γ → reflect g (absorb⁺ (γ .fst) i , γ .snd)) )

    pair⁻ : ∀ x → twist⁻ x ⨾⁻ twist⁺ x ≡ twist⁺ x
    pair⁻ x = unitl⁻ (twist⁺ x)

    pair⁺ : ∀ x → twist⁻ x ⨾⁺ twist⁺ x ≡ twist⁻ x
    pair⁺ x = unitr⁺ (twist⁻ x)
```

A hand's crossed pairing meets that hand's *other* unit law at the
composite of the two twists, so either missing law identifies the
framing. The collapse is one equation about the framing; whether it in
turn forces the two cuts to agree is not settled here.

```agda
    collapse⁺ : (∀ {x y} (g : hom x y) → twist⁻ x ⨾⁺ g ≡ g)
              → ∀ x → twist⁻ x ≡ twist⁺ x
    collapse⁺ L x = sym (pair⁺ x) ∙ L (twist⁺ x)

    collapse⁻ : (∀ {x y} (f : hom x y) → f ⨾⁻ twist⁺ y ≡ f)
              → ∀ x → twist⁻ x ≡ twist⁺ x
    collapse⁻ R x = sym (R (twist⁻ x)) ∙ pair⁻ x
```

## The pentagon

The five bracketings of a four-fold positive cut are five points of
one fiber of `reflect`. Stability makes that fiber a proposition, hence
a set, so any two paths between two of its points agree. Each classical
edge lifts back into the fiber — the triple's own fiber path, whiskered
or with the fourth factor's rewriting appended — and the fiber being a
proposition identifies the lift with the canonical path.

```agda
  module pentagon⁺ {w x y z v}
    (f : hom w x) (g : hom x y) (h : hom y z) (k : hom z v) where

    E : judgment w v
    E γ = reflect f (γ .fst , coact g (coact h (coact k (γ .snd))))

    b₁ b₂ b₃ b₄ b₅ : is-representable E
    b₁ = ((f ⨾⁺ g) ⨾⁺ h) ⨾⁺ k
       , reflect-⨾⁺ ((f ⨾⁺ g) ⨾⁺ h) k
       ∙ (λ i γ → reflect-⨾⁺ (f ⨾⁺ g) h i (γ .fst , coact k (γ .snd)))
       ∙ (λ i γ → reflect-⨾⁺ f g i (γ .fst , coact h (coact k (γ .snd))))
    b₂ = (f ⨾⁺ (g ⨾⁺ h)) ⨾⁺ k
       , reflect-⨾⁺ (f ⨾⁺ (g ⨾⁺ h)) k
       ∙ (λ i γ → reflect-⨾⁺ f (g ⨾⁺ h) i (γ .fst , coact k (γ .snd)))
       ∙ (λ i γ → reflect f (γ .fst , coact-⨾⁺ g h (coact k (γ .snd)) i))
    b₃ = f ⨾⁺ ((g ⨾⁺ h) ⨾⁺ k)
       , reflect-⨾⁺ f ((g ⨾⁺ h) ⨾⁺ k)
       ∙ (λ j γ → reflect f
           (γ .fst , (γ .snd .fst , tri⁺.a₁ g h k .snd j (var _ , γ .snd))))
    b₄ = (f ⨾⁺ g) ⨾⁺ (h ⨾⁺ k)
       , reflect-⨾⁺ (f ⨾⁺ g) (h ⨾⁺ k)
       ∙ (λ i γ → reflect-⨾⁺ f g i (γ .fst , coact (h ⨾⁺ k) (γ .snd)))
       ∙ (λ i γ → reflect f (γ .fst , coact g (coact-⨾⁺ h k (γ .snd) i)))
    b₅ = f ⨾⁺ (g ⨾⁺ (h ⨾⁺ k))
       , reflect-⨾⁺ f (g ⨾⁺ (h ⨾⁺ k))
       ∙ (λ j γ → reflect f
           (γ .fst , (γ .snd .fst , tri⁺.a₂ g h k .snd j (var _ , γ .snd))))

    pth : (a b : is-representable E) → a ≡ b
    pth = S E

    identity : pth b₁ b₄ ∙ pth b₄ b₅ ≡ pth b₁ b₂ ∙ (pth b₂ b₃ ∙ pth b₃ b₅)
    identity = is-prop→is-set (S E) b₁ b₅ _ _

    α₁₂ = ap fst (pth b₁ b₂)
    α₂₃ = ap fst (pth b₂ b₃)
    α₃₅ = ap fst (pth b₃ b₅)
    α₁₄ = ap fst (pth b₁ b₄)
    α₄₅ = ap fst (pth b₄ b₅)

    hom-identity : α₁₄ ∙ α₄₅ ≡ α₁₂ ∙ (α₂₃ ∙ α₃₅)
    hom-identity =
      sym (ap-comp fst (pth b₁ b₄) (pth b₄ b₅))
      ∙ ap (ap fst) identity
      ∙ ap-comp fst (pth b₁ b₂) (pth b₂ b₃ ∙ pth b₃ b₅)
      ∙ ap (α₁₂ ∙_) (ap-comp fst (pth b₂ b₃) (pth b₃ b₅))

    γ₁₂ : b₁ ≡ b₂
    γ₁₂ i = tri⁺.σ f g h i .fst ⨾⁺ k
          , reflect-⨾⁺ (tri⁺.σ f g h i .fst) k
          ∙ (λ j γ → tri⁺.σ f g h i .snd j (γ .fst , coact k (γ .snd)))

    face₁₂ : α₁₂ ≡ ap (_⨾⁺ k) (assoc⁺ f g h)
    face₁₂ = ap (ap fst) (is-prop→is-set (S E) b₁ b₂ (pth b₁ b₂) γ₁₂)

    γ₃₅ : b₃ ≡ b₅
    γ₃₅ i = f ⨾⁺ tri⁺.σ g h k i .fst
          , reflect-⨾⁺ f (tri⁺.σ g h k i .fst)
          ∙ (λ j γ → reflect f
              (γ .fst , (γ .snd .fst , tri⁺.σ g h k i .snd j (var _ , γ .snd))))

    face₃₅ : α₃₅ ≡ ap (f ⨾⁺_) (assoc⁺ g h k)
    face₃₅ = ap (ap fst) (is-prop→is-set (S E) b₃ b₅ (pth b₃ b₅) γ₃₅)

    wrap : judgment x v → judgment w v
    wrap α γ = reflect f (γ .fst , (γ .snd .fst , α (var _ , γ .snd)))

    γ₂₃-pt : (i : I) → is-representable E
    γ₂₃-pt i = tri⁺.σ f (g ⨾⁺ h) k i .fst
             , tri⁺.σ f (g ⨾⁺ h) k i .snd
             ∙ (λ j γ → reflect f (γ .fst , coact-⨾⁺ g h (coact k (γ .snd)) j))

    l₂₃ : γ₂₃-pt i0 ≡ γ₂₃-pt i1
    l₂₃ i = γ₂₃-pt i

    c₂₃⁰ : b₂ ≡ γ₂₃-pt i0
    c₂₃⁰ i = b₂ .fst
           , Path.assoc (reflect-⨾⁺ (f ⨾⁺ (g ⨾⁺ h)) k)
               (λ j γ → reflect-⨾⁺ f (g ⨾⁺ h) j (γ .fst , coact k (γ .snd)))
               (λ j γ → reflect f (γ .fst , coact-⨾⁺ g h (coact k (γ .snd)) j)) i

    c₂₃¹ : γ₂₃-pt i1 ≡ b₃
    c₂₃¹ i = b₃ .fst
           , ( sym (Path.assoc (reflect-⨾⁺ f ((g ⨾⁺ h) ⨾⁺ k))
                 (λ j γ → reflect f (γ .fst , coact-⨾⁺ (g ⨾⁺ h) k (γ .snd) j))
                 (λ j γ → reflect f (γ .fst , coact-⨾⁺ g h (coact k (γ .snd)) j)))
             ∙ ap (reflect-⨾⁺ f ((g ⨾⁺ h) ⨾⁺ k) ∙_)
                 (sym (ap-comp wrap (reflect-⨾⁺ (g ⨾⁺ h) k)
                         (λ j δ → reflect-⨾⁺ g h j (δ .fst , coact k (δ .snd)))))
             ) i

    γ₂₃ : b₂ ≡ b₃
    γ₂₃ = c₂₃⁰ ∙ (l₂₃ ∙ c₂₃¹)

    face₂₃ : α₂₃ ≡ assoc⁺ f (g ⨾⁺ h) k
    face₂₃ =
      ap (ap fst) (is-prop→is-set (S E) b₂ b₃ (pth b₂ b₃) γ₂₃)
      ∙ ap-comp fst c₂₃⁰ (l₂₃ ∙ c₂₃¹)
      ∙ ap (refl ∙_) (ap-comp fst l₂₃ c₂₃¹ ∙ Path.unitr (assoc⁺ f (g ⨾⁺ h) k))
      ∙ Path.unitl (assoc⁺ f (g ⨾⁺ h) k)

    γ₄₅-pt : (i : I) → is-representable E
    γ₄₅-pt i = tri⁺.σ f g (h ⨾⁺ k) i .fst
             , tri⁺.σ f g (h ⨾⁺ k) i .snd
             ∙ (λ j γ → reflect f (γ .fst , coact g (coact-⨾⁺ h k (γ .snd) j)))

    l₄₅ : γ₄₅-pt i0 ≡ γ₄₅-pt i1
    l₄₅ i = γ₄₅-pt i

    c₄₅⁰ : b₄ ≡ γ₄₅-pt i0
    c₄₅⁰ i = b₄ .fst
           , Path.assoc (reflect-⨾⁺ (f ⨾⁺ g) (h ⨾⁺ k))
               (λ j γ → reflect-⨾⁺ f g j (γ .fst , coact (h ⨾⁺ k) (γ .snd)))
               (λ j γ → reflect f (γ .fst , coact g (coact-⨾⁺ h k (γ .snd) j))) i

    c₄₅¹ : γ₄₅-pt i1 ≡ b₅
    c₄₅¹ i = b₅ .fst
           , ( sym (Path.assoc (reflect-⨾⁺ f (g ⨾⁺ (h ⨾⁺ k)))
                 (λ j γ → reflect f (γ .fst , coact-⨾⁺ g (h ⨾⁺ k) (γ .snd) j))
                 (λ j γ → reflect f (γ .fst , coact g (coact-⨾⁺ h k (γ .snd) j))))
             ∙ ap (reflect-⨾⁺ f (g ⨾⁺ (h ⨾⁺ k)) ∙_)
                 (sym (ap-comp wrap (reflect-⨾⁺ g (h ⨾⁺ k))
                         (λ j δ → reflect g (δ .fst , coact-⨾⁺ h k (δ .snd) j))))
             ) i

    γ₄₅ : b₄ ≡ b₅
    γ₄₅ = c₄₅⁰ ∙ (l₄₅ ∙ c₄₅¹)

    face₄₅ : α₄₅ ≡ assoc⁺ f g (h ⨾⁺ k)
    face₄₅ =
      ap (ap fst) (is-prop→is-set (S E) b₄ b₅ (pth b₄ b₅) γ₄₅)
      ∙ ap-comp fst c₄₅⁰ (l₄₅ ∙ c₄₅¹)
      ∙ ap (refl ∙_) (ap-comp fst l₄₅ c₄₅¹ ∙ Path.unitr (assoc⁺ f g (h ⨾⁺ k)))
      ∙ Path.unitl (assoc⁺ f g (h ⨾⁺ k))
```

The last edge is the one where two appended steps commute rather than
reassociate: the fourth factor's rewriting and the head's cross, and
their square is the head's own witness read at a moving coterm.

```agda
    exch : (i j : I) → judgment w v
    exch i j γ = reflect-⨾⁺ f g i (γ .fst , coact-⨾⁺ h k (γ .snd) j)

    γ₁₄-pt : (i : I) → is-representable E
    γ₁₄-pt i = tri⁺.σ (f ⨾⁺ g) h k i .fst
             , tri⁺.σ (f ⨾⁺ g) h k i .snd
             ∙ (λ j γ → reflect-⨾⁺ f g j (γ .fst , coact h (coact k (γ .snd))))

    l₁₄ : γ₁₄-pt i0 ≡ γ₁₄-pt i1
    l₁₄ i = γ₁₄-pt i

    c₁₄⁰ : b₁ ≡ γ₁₄-pt i0
    c₁₄⁰ i = b₁ .fst
           , Path.assoc (reflect-⨾⁺ ((f ⨾⁺ g) ⨾⁺ h) k)
               (λ j γ → reflect-⨾⁺ (f ⨾⁺ g) h j (γ .fst , coact k (γ .snd)))
               (λ j γ → reflect-⨾⁺ f g j (γ .fst , coact h (coact k (γ .snd)))) i

    c₁₄¹ : γ₁₄-pt i1 ≡ b₄
    c₁₄¹ i = b₄ .fst
           , ( sym (Path.assoc (reflect-⨾⁺ (f ⨾⁺ g) (h ⨾⁺ k))
                 (λ j → exch i0 j)
                 (λ j γ → reflect-⨾⁺ f g j (γ .fst , coact h (coact k (γ .snd)))))
             ∙ ap (reflect-⨾⁺ (f ⨾⁺ g) (h ⨾⁺ k) ∙_)
                 (Path.commutes (λ j → exch i0 j) (λ j → exch j i1)
                                (λ j → exch j i0) (λ j → exch i1 j)
                                (λ i j → exch i j))
             ) i

    γ₁₄ : b₁ ≡ b₄
    γ₁₄ = c₁₄⁰ ∙ (l₁₄ ∙ c₁₄¹)

    face₁₄ : α₁₄ ≡ assoc⁺ (f ⨾⁺ g) h k
    face₁₄ =
      ap (ap fst) (is-prop→is-set (S E) b₁ b₄ (pth b₁ b₄) γ₁₄)
      ∙ ap-comp fst c₁₄⁰ (l₁₄ ∙ c₁₄¹)
      ∙ ap (refl ∙_) (ap-comp fst l₁₄ c₁₄¹ ∙ Path.unitr (assoc⁺ (f ⨾⁺ g) h k))
      ∙ Path.unitl (assoc⁺ (f ⨾⁺ g) h k)

    pentagon : assoc⁺ (f ⨾⁺ g) h k ∙ assoc⁺ f g (h ⨾⁺ k)
             ≡ ap (_⨾⁺ k) (assoc⁺ f g h)
             ∙ (assoc⁺ f (g ⨾⁺ h) k ∙ ap (f ⨾⁺_) (assoc⁺ g h k))
    pentagon =
      sym (ap (α₁₄ ∙_) face₄₅ ∙ ap (_∙ assoc⁺ f g (h ⨾⁺ k)) face₁₄)
      ∙ hom-identity
      ∙ ap (_∙ (α₂₃ ∙ α₃₅)) face₁₂
      ∙ ap (ap (_⨾⁺ k) (assoc⁺ f g h) ∙_)
          (ap (_∙ α₃₅) face₂₃ ∙ ap (assoc⁺ f (g ⨾⁺ h) k ∙_) face₃₅)
```
