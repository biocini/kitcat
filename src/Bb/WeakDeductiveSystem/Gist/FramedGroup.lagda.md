A framed deductive system whose fans are not propositional: an abelian
group read as a one-object virtual graph, framed by an arbitrary pair of
its elements.

Every tier holds at every such pair, so the framing is free here as well
— but now outside the path-object regime, where a fan is the whole
group. Two of the fragment's boundaries become arithmetic: the
cancellation is that the two framing elements sum to the unit, and
agreement of the two cuts is that they are equal. Their difference is
what the two cuts differ by.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.WeakDeductiveSystem.Gist.FramedGroup where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Path.Base
open import Core.Equiv.Base using (_≃_; iso→equiv)
open import Core.HLevel.Base using (Π-is-hlevel; is-prop-equiv)
open import Core.Function.Embedding using (injective→is-embedding)
open import Core.Transport.Properties using (prop-inhabited→is-contr)

open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base

open import Bb.WeakDeductiveSystem.Type
open import Bb.WeakDeductiveSystem.Base
open import Bb.WeakDeductiveSystem.Graph
```

## The carrier

One object, and the group as its endo-edges.

```agda
record One : Type 0ℓ where
  constructor ⋆

module group {u} {A : Type u}
  (_·_ : A → A → A) (e : A) (ι : A → A)
  (A-set : is-set A)
  (assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
  (comm  : ∀ a b → a · b ≡ b · a)
  (unitl : ∀ a → e · a ≡ a)
  (invl  : ∀ a → ι a · a ≡ e)
  where

  unitr : ∀ a → a · e ≡ a
  unitr a = comm a e ∙ unitl a

  invr : ∀ a → a · ι a ≡ e
  invr a = comm a (ι a) ∙ invl a

  cancel-l : ∀ a {b c} → a · b ≡ a · c → b ≡ c
  cancel-l a {b} {c} p =
    sym (unitl b)
    ∙ ap (_· b) (sym (invl a))
    ∙ assoc (ι a) a b
    ∙ ap (ι a ·_) p
    ∙ sym (assoc (ι a) a c)
    ∙ ap (_· c) (invl a)
    ∙ unitl c

  cancel-r : ∀ a {b c} → b · a ≡ c · a → b ≡ c
  cancel-r a {b} {c} p = cancel-l a (comm a b ∙ p ∙ comm c a)
```

The framing is a pair of elements, unconstrained.

```agda
  module framing (t⁺ t⁻ : A) where

    VG : virtual-graph 0ℓ u
    VG .virtual-graph.ob            = One
    VG .virtual-graph.hom _ _       = A
    VG .virtual-graph.reflect f γ   = γ .fst .snd · (f · γ .snd .snd)
    VG .virtual-graph.twist⁺ _      = t⁺
    VG .virtual-graph.twist⁻ _      = t⁻

    open virtual-graph VG
    open sequents VG
```

## The fans are the group

A fan is the group paired with the one object, so the graph is a path
object only when the group itself is a proposition.

```agda
    univalent→prop : rx.is-univalent (graph⁺ VG) → is-prop A
    univalent→prop univ = is-prop-equiv fan≃carrier (univ ⋆)
      where
      fan≃carrier : A ≃ rx.fan (graph⁺ VG) ⋆
      fan≃carrier = iso→equiv (λ a → ⋆ , a) (λ z → z .snd) (λ _ → refl) (λ _ → refl)
```

## Stability

Transmission surrounds an edge with one twist of each sign, and
cancelling them is injective, so the edges being a set is the whole of
the tier.

```agda
    transmit-injective : ∀ {m n : A} → t⁻ · (m · t⁺) ≡ t⁻ · (n · t⁺) → m ≡ n
    transmit-injective p = cancel-r t⁺ (cancel-l t⁻ p)

    stable : is-stable VG
    stable = stable-from-hom-sets VG (λ {_} {_} → A-set) transmit-injective
```

## Both cuts

Each composite judgment is a five-fold product with the twist of its own
sign at the junction, and reassociating gathers the middle three into
one edge.

```agda
    cut⁻ : A → A → A
    cut⁻ f k = f · (t⁻ · k)

    cut⁺ : A → A → A
    cut⁺ f k = (f · t⁺) · k

    composable⁻ : is-composable⁺ VG
    composable⁻ f k = cut⁻ f k , funext λ γ →
      ap (γ .fst .snd ·_) (assoc f (t⁻ · k) (γ .snd .snd)
                           ∙ ap (f ·_) (assoc t⁻ k (γ .snd .snd)))

    composable⁺ : is-composable⁻ VG
    composable⁺ f k = cut⁺ f k , funext λ γ →
      ap (γ .fst .snd ·_) (assoc (f · t⁺) k (γ .snd .snd))
      ∙ sym (assoc (γ .fst .snd) (f · t⁺) (k · (γ .snd .snd)))
```

## Both unit tiers

An action map holds the half it does not act on at that half's axiom, so
it multiplies by that half's twist: `coact-π` by the future's `t⁻`,
`act-π` by the buffer's `t⁺`. The edge acting as the second projection
is therefore that twist's inverse. Injectivity makes the fiber a
proposition, and the inverse inhabits it.

```agda
    coact-π-injective : ∀ {m n : A} → coact-π {⋆} {⋆} m ≡ coact-π {⋆} {⋆} n → m ≡ n
    coact-π-injective p = cancel-r e (cancel-l t⁻ (happly p (⋆ , e)))

    act-π-injective : ∀ {m n : A} → act-π {⋆} {⋆} m ≡ act-π {⋆} {⋆} n → m ≡ n
    act-π-injective p = cancel-r t⁺ (cancel-l e (happly p (⋆ , e)))

    unital⁻ : is-invertible⁻ VG
    unital⁻ x = prop-inhabited→is-contr
      (injective→is-embedding (Π-is-hlevel 2 λ _ → A-set)
        (coact-π {⋆} {⋆}) coact-π-injective snd)
      ( (ι t⁻)
      , funext λ γ → sym (assoc t⁻ (ι t⁻) (γ .snd))
                   ∙ ap (_· γ .snd) (invr t⁻)
                   ∙ unitl (γ .snd) )

    unital⁺ : is-invertible⁺ VG
    unital⁺ x = prop-inhabited→is-contr
      (injective→is-embedding (Π-is-hlevel 2 λ _ → A-set)
        (act-π {⋆} {⋆}) act-π-injective snd)
      ( (ι t⁺)
      , funext λ t → ap (t .snd ·_) (invl t⁺) ∙ unitr (t .snd) )
```

A hand's cell reads the opposite half's twist through the opposite
half's action, and each twist acting on its own family lands exactly
there — both sides multiplication by `t⁻ · t⁺`.

```agda
    pin⁻ : ∀ x → coact-π (twist⁺ x) ≡ cell⁻ VG x
    pin⁻ _ = funext λ γ →
      sym (assoc t⁻ t⁺ (γ .snd)) ∙ comm (t⁻ · t⁺) (γ .snd)

    pin⁺ : ∀ x → act-π (twist⁻ x) ≡ cell⁺ VG x
    pin⁺ _ = funext λ t → comm (t .snd) (t⁻ · t⁺) ∙ assoc t⁻ t⁺ (t .snd)
```

## The package

```agda
    deductive : is-deductive-system VG
    deductive .is-deductive-system.stable = stable
    deductive .is-deductive-system.composable .is-composable.contr⁺ = composable⁻
    deductive .is-deductive-system.composable .is-composable.contr⁻ = composable⁺
    deductive .is-deductive-system.invertible .is-invertible.fiber⁻ = unital⁻
    deductive .is-deductive-system.invertible .is-invertible.fiber⁺ = unital⁺

    system : deductive-system 0ℓ u
    system .deductive-system.graph  = VG
    system .deductive-system.axioms = deductive

    open tower stable composable⁻ composable⁺
```

## The two boundaries, as arithmetic

The cancellation is that the two framing elements compose to the unit.

```agda
    cancels→ : t⁻ · t⁺ ≡ e → ∀ x → cell⁻ VG x ≡ snd
    cancels→ K _ = funext λ γ → ap (γ .snd ·_) K ∙ unitr (γ .snd)

    →cancels : (∀ x → cell⁻ VG x ≡ snd) → t⁻ · t⁺ ≡ e
    →cancels K = sym (unitl (t⁻ · t⁺)) ∙ happly (K ⋆) (⋆ , e)
```

Agreement of the two cuts is that the two framing elements are equal:
the cuts are the same product with the junction's twist differing by
sign, so their difference is the framing's.

```agda
    cuts-agree→ : t⁻ ≡ t⁺
                → ∀ {x y z} (f : hom x y) (k : hom y z)
                → composite⁺ VG f k ≡ composite⁻ VG f k
    cuts-agree→ T f k = funext λ γ →
      let a = γ .fst .snd ; b = γ .snd .snd in
        ap (λ s → a · (f · (s · (k · b)))) T
        ∙ ap (a ·_) (sym (assoc f t⁺ (k · b)))
        ∙ sym (assoc a (f · t⁺) (k · b))

    →cuts-agree : (∀ {x y z} (f : hom x y) (k : hom y z)
                   → composite⁺ VG f k ≡ composite⁻ VG f k)
                → t⁻ ≡ t⁺
    →cuts-agree X = sym red⁻ ∙ happly (X e e) ((⋆ , e) , (⋆ , e)) ∙ red⁺
      where
      red⁻ : e · (e · (t⁻ · (e · e))) ≡ t⁻
      red⁻ = unitl _ ∙ unitl _ ∙ ap (t⁻ ·_) (unitl e) ∙ unitr t⁻

      red⁺ : (e · (e · t⁺)) · (e · e) ≡ t⁺
      red⁺ = ap (_· (e · e)) (unitl _ ∙ unitl t⁺)
           ∙ ap (t⁺ ·_) (unitl e) ∙ unitr t⁺
```

So a framing whose two elements differ gives a deductive system on wild
fans whose two cuts are genuinely distinct, and one whose elements are
mutually inverse gives the cancelling case. Both together force each
element to be its own inverse.

```agda
    both→ : t⁻ · t⁺ ≡ e → t⁻ ≡ t⁺ → t⁺ · t⁺ ≡ e
    both→ K T = ap (_· t⁺) (sym T) ∙ K
```

## What each hand's unit actually is

Each cut carries a junction twist, so the coterm hand's composition is
the product twisted by `t⁻` and its unit is that element's inverse.

```agda
    unit⁻-is-inverse : (u : A) → (∀ {x y} (f : hom x y) → f ⨾⁺ u ≡ f)
                     → t⁻ · u ≡ e
    unit⁻-is-inverse u U = sym (unitl (t⁻ · u)) ∙ U e

    unit⁺-is-inverse : (u : A) → (∀ {x y} (f : hom x y) → u ⨾⁻ f ≡ f)
                     → u · t⁺ ≡ e
    unit⁺-is-inverse u U = sym (unitr (u · t⁺)) ∙ U e
```

The composite of the two twists therefore carries three, and demanding
it be the unit is a cubic condition on the framing rather than the
cancellation.

```agda
    ι⁻ : A
    ι⁻ = t⁻ ⨾⁺ t⁺

    ι⁻-unit→cubic : (∀ {x y} (f : hom x y) → f ⨾⁺ ι⁻ ≡ f)
                  → t⁻ · (t⁻ · (t⁻ · t⁺)) ≡ e
    ι⁻-unit→cubic U = sym (unitl _) ∙ U e

    ι⁺ : A
    ι⁺ = t⁻ ⨾⁻ t⁺

    ι⁺-unit→cubic : (∀ {x y} (f : hom x y) → ι⁺ ⨾⁻ f ≡ f)
                  → (((t⁻ · t⁺) · t⁺) · t⁺) ≡ e
    ι⁺-unit→cubic U = sym (unitr _) ∙ U e
```

Read across the hands instead, the count comes out even: one hand's
composite of the two twists carries the *other* hand's junction, and is
that hand's unit exactly under the cancellation.

```agda
    ι⁻-unit⁺→square : (∀ {x y} (f : hom x y) → ι⁻ ⨾⁻ f ≡ f)
                    → (t⁻ · (t⁻ · t⁺)) · t⁺ ≡ e
    ι⁻-unit⁺→square U = sym (unitr _) ∙ U e

    cancels→ι⁻-unit⁺ : t⁻ · t⁺ ≡ e → ∀ {x y} (f : hom x y) → ι⁻ ⨾⁻ f ≡ f
    cancels→ι⁻-unit⁺ K f =
      ap (λ s → (s · t⁺) · f) (ap (t⁻ ·_) K ∙ unitr t⁻)
      ∙ ap (_· f) K
      ∙ unitl f
```

## The tier's centre against the framing

An edge whose coterm action is the projection is the held twist's
inverse — the centre `unital⁻` supplies — and under the cancellation
that inverse is the other twist again, so unit and framing coincide
exactly there.

```agda
    absorber⁻-is-inverse : (u : A) → (∀ γ → coact-π {⋆} {⋆} u γ ≡ γ .snd)
                         → t⁻ · u ≡ e
    absorber⁻-is-inverse u P = sym (ap (t⁻ ·_) (unitr u)) ∙ P (⋆ , e)

    absorber⁻-is-twist⁺ : t⁻ · t⁺ ≡ e
                        → (u : A) → (∀ γ → coact-π {⋆} {⋆} u γ ≡ γ .snd) → u ≡ t⁺
    absorber⁻-is-twist⁺ K u P = cancel-l t⁻ (absorber⁻-is-inverse u P ∙ sym K)
```

## What does untwist it

The twist enters because a cut fills one argument slot with an axiom
half. A two-payload string fills no slot — the factors sit adjacent —
and it is represented by the plain product.

```agda
    string : A → A → argument ⋆ ⋆ → A
    string f g γ = γ .fst .snd · (f · (g · γ .snd .snd))

    string-rep : (f g : A) → string f g ≡ reflect (f · g)
    string-rep f g = funext λ γ →
      ap (γ .fst .snd ·_) (sym (assoc f g (γ .snd .snd)))

    cut⁻-is-twisted : (f g : A) → cut⁻ f g ≡ f · (t⁻ · g)
    cut⁻-is-twisted _ _ = refl

    cut⁺-is-twisted : (f g : A) → cut⁺ f g ≡ (f · t⁺) · g
    cut⁺-is-twisted _ _ = refl
```

Against the plain product the composite of the two twists is the
cancellation itself, with no residue.

```agda
    string-twists : string t⁻ t⁺ ≡ reflect (t⁻ · t⁺)
    string-twists = string-rep t⁻ t⁺
```

## A candidate filler, and what it costs

Filling the junction with a candidate rather than with an axiom half.
The candidate is self-consistent when composing the two twists through
it returns it — and that condition is the cancellation, with no residue.

```agda
    cut[_] : A → A → A → A
    cut[ c ] f g = f · (c · g)

    self-consistent : A → Type u
    self-consistent c = cut[ c ] t⁻ t⁺ ≡ c

    self-consistent→cancels : (c : A) → self-consistent c → t⁻ · t⁺ ≡ e
    self-consistent→cancels c p = cancel-r c
      ( assoc t⁻ t⁺ c
      ∙ ap (t⁻ ·_) (comm t⁺ c)
      ∙ p
      ∙ sym (unitl c) )

    cancels→self-consistent : t⁻ · t⁺ ≡ e → (c : A) → self-consistent c
    cancels→self-consistent K c =
      ap (t⁻ ·_) (comm c t⁺)
      ∙ sym (assoc t⁻ t⁺ c)
      ∙ ap (_· c) K
      ∙ unitl c
```
