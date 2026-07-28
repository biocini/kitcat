Spike: the associativity profile at position (D′) strength —
readback, contractible cuts, both invertibility tiers, stability
a theorem.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeBalancedProfile where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Bool using (Bool; true; false; module Bool)
open import Core.Data.Sum.Type using (_⊎_; inl; inr)
open import Core.Data.Sum.Properties using (⊎-is-hlevel)
open import Core.Data.Empty
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties
  using (prop-inhabited→is-contr; is-prop→is-set)
open import Core.HLevel.Base using (Π-is-hlevel; ×-is-hlevel)
open import Core.Function.Embedding using (injective→is-embedding)

open import Cat.Logic.Type
open import Cat.Logic.Base

open import Test.SpikeBalancedBase
```

At this strength each tier's centre reads back as the other
twist: the centre's family, evaluated at the axiom coterm or
term, is the centre's own readback. So both cancellations are
theorems, each hand is two-sided unital with its own twist as
unit, and `associates` holds wherever the units can reach — the
word with both trailing edges at the twists.

```agda
module profile {o h} (B : bgraph o h) where
  open bgraph B
  open virtual-graph graph
  open sequents graph

  module at-strength
    (cc⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable (composite⁺ graph f g)))
    (cc⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable (composite⁻ graph f g)))
    (T⁻ : is-invertible⁻ graph)
    (T⁺ : is-invertible⁺ graph)
    where

    open rehearsal.cuts B (λ f g → cc⁺ f g .center) (λ f g → cc⁻ f g .center)

    centre⁻-twist⁺ : ∀ x → T⁻ x .center .fst ≡ twist⁺ x
    centre⁻-twist⁺ x =
        sym (readback (T⁻ x .center .fst))
      ∙ happly (T⁻ x .center .snd) (x , twist⁺ x)

    centre⁺-twist⁻ : ∀ x → T⁺ x .center .fst ≡ twist⁻ x
    centre⁺-twist⁻ x =
        sym (readback (T⁺ x .center .fst))
      ∙ happly (T⁺ x .center .snd) (x , twist⁻ x)

    cancel⁻ : ∀ x → coact-π (twist⁺ x) ≡ snd
    cancel⁻ x =
      subst (λ e → coact-π e ≡ snd) (centre⁻-twist⁺ x) (T⁻ x .center .snd)

    cancel⁺ : ∀ x → act-π (twist⁻ x) ≡ snd
    cancel⁺ x =
      subst (λ e → act-π e ≡ snd) (centre⁺-twist⁻ x) (T⁺ x .center .snd)

    unitl⁺ : ∀ {w x} (s : hom w x) → twist⁺ w ⨾⁺ s ≡ s
    unitl⁺ {w} {x} s =
      sym (⨾⁺-is-coact (twist⁺ w) s) ∙ happly (cancel⁻ w) (x , s)

    unitr⁻ : ∀ {x v} (k : hom x v) → k ⨾⁻ twist⁻ v ≡ k
    unitr⁻ {x} {v} k =
      sym (⨾⁻-is-act k (twist⁻ v)) ∙ happly (cancel⁺ v) (x , k)

    S : is-stable graph
    S = stable-from-contr-cut⁻ cc⁻

    open tower {G = graph} S
      (λ f g → cc⁺ f g .center) (λ f g → cc⁻ f g .center)
      using (associates)

    associates-at-twists : ∀ {x y} (f : hom x y)
                         → associates f (twist⁺ y) (twist⁻ y)
    associates-at-twists {x} {y} f =
        ap (_⨾⁻ twist⁻ y) (unitr⁺ f)
      ∙ unitr⁻ f
      ∙ sym (ap (f ⨾⁺_) (unitr⁻ (twist⁺ y)) ∙ unitr⁺ f)
```

## Carrier attempt 1

The projection model with one added reading point. Constants read
constantly as themselves; the added point is the twist in both
slots, reads whichever flank holds the twist, and reads the
coterm where both flanks are constant. Readback and both tiers
hold. The negative cut dies: a constant against the twist is a
mixed reader — the coterm where constant, the leading constant at
the twist — and the three-point carrier holds no such edge.

```agda
module attempt₁ where

  E : Type
  E = Bool ⊎ ⊤

  ⋆ : E
  ⋆ = inr tt

  is-inl : E → Type
  is-inl (inl _) = ⊤
  is-inl (inr _) = ⊥

  tflag : E → Type
  tflag (inl true)  = ⊤
  tflag (inl false) = ⊥
  tflag (inr _)     = ⊥

  E-set : is-set E
  E-set = ⊎-is-hlevel 0 Bool.set (is-prop→is-set (λ _ _ → refl))

  rf : E → Sigma ⊤ (λ _ → E) × Sigma ⊤ (λ _ → E) → E
  rf (inl m) γ = inl m
  rf (inr t) ((_ , inr _) , (_ , k)) = k
  rf (inr t) ((_ , inl m) , (_ , inr _)) = inl m
  rf (inr t) ((_ , inl m) , (_ , inl n)) = inl n

  P : virtual-graph 0ℓ 0ℓ
  P .virtual-graph.ob      = ⊤
  P .virtual-graph.hom _ _ = E
  P .virtual-graph.reflect = rf
  P .virtual-graph.twist⁺ _ = ⋆
  P .virtual-graph.twist⁻ _ = ⋆

  open virtual-graph P using (coact-π; act-π)
  open sequents P using (is-representable; eval)

  rb : (e : E) → eval (rf e) ≡ e
  rb (inl m) = refl
  rb (inr t) = refl

  tier⁻ : is-contr (fiber (coact-π {tt} {tt}) snd)
  tier⁻ .center = ⋆ , refl
  tier⁻ .paths (inr t , w) i =
    ⋆ , Π-is-hlevel 2 (λ _ → E-set) (coact-π ⋆) snd refl w i
  tier⁻ .paths (inl m , w) =
    ex-falso (subst is-inl (happly w (tt , ⋆)) tt)

  act-π-⋆ : (t : Sigma ⊤ (λ _ → E)) → act-π ⋆ t ≡ t .snd
  act-π-⋆ (_ , inl m) = refl
  act-π-⋆ (_ , inr t) = refl

  tier⁺ : is-contr (fiber (act-π {tt} {tt}) snd)
  tier⁺ .center = ⋆ , funext act-π-⋆
  tier⁺ .paths (inr t , w) i =
    ⋆ , Π-is-hlevel 2 (λ _ → E-set) (act-π ⋆) snd (funext act-π-⋆) w i
  tier⁺ .paths (inl m , w) =
    ex-falso (subst is-inl (happly w (tt , ⋆)) tt)

  no-cut⁻ : is-representable (composite⁻ P (inl false) ⋆) → ⊥
  no-cut⁻ (inl x , w) =
    subst tflag
      ( sym (happly w ((tt , ⋆) , (tt , inl true)))
      ∙ happly w ((tt , ⋆) , (tt , inl false)) )
      tt
  no-cut⁻ (inr t , w) =
    subst is-inl (sym (happly w ((tt , ⋆) , (tt , ⋆)))) tt
```

## Carrier attempt 2

The four readers with the constants reindexed to themselves and
the positive twist moved to the coterm projection. Every edge
reads back as itself, and each tier's centre is the other twist —
the balanced situation on the nose. The positive cut dies: the
coterm projection against the term projection composes to the
reader constantly at `π₁`, and no edge reads constantly at a
projection — readback pins every constant reader to its own
value.

```agda
module attempt₂ where

  M : Type
  M = Bool × Bool

  π₁ π₂ κ₁ : M
  π₁ = false , false
  π₂ = false , true
  κ₁ = true , false

  is-true : Bool → Type
  is-true true  = ⊤
  is-true false = ⊥

  flag₁ : M → Type
  flag₁ v = is-true (v .fst)

  M-set : is-set M
  M-set = ×-is-hlevel 2 Bool.set Bool.set

  rf : M → Sigma ⊤ (λ _ → M) × Sigma ⊤ (λ _ → M) → M
  rf (false , false) γ = γ .fst .snd
  rf (false , true)  γ = γ .snd .snd
  rf (true , d)      γ = true , d

  Q : virtual-graph 0ℓ 0ℓ
  Q .virtual-graph.ob      = ⊤
  Q .virtual-graph.hom _ _ = M
  Q .virtual-graph.reflect = rf
  Q .virtual-graph.twist⁺ _ = π₂
  Q .virtual-graph.twist⁻ _ = π₁

  open virtual-graph Q using (coact-π; act-π)
  open sequents Q using (is-representable; eval)

  rb : (e : M) → eval (rf e) ≡ e
  rb (false , false) = refl
  rb (false , true)  = refl
  rb (true , d)      = refl

  tier⁻ : is-contr (fiber (coact-π {tt} {tt}) snd)
  tier⁻ .center = π₂ , refl
  tier⁻ .paths ((false , true) , w) i =
    π₂ , Π-is-hlevel 2 (λ _ → M-set) (coact-π π₂) snd refl w i
  tier⁻ .paths ((false , false) , w) =
    ex-falso (subst flag₁ (sym (happly w (tt , κ₁))) tt)
  tier⁻ .paths ((true , d) , w) =
    ex-falso (subst flag₁ (happly w (tt , π₁)) tt)

  tier⁺ : is-contr (fiber (act-π {tt} {tt}) snd)
  tier⁺ .center = π₁ , refl
  tier⁺ .paths ((false , false) , w) i =
    π₁ , Π-is-hlevel 2 (λ _ → M-set) (act-π π₁) snd refl w i
  tier⁺ .paths ((false , true) , w) =
    ex-falso (subst flag₁ (sym (happly w (tt , κ₁))) tt)
  tier⁺ .paths ((true , d) , w) =
    ex-falso (subst flag₁ (happly w (tt , π₁)) tt)

  no-cut⁺ : is-representable (composite⁺ Q π₂ π₁) → ⊥
  no-cut⁺ ((false , false) , w) =
    subst flag₁ (happly w ((tt , κ₁) , (tt , κ₁))) tt
  no-cut⁺ ((false , true) , w) =
    subst flag₁ (happly w ((tt , κ₁) , (tt , κ₁))) tt
  no-cut⁺ ((true , d) , w) =
    subst flag₁ (happly w ((tt , κ₁) , (tt , κ₁))) tt
```

## The verdict

Both carriers die on a cut, the same way. Readback pins every
constant reader to its own value, while a tier centre must read a
flank. The mixed composites manufacture readers constant at a
projection — the negative cut of a constant against the twist,
the positive cut of the coterm projection against the term
projection — and no readback carrier holds such an edge. On the
other side, the units reach only twist-flanked words, and the
offset of the two units blocks the interchange route to a general
derivation. The gate stays open in both directions.
