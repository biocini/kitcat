The two-element heap, presented as a unital magmoid in two ways.

Reflection here is the ternary operation `t ⊕ m ⊕ k`, which has no
distinguished argument: every edge is neutral in the self-filled sense,
and both cuts are represented. What separates one edge from another is
idempotence, an equation and not an equivalence. The unit is therefore
a choice of origin laid on top of the reflection, and either choice
extends to a unital magmoid with the same graph, the same reflection,
and full interchange — but different compositions.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VgCategoryShape.Parity where

open import Core.Type
open import Core.Base
open import Core.Data.Empty using (⊥; ¬_)
open import Core.Data.Sigma
open import Core.Data.Bool
open import Core.Kan using (_∙_)
open import Core.Path.Base using (_≢_)
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv; iso→equiv)
open import Core.Function.Embedding
  using (is-embedding; injective→is-embedding
        ; is-embedding→contr-fibers)
open import Core.HLevel.Base using (Π-is-hlevel)

open import Bb.VgCategoryShape.Type
open import Bb.VgCategoryShape.Base
open import Bb.VgCategoryShape.Unit

open Bool using (xor; module xor)
```

## Parity as a reflection

```agda
private
  arg : Type 0ℓ
  arg = (Σ w ∶ ⊤ , Bool) × (Σ v ∶ ⊤ , Bool)

  emb : Bool → arg → Bool
  emb m γ = xor (γ .fst .snd) (xor m (γ .snd .snd))
```

Evaluating at any fixed pair of endpoints recovers the edge, so the
reflection is injective; the judgments form a set, so it is an
embedding and every represented judgment has a contractible fiber.

```agda
  emb-eval : ∀ m → emb m ((tt , false) , (tt , false)) ≡ m
  emb-eval m = xor.unitl (xor m false) ∙ xor.unitr m

  emb-lc : ∀ {m n} → emb m ≡ emb n → m ≡ n
  emb-lc {m} {n} p =
    sym (emb-eval m)
    ∙ ap (λ α → α ((tt , false) , (tt , false))) p
    ∙ emb-eval n

  emb-is-embedding : is-embedding emb
  emb-is-embedding =
    injective→is-embedding (Π-is-hlevel 2 λ _ → Bool.set) emb emb-lc
```

## Neutrality is free

Holding an edge in one slot and letting the other vary gives, on the
one hand, a doubled sum that the involution cancels, and on the other
a translation by `e ⊕ e`, which is zero. Neither computation looks at
which edge `e` is.

```agda
  self : ∀ e → xor e e ≡ false
  self e = sym (ap (xor e) (xor.unitr e)) ∙ xor.invol e false

  left-neutral : ∀ e → is-equiv (λ (h : Bool) → xor e (xor e h))
  left-neutral e =
    iso→equiv (λ h → xor e (xor e h)) (λ h → h)
      (xor.invol e) (xor.invol e) .snd

  right-neutral : ∀ e → is-equiv (λ (g : Bool) → xor g (xor e e))
  right-neutral e =
    iso→equiv (λ g → xor g (xor e e)) (λ g → g) absorbs absorbs .snd
    where
      absorbs : ∀ g → xor g (xor e e) ≡ g
      absorbs g = ap (xor g) (self e) ∙ xor.unitr g
```

## The magmoid on an origin

With an origin chosen the two cuts have one and the same
representative, the sum through that origin.

```agda
  cmp : Bool → Bool → Bool → Bool
  cmp o f g = xor f (xor o g)

  shape⁺
    : ∀ o f g (γ : arg)
    → emb (cmp o f g) γ
    ≡ xor (γ .fst .snd) (xor f (xor o (xor g (γ .snd .snd))))
  shape⁺ o f g γ = ap (xor (γ .fst .snd))
    ( sym (xor.assoc f (xor o g) (γ .snd .snd))
    ∙ ap (xor f) (sym (xor.assoc o g (γ .snd .snd))) )

  shape⁻
    : ∀ o f g (γ : arg)
    → emb (cmp o f g) γ
    ≡ xor (xor (γ .fst .snd) (xor f o)) (xor g (γ .snd .snd))
  shape⁻ o f g γ =
    ap (xor (γ .fst .snd))
      ( ap (λ b → xor b (γ .snd .snd)) (xor.assoc f o g)
      ∙ sym (xor.assoc (xor f o) g (γ .snd .snd)) )
    ∙ xor.assoc (γ .fst .snd) (xor f o) (xor g (γ .snd .snd))

  origin-readback : ∀ o m → xor o (xor m o) ≡ m
  origin-readback o m = ap (xor o) (xor.comm m o) ∙ xor.invol o m
```

```agda
heap : Bool → hcategory 0ℓ 0ℓ
heap o .hcategory.ob = ⊤
heap o .hcategory.hom _ _ = Bool
heap o .hcategory.reflect m γ =
  xor (γ .fst .snd) (xor m (γ .snd .snd))
heap o .hcategory.rx _ = o
heap o .hcategory.readback f = origin-readback o f
heap o .hcategory.cut⁺ f g =
  is-embedding→contr-fibers emb-is-embedding
    (cmp o f g , funext (shape⁺ o f g))
heap o .hcategory.cut⁻ f g =
  is-embedding→contr-fibers emb-is-embedding
    (cmp o f g , funext (shape⁻ o f g))
heap o .hcategory.unit _ =
  o , (left-neutral o , right-neutral o) , xor.invol o o
```

## What the axioms fail to select

Every edge is neutral, and interchange holds in full — as
`Bb.VgCategoryShape.Base` proves it must. Readback holds at
either origin, since the group is
2-torsion, so alignment does not separate them either.

```agda
module _ (o : Bool) where
  open hcat (heap o)

  every-edge-is-neutral : (e : Bool) → is-neutral e
  every-edge-is-neutral e = left-neutral e , right-neutral e

  full-interchange : (f g : Bool) → composite⁺ f g ≡ composite⁻ f g
  full-interchange f g = sym (reflect-⨾⁺ f g) ∙ reflect-⨾⁻ f g
```

Idempotence is what remains, and it is not implied: over the origin
`false` the edge `true` is a unit candidate whose self-composite is the
origin instead of itself.

```agda
private
  false≢true : false ≢ true
  false≢true p = subst (λ { false → ⊤ ; true → ⊥ }) p tt

module _ where
  open hcat (heap false)

  rival-is-neutral : is-neutral true
  rival-is-neutral = every-edge-is-neutral false true

  rival-not-idempotent : ¬ (true ⨾⁻ true ≡ true)
  rival-not-idempotent = false≢true

  rival-not-the-unit : true ≢ idn
  rival-not-the-unit p = false≢true (sym p)
```

The two origins give two magmoids on one graph and one reflection.

```agda
same-reflection
  : (m : Bool) (γ : arg)
  → hcategory.reflect (heap false) m γ
  ≡ hcategory.reflect (heap true) m γ
same-reflection m γ = refl

compositions-differ
  : hcat._⨾⁺_ (heap false) true true
  ≢ hcat._⨾⁺_ (heap true) true true
compositions-differ = false≢true
```

## The origins are exchanged by a twist

Negation fixes the graph, commutes with reflection, and carries one
origin to the other. Nothing said about the reflection alone can
separate them, whatever its logical complexity, so idempotence is not
merely absent from the axioms — over this reflection it is
inexpressible.

```agda
private
  twist : Bool → Bool
  twist = xor true

  twist-arg : arg → arg
  twist-arg γ = (γ .fst .fst , twist (γ .fst .snd))
              , (γ .snd .fst , twist (γ .snd .snd))

  twist-emb
    : ∀ t m k
    → xor (twist t) (xor (twist m) (twist k)) ≡ twist (xor t (xor m k))
  twist-emb true  true  true  = refl
  twist-emb true  true  false = refl
  twist-emb true  false true  = refl
  twist-emb true  false false = refl
  twist-emb false true  true  = refl
  twist-emb false true  false = refl
  twist-emb false false true  = refl
  twist-emb false false false = refl

reflection-is-equivariant
  : (m : Bool) (γ : arg)
  → hcategory.reflect (heap false) (twist m) (twist-arg γ)
  ≡ twist (hcategory.reflect (heap false) m γ)
reflection-is-equivariant m γ = twist-emb (γ .fst .snd) m (γ .snd .snd)

twist-moves-the-origin
  : twist (hcategory.idn (heap false))
  ≡ hcategory.idn (heap true)
twist-moves-the-origin = refl
```
