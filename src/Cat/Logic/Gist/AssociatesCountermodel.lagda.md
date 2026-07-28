Spike: the failing mixed word is independent of the deductive-system
axioms.

Two finite models bound the associativity profile. In both, the tower
theorems `assoc⁺`, `assoc⁻` and `mixed-assoc` apply, and one closed
instance of `associates` fails. So the provable profile of the
three-factor words is exactly the pre-duploid triple.

The projection model reflects every edge to the constant judgment on
itself. Each hand then projects: the positive composite is the first
factor, the negative composite is the second. `associates f g h`
computes to `h ≡ f`, and no edge is thunkable or linear. The same
carrier satisfies the readback record of
`Cat.Logic.Gist.FramedInterchange`, so readback and both cuts do not
derive `associates` either. What the projection model lacks is the
invertibility tier, which it refutes.

The four-reader model repairs that: a full deductive system on
`Bool × Bool` in which `associates` still fails. An edge is a reader
of the argument. The first component chooses between projection and
constant, the second names a side. The tier centres are the two
projection readers, and they carry the whole of both classes. The
coterm reader is the one thunkable edge. The term reader, which is
both twists and the `⁺` centre, is the one linear edge. In
particular the twists are not thunkable.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.AssociatesCountermodel where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Bool using (Bool; true; false; module Bool)
open import Core.Data.Empty

open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-hlevel; ×-is-hlevel)
open import Core.Function.Embedding using (injective→is-embedding)

open import Cat.Logic.Type
open import Cat.Logic.Base
open import Cat.Logic.Gist.FramedInterchange using (framed; module framing)

is-true : Bool → Type
is-true true  = ⊤
is-true false = ⊥
```

## The projection model

One object, edges the booleans, and a reflection that ignores its
argument. A judgment reads off its edge at any argument, so
reflection is injective and stability is an embedding over the hom
set. Each composite judgment collapses to the constant judgment on
one factor, and that factor represents it on the nose.

```agda
module projection where

  rf : Bool → Sigma ⊤ (λ _ → Bool) × Sigma ⊤ (λ _ → Bool) → Bool
  rf m _ = m

  emb : (α : Sigma ⊤ (λ _ → Bool) × Sigma ⊤ (λ _ → Bool) → Bool)
      → is-prop (fiber rf α)
  emb = injective→is-embedding (Π-is-hlevel 2 λ _ → Bool.set) rf
          (λ w → happly w ((tt , false) , (tt , false)))

  P : virtual-graph 0ℓ 0ℓ
  P .virtual-graph.ob      = ⊤
  P .virtual-graph.hom _ _ = Bool
  P .virtual-graph.reflect = rf
  P .virtual-graph.twist⁺ _ = false
  P .virtual-graph.twist⁻ _ = false

  S : is-stable P
  S α = emb α

  C⁺ : is-composable⁺ P
  C⁺ f g = f , refl

  C⁻ : is-composable⁻ P
  C⁻ f g = g , refl

  open tower {G = P} S C⁺ C⁻
```

## What fails there

With both hands projections, `associates f g h` is `h ≡ f`, and any
distinct pair refutes it. The two universal closures die at every
edge: a thunkable edge would equal every trailing edge, a linear one
every leading edge.

```agda
  no-associates : ∀ g → associates true g false → ⊥
  no-associates g w = subst is-true (sym w) tt

  no-thunkable : ∀ f → thunkable f → ⊥
  no-thunkable false T = subst is-true (T true true) tt
  no-thunkable true  T = subst is-true (sym (T true false)) tt

  no-linear : ∀ h → linear h → ⊥
  no-linear false L = subst is-true (sym (L true true)) tt
  no-linear true  L = subst is-true (L false false) tt
```

The invertibility tier is what this model does not have. A centre of
the `⁻` fiber would read constantly as the identity of the coterm
family. Two coterms already disagree.

```agda
  no-invertible⁻ : is-invertible⁻ P → ⊥
  no-invertible⁻ I =
    subst is-true
      ( sym (happly (I tt .center .snd) (tt , true))
      ∙ happly (I tt .center .snd) (tt , false) )
      tt
```

## Readback does not repair it

The same carrier satisfies every field of the readback record. The
axiom reads back the edge by definition, and both cuts are
contractible over the embedding. The failing word keeps its
projection reading, so the record proves `unitr⁺`, `unitl⁻` and
`mixed-assoc` while `associates` still fails.

```agda
  F : framed 0ℓ 0ℓ
  F .framed.ob      = ⊤
  F .framed.hom _ _ = Bool
  F .framed.reflect = rf
  F .framed.twist⁺ _ = false
  F .framed.twist⁻ _ = false
  F .framed.readback _ = refl
  F .framed.cut⁺ f g = prop-inhabited→is-contr (emb _) (f , refl)
  F .framed.cut⁻ f g = prop-inhabited→is-contr (emb _) (g , refl)

  module R = framing F

  no-associates-readback
    : ∀ g → (true R.⨾⁺ g) R.⨾⁻ false ≡ true R.⨾⁺ (g R.⨾⁻ false) → ⊥
  no-associates-readback g w = subst is-true (sym w) tt
```

## The four readers

Edges are pairs of booleans, read as functions of the argument. A
`false` first component is a projection onto one flank: `π₁` returns
the term flank, `π₂` the coterm flank. A `true` first component is a
constant, at the projection its second component names. Reflection
applies the reader.

```agda
module four-reader where

  M : Type
  M = Bool × Bool

  π₁ π₂ κ₁ κ₂ : M
  π₁ = false , false
  π₂ = false , true
  κ₁ = true , false
  κ₂ = true , true

  M-set : is-set M
  M-set = ×-is-hlevel 2 Bool.set Bool.set

  rf : M → Sigma ⊤ (λ _ → M) × Sigma ⊤ (λ _ → M) → M
  rf (false , false) γ = γ .fst .snd
  rf (false , true)  γ = γ .snd .snd
  rf (true  , d)     γ = false , d

  flag₁ flag₂ : M → Type
  flag₁ v = is-true (v .fst)
  flag₂ v = is-true (v .snd)
```

One probe argument, with a constant in both flanks, separates the
four readers. Each projection returns a constant and each constant
returns a projection. The probe reading is the flip of the first
component, an involution, so reflection is injective.

```agda
  probe : Sigma ⊤ (λ _ → M) × Sigma ⊤ (λ _ → M)
  probe = (tt , κ₁) , (tt , κ₂)

  flip₁ : M → M
  flip₁ (false , d) = true  , d
  flip₁ (true  , d) = false , d

  flip₁-rf : ∀ m → flip₁ (rf m probe) ≡ m
  flip₁-rf (false , false) = refl
  flip₁-rf (false , true)  = refl
  flip₁-rf (true  , d)     = refl

  rf-inj : {m n : M} → rf m ≡ rf n → m ≡ n
  rf-inj {m} {n} w = sym (flip₁-rf m) ∙ ap flip₁ (happly w probe) ∙ flip₁-rf n
```

## A full deductive system

Both twists are the term projection `π₁`. Each composite judgment
computes to a reader again, so a case split represents both cuts. A
projection head passes the composite to its far factor, and a
constant head stays constant.

```agda
  model : virtual-graph 0ℓ 0ℓ
  model .virtual-graph.ob      = ⊤
  model .virtual-graph.hom _ _ = M
  model .virtual-graph.reflect = rf
  model .virtual-graph.twist⁺ _ = π₁
  model .virtual-graph.twist⁻ _ = π₁

  open virtual-graph model using (coact-π; act-π)

  S : is-stable model
  S α = injective→is-embedding (Π-is-hlevel 2 λ _ → M-set) rf rf-inj α

  C⁺ : is-composable⁺ model
  C⁺ (false , false) g = π₁ , refl
  C⁺ (false , true) (false , false) = κ₁ , refl
  C⁺ (false , true) (false , true)  = π₂ , refl
  C⁺ (false , true) (true , d) = (true , d) , refl
  C⁺ (true , d) g = (true , d) , refl

  C⁻ : is-composable⁻ model
  C⁻ f (false , true) = π₂ , refl
  C⁻ f (true , d) = (true , d) , refl
  C⁻ (false , false) (false , false) = π₁ , refl
  C⁻ (false , true)  (false , false) = κ₁ , refl
  C⁻ (true , d)      (false , false) = (true , d) , refl
```

The projection onto each side inhabits that side's tier: the `⁻`
centre is `π₂` and the `⁺` centre is `π₁`. Contractibility is a case
split. The centre's witness lives in a set, and every other edge
misreads some flank.

```agda
  tier⁻ : is-contr (fiber (coact-π {tt} {tt}) snd)
  tier⁻ .center = π₂ , refl
  tier⁻ .paths ((false , true) , w) i =
    π₂ , Π-is-hlevel 2 (λ _ → M-set) (coact-π π₂) snd refl w i
  tier⁻ .paths ((false , false) , w) =
    ex-falso (subst flag₂ (sym (happly w (tt , π₂))) tt)
  tier⁻ .paths ((true , d) , w) =
    ex-falso (subst flag₁ (sym (happly w (tt , (true , d)))) tt)

  tier⁺ : is-contr (fiber (act-π {tt} {tt}) snd)
  tier⁺ .center = π₁ , refl
  tier⁺ .paths ((false , false) , w) i =
    π₁ , Π-is-hlevel 2 (λ _ → M-set) (act-π π₁) snd refl w i
  tier⁺ .paths ((false , true) , w) =
    ex-falso (subst flag₂ (sym (happly w (tt , π₂))) tt)
  tier⁺ .paths ((true , d) , w) =
    ex-falso (subst flag₁ (sym (happly w (tt , (true , d)))) tt)

  D : is-deductive-system model
  D .is-deductive-system.stable = S
  D .is-deductive-system.composable .is-composable.contr⁺ = C⁺
  D .is-deductive-system.composable .is-composable.contr⁻ = C⁻
  D .is-deductive-system.invertible .is-invertible.fiber⁻ = λ _ → tier⁻
  D .is-deductive-system.invertible .is-invertible.fiber⁺ = λ _ → tier⁺
```

## The kill, and the classes

`associates π₁ g π₂` computes to `π₂ ≡ π₁` for every middle edge.
The left bracketing ends in the coterm projection, the right one in
the term projection. So a full deductive system leaves the failing
word underivable.

```agda
  open tower {G = model} S C⁺ C⁻

  no-associates : ∀ g → associates π₁ g π₂ → ⊥
  no-associates g w = subst flag₂ w tt
```

The classes are exactly the centres. `π₂` associates ahead of every
pair, `π₁` behind every pair, and the remaining six closures each die
on a computed instance. The linear edge `π₁` is both twists, so the
framing itself is linear and not thunkable.

```agda
  centre⁻-thunkable : thunkable π₂
  centre⁻-thunkable g (false , true) = refl
  centre⁻-thunkable g (true , d) = refl
  centre⁻-thunkable (false , false) (false , false) = refl
  centre⁻-thunkable (false , true)  (false , false) = refl
  centre⁻-thunkable (true , e)      (false , false) = refl

  centre⁺-linear : linear π₁
  centre⁺-linear (false , false) g = refl
  centre⁺-linear (false , true) (false , false) = refl
  centre⁺-linear (false , true) (false , true)  = refl
  centre⁺-linear (false , true) (true , e) = refl
  centre⁺-linear (true , d) g = refl

  no-thunkable-twist : thunkable π₁ → ⊥
  no-thunkable-twist T = subst flag₂ (T π₁ π₂) tt

  no-thunkable-κ : ∀ d → thunkable (true , d) → ⊥
  no-thunkable-κ d T = subst flag₁ (sym (T π₁ π₂)) tt

  no-linear-centre⁻ : linear π₂ → ⊥
  no-linear-centre⁻ L = subst flag₂ (L π₁ π₁) tt

  no-linear-κ : ∀ d → linear (true , d) → ⊥
  no-linear-κ d L = subst flag₁ (L π₁ π₁) tt
```
