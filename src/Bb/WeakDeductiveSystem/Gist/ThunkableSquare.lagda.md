Spike: thunkability is data, and the length-4 square does not
truncate it.

`compat` is the length-4 compatibility square for a thunkable
edge. It says the two resolutions of the blocked word inside
`f ⨾⁺ g ⨾⁻ h ⨾⁺ k` agree. The square consumes the witness at
`(g , h)` and at `(g , h ⨾⁺ k)`. Its other three edges are tower
theorems. So the square is the least coherence a choice of
associators can carry. It is naturality of the choice when the
trailing edge grows through the valid mixed word. The `⨾⁻` growth
gives a pentagon with three witness instances against `assoc⁻`.
Growth at the leading edge produces witnesses for composites, not
a law. Over hom sets the choice and the square are both
propositions.

The circle model decides the wild case. One object, homs the
circle, both twists at `base`. Reflection reads both flanks
through the multiplication. The model is a full deductive system.
`associates base g h` computes to the loop space of the circle at
`mult g h`. So `thunkable base` holds in provably distinct ways:
`refl` and its `rot`-shift differ by winding. Thunkability is
structure at full deductive-system strength, not a property.

The square does not cut the freedom. The constant witness
satisfies it. `rot` is `mult`-equivariant, so the shifted witness
satisfies it too. The coherent refinement is then not a
proposition either. A propositional form of thunkability must
demand more than the closure and its coherence. A contractibility
demand in the tier style is strictly stronger than inhabitation.
This model separates the two.

This module uses `--cubical` because it consumes
`loop-nontrivial` and `Circle-is-groupoid` in unerased positions.
Both ride the winding equivalence, which `ua` builds.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.WeakDeductiveSystem.Gist.ThunkableSquare where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Path.Base using (ap-comp)
open import Core.Transport.J using (J; subst)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (SinglP-contr; is-prop→is-set)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop)
open import Core.Equiv.Base using (_≃_; iso→equiv)
open import Core.Equiv.Properties using (is-contr-equiv; Σ-equiv-snd)
open import Core.Data.Empty using (⊥)

open import Bb.WeakDeductiveSystem.Type
open import Bb.WeakDeductiveSystem.Base

open import HData.Circle
open Circle
```

## The square

The two witness instances close the pentagon whose other three
edges are `mixed-assoc` twice and `assoc⁺` once. Over hom sets
each `associates` cell lives in a set. The closure is then a
proposition, and the square holds for every witness.

```agda
module coherence {o h} {G : virtual-graph o h}
  (S : is-stable G) (C⁺ : is-composable⁺ G) (C⁻ : is-composable⁻ G) where
  open virtual-graph G
  open tower S C⁺ C⁻ public

  compat : ∀ {w x y z v} {f : hom w x} (T : thunkable f)
         → hom x y → hom y z → hom z v → Type h
  compat {f = f} T g h k =
      ap (_⨾⁺ k) (T g h)
        ∙ (assoc⁺ f (g ⨾⁻ h) k ∙ ap (f ⨾⁺_) (mixed-assoc g h k))
    ≡ mixed-assoc (f ⨾⁺ g) h k ∙ T g (h ⨾⁺ k)

  coherent : ∀ {w x} (f : hom w x) → thunkable f → Type (o ⊔ h)
  coherent {x = x} f T =
    ∀ {y z v} (g : hom x y) (h : hom y z) (k : hom z v)
    → compat T g h k

  thunkable-is-prop : (∀ {x y} → is-set (hom x y))
                    → ∀ {w x} (f : hom w x) → is-prop (thunkable f)
  thunkable-is-prop hs f =
    Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → hs _ _

  compat-over-sets : (∀ {x y} → is-set (hom x y))
                   → ∀ {w x y z v} {f : hom w x} (T : thunkable f)
                     (g : hom x y) (h : hom y z) (k : hom z v)
                   → compat T g h k
  compat-over-sets hs T g h k = hs _ _ _ _
```

## The circle model

Reflection sends an edge to the reader that multiplies it between
the two flanks. The fiber of reflection over a reflected edge is
contractible. Currying is definitional, left translations cancel,
the first slot is faithful, and the path singleton remains. So
stability holds with no set condition on the homs.

```agda
module circle where

  rf : Circle → Sigma ⊤ (λ _ → Circle) × Sigma ⊤ (λ _ → Circle) → Circle
  rf m γ = mult (γ .fst .snd) (mult m (γ .snd .snd))

  model : virtual-graph 0ℓ 0ℓ
  model .virtual-graph.ob      = ⊤
  model .virtual-graph.hom _ _ = Circle
  model .virtual-graph.reflect = rf
  model .virtual-graph.twist⁺ _ = base
  model .virtual-graph.twist⁻ _ = base

  open virtual-graph model using (coact-π; act-π)

  private
    rev-path : {x y : Circle} → (x ≡ y) ≃ (y ≡ x)
    rev-path = iso→equiv (λ p i → p (~ i)) (λ p i → p (~ i))
      (λ _ → refl) (λ _ → refl)

    slice : (n m : Circle)
          → (rf n ≡ rf m)
          ≃ ((l r : Circle) → mult l (mult n r) ≡ mult l (mult m r))
    slice n m = iso→equiv
      (λ w l r i → w i ((tt , l) , (tt , r)))
      (λ v i γ → v (γ .fst .snd) (γ .snd .snd) i)
      (λ _ → refl) (λ _ → refl)

  rf-fiber-contr : (m : Circle) → is-contr (fiber rf (rf m))
  rf-fiber-contr m =
    is-contr-equiv (Σ-equiv-snd λ n → slice n m)
      (is-contr-equiv (Σ-equiv-snd λ n → mult-l-cancel)
        (is-contr-equiv (Σ-equiv-snd λ n → mult-faithful n m)
          (is-contr-equiv (Σ-equiv-snd λ _ → rev-path)
            (SinglP-contr {A = λ _ → Circle} m))))

  stable : is-stable model
  stable α u v =
    is-contr→is-prop
      (subst (λ β → is-contr (fiber rf β)) (u .snd)
        (rf-fiber-contr (u .fst)))
      u v
```

Both cuts land on the multiplication. The positive cut is one
associativity whisker. The negative cut also crosses the right
unit law, because the coterm axiom sits inside `act`.

```agda
  C⁺ : is-composable⁺ model
  C⁺ f g = mult f g
         , λ i γ → mult (γ .fst .snd) (mult-assoc f g (γ .snd .snd) i)

  C⁻ : is-composable⁻ model
  C⁻ f g = mult f g
         , sym (funext λ γ →
             ap (λ t → mult (mult (γ .fst .snd) t) (mult g (γ .snd .snd)))
                (mult-unit-r f)
           ∙ (mult-assoc (γ .fst .snd) f (mult g (γ .snd .snd))
           ∙ ap (mult (γ .fst .snd)) (sym (mult-assoc f g (γ .snd .snd)))))
```

Each tier is the faithfulness of translation at the unit. The
coterm side is definitional. The term side crosses the right unit
law twice. One crossing evaluates the family, the other moves the
centre onto `base`.

```agda
  private
    slice⁻ : (e : Circle)
           → (coact-π {tt} {tt} e ≡ snd) ≃ ((r : Circle) → mult e r ≡ r)
    slice⁻ e = iso→equiv
      (λ w r i → w i (tt , r))
      (λ v i γ → v (γ .snd) i)
      (λ _ → refl) (λ _ → refl)

    slice⁺ : (e : Circle)
           → (act-π {tt} {tt} e ≡ snd)
           ≃ ((l : Circle) → mult l (mult e base) ≡ l)
    slice⁺ e = iso→equiv
      (λ w l i → w i (tt , l))
      (λ v i t → v (t .snd) i)
      (λ _ → refl) (λ _ → refl)

    eval-free : (c : Circle) → ((l : Circle) → mult l c ≡ l) ≃ (c ≡ base)
    eval-free c = iso→equiv to fro sec retr
      where
      to : ((l : Circle) → mult l c ≡ l) → c ≡ base
      to w = w base

      fro : c ≡ base → (l : Circle) → mult l c ≡ l
      fro v l = ap (mult l) v ∙ mult-unit-r l

      sec : (w : (l : Circle) → mult l c ≡ l) → fro (to w) ≡ w
      sec w = funext (ind (λ l → fro (to w) l ≡ w l)
        (Path.unitr (w base))
        (is-prop→PathP (λ i → Circle-is-groupoid _ _ _ _)
          (Path.unitr (w base)) (Path.unitr (w base))))

      retr : (v : c ≡ base) → to (fro v) ≡ v
      retr v = Path.unitr v

    unit-conj : (e : Circle) → (mult e base ≡ base) ≃ (e ≡ base)
    unit-conj e = iso→equiv to fro sec retr
      where
      H : mult e base ≡ e
      H = mult-unit-r e

      to : mult e base ≡ base → e ≡ base
      to v = sym H ∙ v

      fro : e ≡ base → mult e base ≡ base
      fro u = H ∙ u

      sec : (v : mult e base ≡ base) → fro (to v) ≡ v
      sec v = Path.assoc H (sym H) v
            ∙ (ap (_∙ v) (Path.invr H) ∙ Path.unitl v)

      retr : (u : e ≡ base) → to (fro u) ≡ u
      retr u = Path.assoc (sym H) H u
             ∙ (ap (_∙ u) (Path.invl H) ∙ Path.unitl u)

  tier⁻ : is-contr (fiber (coact-π {tt} {tt}) snd)
  tier⁻ =
    is-contr-equiv (Σ-equiv-snd λ e → slice⁻ e)
      (is-contr-equiv (Σ-equiv-snd λ e → mult-faithful e base)
        (is-contr-equiv (Σ-equiv-snd λ _ → rev-path)
          (SinglP-contr {A = λ _ → Circle} base)))

  tier⁺ : is-contr (fiber (act-π {tt} {tt}) snd)
  tier⁺ =
    is-contr-equiv (Σ-equiv-snd λ e → slice⁺ e)
      (is-contr-equiv (Σ-equiv-snd λ e → eval-free (mult e base))
        (is-contr-equiv (Σ-equiv-snd λ e → unit-conj e)
          (is-contr-equiv (Σ-equiv-snd λ _ → rev-path)
            (SinglP-contr {A = λ _ → Circle} base))))

  D : is-deductive-system model
  D .is-deductive-system.stable = stable
  D .is-deductive-system.composable .is-composable.contr⁺ = C⁺
  D .is-deductive-system.composable .is-composable.contr⁻ = C⁻
  D .is-deductive-system.invertible .is-invertible.fiber⁻ = λ _ → tier⁻
  D .is-deductive-system.invertible .is-invertible.fiber⁺ = λ _ → tier⁺
```

## Two witnesses

Both hands compute to `mult`, so `associates base g h` is the
loop space at `mult g h`. The constant family and its pointwise
`rot`-shift are both witnesses. Evaluation at the axiom separates
them by one winding.

```agda
  open coherence {G = model} stable C⁺ C⁻

  T₀ : thunkable base
  T₀ g h = refl

  shift : (f : Circle) → thunkable f → thunkable f
  shift f T g h = T g h ∙ rot (mult f (mult g h))

  T₁ : thunkable base
  T₁ = shift base T₀

  thunkable-not-prop : is-prop (thunkable base) → ⊥
  thunkable-not-prop W =
    loop-nontrivial
      (sym (Path.unitl loop) ∙ sym (λ i → W T₀ T₁ i base base))

  associates-not-prop : is-prop (associates base base base) → ⊥
  associates-not-prop W = loop-nontrivial (W loop refl)
```

## The square does not separate them

At the base edge the tower associator degenerates. The fiber over
the common judgment is a proposition, so the stability path
agrees with the pair path whose first component is constant. The
trace on edges is then `refl`.

```agda
  assoc⁺-base : (g k : Circle) → assoc⁺ base g k ≡ refl
  assoc⁺-base g k =
    ap (ap fst)
      (is-prop→is-set (stable (tri⁺.E base g k))
        (tri⁺.a₁ base g k) (tri⁺.a₂ base g k)
        (tri⁺.σ base g k)
        (λ i → mult g k , edge i))
    where
    edge : tri⁺.a₁ base g k .snd ≡ tri⁺.a₂ base g k .snd
    edge = Path.unitr (C⁺ g k .snd) ∙ sym (Path.unitl (C⁺ g k .snd))
```

The constant witness satisfies the square through the degenerate
associator and the unit laws.

```agda
  T₀-coherent : coherent base T₀
  T₀-coherent g h k =
      Path.unitl (assoc⁺ base (g ⨾⁻ h) k ∙ mixed-assoc g h k)
    ∙ (ap (_∙ mixed-assoc g h k) (assoc⁺-base (mult g h) k)
    ∙ (Path.unitl (mixed-assoc g h k)
    ∙ sym (Path.unitr (mixed-assoc g h k))))
```

The shift preserves the square. `rot-mult` moves the shift across
the trailing whisker, and `rot` is natural, so the shift commutes
with the canonical edges and lands on the shift of the other
instance.

```agda
  rot-natural : {x y : Circle} (p : x ≡ y) → rot x ∙ p ≡ p ∙ rot y
  rot-natural {x} p =
    J (λ y q → rot x ∙ q ≡ q ∙ rot y)
      (Path.unitr (rot x) ∙ sym (Path.unitl (rot x))) p

  shift-coherent : (f : Circle) (T : thunkable f)
                 → coherent f T → coherent f (shift f T)
  shift-coherent f T cT g h k =
      ap (_∙ canon)
         ( ap-comp (_⨾⁺ k) (T g h) (rot X)
         ∙ ap (ap (_⨾⁺ k) (T g h) ∙_) (rot-mult X k))
    ∙ (sym (Path.assoc (ap (_⨾⁺ k) (T g h)) (rot (mult X k)) canon)
    ∙ (ap (ap (_⨾⁺ k) (T g h) ∙_) (rot-natural canon)
    ∙ (Path.assoc (ap (_⨾⁺ k) (T g h)) canon (rot Y)
    ∙ (ap (_∙ rot Y) (cT g h k)
    ∙ sym (Path.assoc (mixed-assoc (f ⨾⁺ g) h k)
            (T g (h ⨾⁺ k)) (rot Y))))))
    where
    X = mult f (mult g h)
    Y = mult f (mult g (mult h k))
    canon = assoc⁺ f (g ⨾⁻ h) k ∙ ap (f ⨾⁺_) (mixed-assoc g h k)

  T₁-coherent : coherent base T₁
  T₁-coherent = shift-coherent base T₀ T₀-coherent

  coherent-not-prop : is-prop (Sigma (thunkable base) (coherent base)) → ⊥
  coherent-not-prop W =
    loop-nontrivial
      (sym (Path.unitl loop)
       ∙ sym (λ i → W (T₀ , T₀-coherent) (T₁ , T₁-coherent) i .fst base base))
```

## What the spike settles

`thunkable-not-prop` refutes the closure as a proposition in a
full deductive system. The deductive-system axioms leave
thunkability as structure. `coherent-not-prop` refutes the
square-refined closure as well. No coherence tower over the same
data can truncate it: the freedom is a loop-space action, and the
square is blind to a uniform shift.

What this model cannot refute is the square itself. Its witness
freedom is set-level, every definable shift is uniform, and
uniform shifts are natural. A witness that fails the square needs
a hom type with nontrivial parallel two-cells. No type in the
library provides one.
