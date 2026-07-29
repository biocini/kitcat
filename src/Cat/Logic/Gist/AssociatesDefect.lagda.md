Spike: the mixed-associativity defect is a twist word, one per
flanking edge, not an opaque discrepancy.

`associates f g h` compares the two bracketings of the mixed word
whose junctions run positive then negative. The 2026-07-27
countermodel showed `associates` fails in general, over
`Cat.Logic.Gist.BalancedWord`, but named no relation between the
two bracketings. This spike supplies one. Each bracketing
determines the other up to a correction, and the word depends on
one flanking edge alone.

The correction turns the independence result into a mechanism. It
is a power of the bicyclic defect, the word already on record as
the obstruction to `associates`. Each correction is a unit exactly
at the closure the deductive-system axioms already name for that
edge. Thunkable is the closure for the leading edge, and linear is
the closure for the trailing edge. So those two closures are not an
arbitrary pair. They are exactly the conditions under which a
correction vanishes.

Balance is the collapse where the bicyclic defect becomes the
unit, and it erases both corrections at once. The pre-duploid
profile gains a reason in place of a bare countermodel. It is the
exact strength at which the correction survives, and duploid
strength is the exact strength that removes it.

There is one correction per hand. `w⁺ (rise f)` flanks the leading
side through the positive cut, and `rise f` is the value of the
edge at zero. `w⁻ (zrunW h)` flanks the trailing side through the
negative cut, and `zrunW h` is the length of the zero plateau of
`h`. The theorems `defect⁺` and `defect⁻` hold for every triple,
with no failure hypothesis. The middle edge never enters either
correction.

Both corrections are words in the twists by construction. `w⁺ (S Z)`
is the reverse bicyclic composite `τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)` on the nose, the
word `bicyclic-persists` separates from the unit. `thunkable→rise`
and `rise→thunkable` pin `w⁺` to the unit exactly when `f` is
thunkable. `run→linear` and `linear→run` pin `w⁻` to the unit
exactly when `h` is linear.

The defect is not a framing constant. `no-uniform⁺` and
`no-uniform⁻` refute a single word for all triples in the two
surviving placements. Every placement is well typed at the point,
and one-sided invertibility keeps them inequivalent. The label
legend, over `L = (f ⨾⁺ g) ⨾⁻ h` and `R = f ⨾⁺ (g ⨾⁻ h)`: the
whole-word placements put `w` on one side of one hand, and the seam
placements move `w` inside one bracketing. All fourteen others fail
at a concrete triple, for every `w` at once: `A1-refuted` through
`A8-refuted` cover `R ≡ L ⨾⁺ w`, `R ≡ L ⨾⁻ w`, `R ≡ w ⨾⁻ L`,
`L ≡ R ⨾⁺ w`, `L ≡ w ⨾⁺ R`, `L ≡ w ⨾⁻ R`, and `S1-refuted` through
`S8-refuted` cover the seams. The surviving pair is the whole
placement analysis.

`shift-w⁺` and `shift-w⁻` show both corrections carry only the
winding grade of their unit. The grade map is the collapse where
the twists cancel two-sidedly, onto the translation group in which
the reverse bicyclic composite is already the unit.
`shift-associates` states the consequence directly: the two
bracketings of `associates` always agree in winding grade.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.AssociatesDefect where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat
open import Core.Data.List
open import Core.Data.Bool
open import Core.Data.Sum using (_⊎_; inl; inr)
open import Core.Data.Int

open import Cat.Logic.Base
open import Cat.Logic.Gist.BalancedWord

open Nat using (_+_; _-_; _<_; _≤_)
open Bool using (So; so-fst; so-snd)
open Int using (add; _⊖_; zpred; zero-l; ⊖-pred)

open tower BW BW-stable BW-comp⁺ BW-comp⁻
  using (_⨾⁺_; _⨾⁻_; associates; thunkable; linear)
```

## Small lemmas

Disequalities, monus recovery, order splitting, and the values of
the twists.

```agda
z≢s : ∀ {n} → Z ≡ S n → ⊥
z≢s e = subst pos? (sym e) tt

s≢z : ∀ {n} → S n ≡ Z → ⊥
s≢z e = subst pos? e tt

monus-zero : ∀ a → Z - a ≡ Z
monus-zero Z     = refl
monus-zero (S a) = refl

le-monus-plus : ∀ a v → a ≤ v → (v - a) + a ≡ v
le-monus-plus Z     v     q = Nat.add.unitr v
le-monus-plus (S a) Z     q = ex-falso (Nat.lt.¬n<z (Nat.lt.peel Z q))
le-monus-plus (S a) (S v) q =
  Nat.add.+suc (v - a) a ∙ ap S (le-monus-plus a v (Nat.lt.peel (S v) q))

le-split : ∀ k n → k ≤ n → Σ m ∶ Nat , n ≡ k + m
le-split Z     n     q = n , refl
le-split (S k) Z     q = ex-falso (Nat.lt.¬n<z (Nat.lt.peel Z q))
le-split (S k) (S n) q with le-split k n (Nat.lt.peel (S n) q)
... | m , e = m , ap S e

le-pos : ∀ x v → S x ≤ v → Σ j ∶ Nat , v ≡ S j
le-pos x Z     q = ex-falso (Nat.lt.¬n<z (Nat.lt.peel Z q))
le-pos x (S v) q = v , refl

ev-ε : ∀ x → evW ε̂ x ≡ x
ev-ε = Nat.add.unitr

ev-τ : ∀ x → evW τ̂ x ≡ S x
ev-τ x = Nat.add.+suc x Z ∙ ap S (Nat.add.unitr x)

ev-cutε : ∀ x n → evW (x ⨾⁻ ε̂) n ≡ φ (evW x) n
ev-cutε x n = ev-comp (φW x) ε̂ n ∙ ap (evW (φW x)) (ev-ε n) ∙ ev-φ x n
```

## The corrections

`w⁺ a` is `a` twists composed with `a` double twists, interleaved so
the induction is structural; its denotation is `max (- , a)`, written
through monus. `w⁻ k` guards the `S k`-fold twist by `k` zeros; its
denotation is zero below `k` and the successor above. Both are words
in `τ̂` and `ε̂` under the two cuts, and nothing else.

```agda
w⁺ : Nat → W
w⁺ Z     = ε̂
w⁺ (S a) = τ̂ ⨾⁺ (w⁺ a ⨾⁺ δ̂)

pow⁺ : Nat → W → W
pow⁺ Z     x = ε̂
pow⁺ (S n) x = x ⨾⁺ pow⁺ n x

guard : Nat → W → W
guard Z     x = x
guard (S j) x = guard j x ⨾⁻ ε̂

w⁻ : Nat → W
w⁻ k = guard k (pow⁺ (S k) τ̂)

w⁺-unit : w⁺ Z ≡ ε̂
w⁺-unit = refl

w⁺-gen : w⁺ (S Z) ≡ τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)
w⁺-gen = refl

w⁻-unit : w⁻ Z ≡ τ̂
w⁻-unit = refl
```

Their denotations.

```agda
ev-w⁺ : ∀ a n → evW (w⁺ a) n ≡ (n - a) + a
ev-w⁺ Z     n = refl
ev-w⁺ (S a) Z =
  ev-comp τ̂ (w⁺ a ⨾⁺ δ̂) Z
  ∙ ap (evW τ̂) (ev-comp (w⁺ a) δ̂ Z ∙ ev-w⁺ a Z ∙ ap (_+ a) (monus-zero a))
  ∙ ev-τ a
ev-w⁺ (S a) (S m) =
  ev-comp τ̂ (w⁺ a ⨾⁺ δ̂) (S m)
  ∙ ap (evW τ̂)
       ( ev-comp (w⁺ a) δ̂ (S m)
       ∙ ap (evW (w⁺ a)) (Nat.add.unitr m)
       ∙ ev-w⁺ a m )
  ∙ ev-τ ((m - a) + a)
  ∙ sym (Nat.add.+suc (m - a) a)

ev-pow⁺τ : ∀ a m → evW (pow⁺ a τ̂) m ≡ m + a
ev-pow⁺τ Z     m = refl
ev-pow⁺τ (S a) m =
  ev-comp τ̂ (pow⁺ a τ̂) m
  ∙ ap (evW τ̂) (ev-pow⁺τ a m)
  ∙ ev-τ (m + a)
  ∙ sym (Nat.add.+suc m a)

ev-guard-lo : ∀ j x m → m < j → evW (guard j x) m ≡ Z
ev-guard-lo Z     x m     p = ex-falso (Nat.lt.¬n<z p)
ev-guard-lo (S j) x Z     p = ev-cutε (guard j x) Z
ev-guard-lo (S j) x (S m) p =
  ev-cutε (guard j x) (S m) ∙ ev-guard-lo j x m (Nat.lt.peel j p)

ev-guard-hi : ∀ j x m → evW (guard j x) (j + m) ≡ evW x m
ev-guard-hi Z     x m = refl
ev-guard-hi (S j) x m =
  ev-cutε (guard j x) (S (j + m)) ∙ ev-guard-hi j x m

ev-w⁻-lo : ∀ k m → m < k → evW (w⁻ k) m ≡ Z
ev-w⁻-lo k = ev-guard-lo k (pow⁺ (S k) τ̂)

ev-w⁻-hi : ∀ k m → evW (w⁻ k) (k + m) ≡ S (k + m)
ev-w⁻-hi k m =
  ev-guard-hi k (pow⁺ (S k) τ̂) m
  ∙ ev-pow⁺τ (S k) m
  ∙ Nat.add.+suc m k
  ∙ ap S (Nat.add.comm m k)
```

## The two indices

`rise f` is the value at zero. `zrunW h` is the length of the zero
plateau: under weak monotonicity the edge is zero strictly below it
and positive from it on.

```agda
rise : W → Nat
rise f = evW f Z

zrun : List Nat → Nat → Nat
zrun []          Z     = S Z
zrun []          (S t) = Z
zrun (Z ∷ p)     t     = S (zrun p t)
zrun (S x ∷ p)   t     = Z

zrunW : W → Nat
zrunW h = zrun (h .fst) (h .snd .fst)

ev-zrun-lo : ∀ p t n → n < zrun p t → ev p t n ≡ Z
ev-zrun-lo []        Z     Z     q = refl
ev-zrun-lo []        Z     (S n) q =
  ex-falso (Nat.lt.¬n<z (Nat.lt.peel Z q))
ev-zrun-lo []        (S t) n     q = ex-falso (Nat.lt.¬n<z q)
ev-zrun-lo (Z ∷ p)   t     Z     q = refl
ev-zrun-lo (Z ∷ p)   t     (S n) q =
  ev-zrun-lo p t n (Nat.lt.peel (zrun p t) q)
ev-zrun-lo (S x ∷ p) t     n     q = ex-falso (Nat.lt.¬n<z q)

ev-zrun-hi : ∀ p t → So (incr? p t)
           → ∀ n → zrun p t ≤ n → Σ j ∶ Nat , ev p t n ≡ S j
ev-zrun-hi []        Z     inc Z     q = ex-falso (Nat.lt.irrefl q)
ev-zrun-hi []        Z     inc (S n) q = n + Z , refl
ev-zrun-hi []        (S t) inc n     q = n + t , Nat.add.+suc n t
ev-zrun-hi (Z ∷ p)   t     inc Z     q =
  ex-falso (Nat.lt.¬n<z (Nat.lt.peel Z q))
ev-zrun-hi (Z ∷ p)   t     inc (S n) q =
  ev-zrun-hi p t (so-snd (Z Nat.≤ᵇ ev p t Z) (incr? p t) inc)
    n (Nat.lt.peel (S n) q)
ev-zrun-hi (S x ∷ p) t     inc Z     q = x , refl
ev-zrun-hi (S x ∷ p) t     inc (S n) q =
  le-pos x (ev p t n)
    (Nat.le.cat
      (Nat.≤ᵇ-sound (S x) (ev p t Z)
        (so-fst (S x Nat.≤ᵇ ev p t Z) (incr? p t) inc))
      (ev-mono-le p t
        (so-snd (S x Nat.≤ᵇ ev p t Z) (incr? p t) inc)
        Z n Nat.lt.z<s))
```

## The main theorems

The two bracketings, read pointwise.

```agda
ev-mixL : ∀ f g h n
        → evW ((f ⨾⁺ g) ⨾⁻ h) n ≡ φ (evW (f ⨾⁺ g)) (evW h n)
ev-mixL f g h n =
  ev-comp (φW (f ⨾⁺ g)) h n ∙ ev-φ (f ⨾⁺ g) (evW h n)

ev-mixR : ∀ f g h n
        → evW (f ⨾⁺ (g ⨾⁻ h)) n ≡ evW f (φ (evW g) (evW h n))
ev-mixR f g h n =
  ev-comp f (g ⨾⁻ h) n
  ∙ ap (evW f) (ev-comp (φW g) h n ∙ ev-φ g (evW h n))
```

The leading correction: for every triple, the right bracketing is
the left one cut against `w⁺ (rise f)` on the outside of the
positive hand. Weak monotonicity pins the corrected values, and the
zero case is the axiom value itself.

```agda
point⁺ : ∀ f g v
       → evW (w⁺ (rise f)) (φ (evW (f ⨾⁺ g)) v) ≡ evW f (φ (evW g) v)
point⁺ f g Z =
  ev-w⁺ (rise f) Z ∙ ap (_+ rise f) (monus-zero (rise f))
point⁺ f g (S m) =
  ap (evW (w⁺ (rise f))) (ev-comp f g m)
  ∙ ev-w⁺ (rise f) (evW f (evW g m))
  ∙ le-monus-plus (rise f) (evW f (evW g m))
      (ev-mono-le (f .fst) (f .snd .fst) (w-inc f) Z (evW g m)
        Nat.lt.z<s)

defect⁺ : ∀ f g h → f ⨾⁺ (g ⨾⁻ h) ≡ w⁺ (rise f) ⨾⁺ ((f ⨾⁺ g) ⨾⁻ h)
defect⁺ f g h =
  ev-inj (f ⨾⁺ (g ⨾⁻ h)) (w⁺ (rise f) ⨾⁺ ((f ⨾⁺ g) ⨾⁻ h)) λ n →
    ev-mixR f g h n
    ∙ sym (point⁺ f g (evW h n))
    ∙ sym (ap (evW (w⁺ (rise f))) (ev-mixL f g h n))
    ∙ sym (ev-comp (w⁺ (rise f)) ((f ⨾⁺ g) ⨾⁻ h) n)
```

The trailing correction: for every triple, the left bracketing is
the right one cut against `w⁻ (zrunW h)` on the inside of the
negative hand. Below the plateau both sides vanish, and from the
plateau on the guard steps aside.

```agda
defect⁻ : ∀ f g h → (f ⨾⁺ g) ⨾⁻ h ≡ (f ⨾⁺ (g ⨾⁻ h)) ⨾⁻ w⁻ (zrunW h)
defect⁻ f g h =
  ev-inj ((f ⨾⁺ g) ⨾⁻ h) ((f ⨾⁺ (g ⨾⁻ h)) ⨾⁻ w⁻ (zrunW h)) point
  where
  k : Nat
  k = zrunW h

  P : Nat → Type
  P n = evW ((f ⨾⁺ g) ⨾⁻ h) n ≡ evW ((f ⨾⁺ (g ⨾⁻ h)) ⨾⁻ w⁻ k) n

  lo : ∀ n → n < k → P n
  lo n p =
    ev-mixL f g h n
    ∙ ap (φ (evW (f ⨾⁺ g)))
         (ev-zrun-lo (h .fst) (h .snd .fst) n p)
    ∙ sym ( ev-comp (φW (f ⨾⁺ (g ⨾⁻ h))) (w⁻ k) n
          ∙ ev-φ (f ⨾⁺ (g ⨾⁻ h)) (evW (w⁻ k) n)
          ∙ ap (φ (evW (f ⨾⁺ (g ⨾⁻ h)))) (ev-w⁻-lo k n p) )

  hi : ∀ m → P (k + m)
  hi m with ev-zrun-hi (h .fst) (h .snd .fst) (w-inc h)
             (k + m) (Nat.le-plus k m)
  ... | j , ej =
    ev-mixL f g h (k + m)
    ∙ ap (φ (evW (f ⨾⁺ g))) ej
    ∙ ev-comp f g j
    ∙ sym ( ev-comp (φW (f ⨾⁺ (g ⨾⁻ h))) (w⁻ k) (k + m)
          ∙ ev-φ (f ⨾⁺ (g ⨾⁻ h)) (evW (w⁻ k) (k + m))
          ∙ ap (φ (evW (f ⨾⁺ (g ⨾⁻ h)))) (ev-w⁻-hi k m)
          ∙ ev-mixR f g h (k + m)
          ∙ ap (λ v → evW f (φ (evW g) v)) ej )

  point : ∀ n → P n
  point n with Nat.cmp k n
  ... | inl q =
    subst P (sym (le-split k n q .snd)) (hi (le-split k n q .fst))
  ... | inr p = lo n p
```

## Triviality is the closure, exactly

The leading correction is a unit exactly when `rise f` is zero, and
that is exactly thunkability. Dually for the trailing correction
and linearity. So the defect words measure the two closures.

```agda
w⁺-nontrivial : ∀ a → ¬ (w⁺ (S a) ≡ ε̂)
w⁺-nontrivial a e =
  s≢z (sym (ev-w⁺ (S a) Z) ∙ ap (λ A → evW A Z) e)

w⁻-nontrivial : ∀ k → ¬ (w⁻ (S k) ≡ τ̂)
w⁻-nontrivial k e =
  z≢s (sym (ev-w⁻-lo (S k) Z Nat.lt.z<s) ∙ ap (λ A → evW A Z) e)

rise→thunkable : ∀ f → rise f ≡ Z → thunkable f
rise→thunkable f e g h =
  sym ( defect⁺ f g h
      ∙ ap (λ x → w⁺ x ⨾⁺ ((f ⨾⁺ g) ⨾⁻ h)) e
      ∙ comp-unitl ((f ⨾⁺ g) ⨾⁻ h) )

thunkable→rise : ∀ f → thunkable f → rise f ≡ Z
thunkable→rise f th =
  sym (ev-comp f δ̂ Z)
  ∙ ap (λ A → evW A Z) (sym (th ε̂ ε̂))
  ∙ ev-comp (φW (f ⨾⁺ ε̂)) ε̂ Z
  ∙ ev-φ (f ⨾⁺ ε̂) Z

⨾⁻-unitr : ∀ x → x ⨾⁻ τ̂ ≡ x
⨾⁻-unitr x = sym (comp-unitr (comp (φW x) τ̂)) ∙ act-τ x

run→linear : ∀ h → zrunW h ≡ Z → linear h
run→linear h e f g =
  defect⁻ f g h
  ∙ ap (λ x → (f ⨾⁺ (g ⨾⁻ h)) ⨾⁻ w⁻ x) e
  ∙ ⨾⁻-unitr (f ⨾⁺ (g ⨾⁻ h))

run-of-pos : ∀ p t → (Σ j ∶ Nat , ev p t Z ≡ S j) → zrun p t ≡ Z
run-of-pos []        Z     (j , e) = ex-falso (z≢s e)
run-of-pos []        (S t) _       = refl
run-of-pos (Z ∷ p)   t     (j , e) = ex-falso (z≢s e)
run-of-pos (S x ∷ p) t     _       = refl

pos-val : ∀ v → v ≡ S (evW δ̂ v) → Σ j ∶ Nat , v ≡ S j
pos-val Z     e = ex-falso (z≢s e)
pos-val (S u) e = u , refl

linear→run : ∀ h → linear h → zrunW h ≡ Z
linear→run h li =
  run-of-pos (h .fst) (h .snd .fst) (pos-val (evW h Z) q)
  where
  q : evW h Z ≡ S (evW δ̂ (evW h Z))
  q = sym (ev-comp ε̂ h Z ∙ ev-ε (evW h Z))
    ∙ ap (λ A → evW A Z) (li τ̂ ε̂)
    ∙ ev-comp τ̂ (ε̂ ⨾⁻ h) Z
    ∙ ap (evW τ̂) (ev-comp δ̂ h Z)
    ∙ ev-τ (evW δ̂ (evW h Z))
```

## No framing constant

Neither surviving placement admits one word for every triple.

```agda
no-uniform⁺ :
  ¬ (Σ w ∶ W , ((f g h : W) → f ⨾⁺ (g ⨾⁻ h) ≡ w ⨾⁺ ((f ⨾⁺ g) ⨾⁻ h)))
no-uniform⁺ (w , H) = z≢s (q ∙ ap (λ A → evW A Z) wv)
  where
  wv : w ≡ τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)
  wv = sym (comp-unitr w) ∙ sym (H τ̂ ε̂ ε̂)

  q : Z ≡ evW w Z
  q = ap (λ A → evW A Z) (H ε̂ ε̂ ε̂) ∙ ev-comp w δ̂ Z

no-uniform⁻ :
  ¬ (Σ w ∶ W , ((f g h : W) → (f ⨾⁺ g) ⨾⁻ h ≡ (f ⨾⁺ (g ⨾⁻ h)) ⨾⁻ w))
no-uniform⁻ (w , H) = probe (evW w (S Z)) q₁ q₂
  where
  q₁ : S Z ≡ evW δ̂ (evW w (S Z))
  q₁ = ap (λ A → evW A (S Z)) (H ε̂ ε̂ τ̂) ∙ ev-comp δ̂ w (S Z)

  q₂ : Z ≡ evW (φW (τ̂ ⨾⁺ (ε̂ ⨾⁻ δ̂))) (evW w (S Z))
  q₂ = ap (λ A → evW A (S Z)) (H τ̂ ε̂ δ̂)
     ∙ ev-comp (φW (τ̂ ⨾⁺ (ε̂ ⨾⁻ δ̂))) w (S Z)

  probe : ∀ u → S Z ≡ evW δ̂ u
        → Z ≡ evW (φW (τ̂ ⨾⁺ (ε̂ ⨾⁻ δ̂))) u → ⊥
  probe Z           e₁ e₂ = s≢z e₁
  probe (S Z)       e₁ e₂ = s≢z e₁
  probe (S (S Z))   e₁ e₂ = z≢s e₂
  probe (S (S (S j))) e₁ e₂ = z≢s (e₂ ∙ Nat.add.+suc j Z)
```

## The dead placements

Each remaining placement fails at a concrete triple, for every `w`.
The whole-word placements: `A1` is `R ≡ L ⨾⁺ w`, `A3` is
`R ≡ L ⨾⁻ w`, `A4` is `R ≡ w ⨾⁻ L`, `A5` is `L ≡ R ⨾⁺ w`, `A6` is
`L ≡ w ⨾⁺ R`, `A8` is `L ≡ w ⨾⁻ R`. The refuting triples are
`(τ̂ , τ̂ , ε̂)` where the left bracketing must supply the value one
and cannot, and `(τ̂ , ε̂ , ε̂)` where a flank forces zero against
one or pins two values of `w` at once.

```agda
miss₁ : ∀ v → S Z ≡ evW ((τ̂ ⨾⁺ τ̂) ⨾⁻ ε̂) v → ⊥
miss₁ Z     e = z≢s (sym e)
miss₁ (S j) e =
  z≢s (ap Nat.pred (e ∙ Nat.add.+suc j (S Z)) ∙ Nat.add.+suc j Z)

A1-refuted : ∀ w → ¬ (τ̂ ⨾⁺ (τ̂ ⨾⁻ ε̂) ≡ ((τ̂ ⨾⁺ τ̂) ⨾⁻ ε̂) ⨾⁺ w)
A1-refuted w e =
  miss₁ (evW w Z)
    (ap (λ A → evW A Z) e ∙ ev-comp ((τ̂ ⨾⁺ τ̂) ⨾⁻ ε̂) w Z)

miss₃ : ∀ v → S Z ≡ evW (φW ((τ̂ ⨾⁺ τ̂) ⨾⁻ ε̂)) v → ⊥
miss₃ Z         e = z≢s (sym e)
miss₃ (S Z)     e = z≢s (sym e)
miss₃ (S (S j)) e =
  z≢s (ap Nat.pred (e ∙ Nat.add.+suc j (S Z)) ∙ Nat.add.+suc j Z)

A3-refuted : ∀ w → ¬ (τ̂ ⨾⁺ (τ̂ ⨾⁻ ε̂) ≡ ((τ̂ ⨾⁺ τ̂) ⨾⁻ ε̂) ⨾⁻ w)
A3-refuted w e =
  miss₃ (evW w Z)
    (ap (λ A → evW A Z) e ∙ ev-comp (φW ((τ̂ ⨾⁺ τ̂) ⨾⁻ ε̂)) w Z)

A4-refuted : ∀ w → ¬ (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂) ≡ w ⨾⁻ ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂))
A4-refuted w e =
  s≢z ( ap (λ A → evW A Z) e
      ∙ ev-comp (φW w) ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂) Z
      ∙ ev-φ w Z )

miss₅ : ∀ v → Z ≡ evW (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)) v → ⊥
miss₅ Z     e = z≢s e
miss₅ (S j) e = z≢s (e ∙ Nat.add.+suc j Z)

A5-refuted : ∀ w → ¬ ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂ ≡ (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)) ⨾⁺ w)
A5-refuted w e =
  miss₅ (evW w Z)
    (ap (λ A → evW A Z) e ∙ ev-comp (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)) w Z)

A6-refuted : ∀ w → ¬ ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂ ≡ w ⨾⁺ (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)))
A6-refuted w e = z≢s (q₀ ∙ sym q₁)
  where
  q₀ : Z ≡ evW w (S Z)
  q₀ = ap (λ A → evW A Z) e ∙ ev-comp w (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)) Z

  q₁ : S Z ≡ evW w (S Z)
  q₁ = ap (λ A → evW A (S Z)) e ∙ ev-comp w (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)) (S Z)

A8-refuted : ∀ w → ¬ ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂ ≡ w ⨾⁻ (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)))
A8-refuted w e = z≢s (q₀ ∙ sym q₁)
  where
  R₁ : W
  R₁ = τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)

  q₀ : Z ≡ evW w Z
  q₀ = ap (λ A → evW A Z) e
     ∙ ev-comp (φW w) R₁ Z ∙ ev-φ w (S Z)

  q₁ : S Z ≡ evW w Z
  q₁ = ap (λ A → evW A (S Z)) e
     ∙ ev-comp (φW w) R₁ (S Z) ∙ ev-φ w (S Z)
```

The seam placements, at the same two triples. `S1` through `S4`
correct inside the right bracketing toward the left, and the head
of the leading edge forces a positive value where the left
bracketing is zero. `S5`, `S6`, `S8` correct inside the left
bracketing toward the right, and the guarding cut forces zero where
the right bracketing is one. `S7` reroutes the trailing edge and
misses the value one.

```agda
S1-refuted : ∀ w → ¬ ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂ ≡ (τ̂ ⨾⁺ w) ⨾⁺ (ε̂ ⨾⁻ ε̂))
S1-refuted w e =
  z≢s ( ap (λ A → evW A Z) e
      ∙ ev-comp (τ̂ ⨾⁺ w) (ε̂ ⨾⁻ ε̂) Z
      ∙ ev-comp τ̂ w Z
      ∙ ev-τ (evW w Z) )

S2-refuted : ∀ w → ¬ ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂ ≡ τ̂ ⨾⁺ ((w ⨾⁺ ε̂) ⨾⁻ ε̂))
S2-refuted w e =
  z≢s ( ap (λ A → evW A Z) e
      ∙ ev-comp τ̂ ((w ⨾⁺ ε̂) ⨾⁻ ε̂) Z
      ∙ ap (evW τ̂) (ev-comp (φW (w ⨾⁺ ε̂)) ε̂ Z ∙ ev-φ (w ⨾⁺ ε̂) Z)
      ∙ ev-τ Z )

S3-refuted : ∀ w → ¬ ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂ ≡ τ̂ ⨾⁺ (ε̂ ⨾⁻ (w ⨾⁺ ε̂)))
S3-refuted w e =
  z≢s ( ap (λ A → evW A Z) e
      ∙ ev-comp τ̂ (ε̂ ⨾⁻ (w ⨾⁺ ε̂)) Z
      ∙ ev-τ (evW (ε̂ ⨾⁻ (w ⨾⁺ ε̂)) Z) )

S4-refuted : ∀ w → ¬ ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂ ≡ τ̂ ⨾⁺ ((ε̂ ⨾⁺ w) ⨾⁻ ε̂))
S4-refuted w e =
  z≢s ( ap (λ A → evW A Z) e
      ∙ ev-comp τ̂ ((ε̂ ⨾⁺ w) ⨾⁻ ε̂) Z
      ∙ ap (evW τ̂) (ev-comp (φW (ε̂ ⨾⁺ w)) ε̂ Z ∙ ev-φ (ε̂ ⨾⁺ w) Z)
      ∙ ev-τ Z )

S5-refuted : ∀ w → ¬ (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂) ≡ (τ̂ ⨾⁺ (ε̂ ⨾⁺ w)) ⨾⁻ ε̂)
S5-refuted w e =
  s≢z ( ap (λ A → evW A Z) e
      ∙ ev-comp (φW (τ̂ ⨾⁺ (ε̂ ⨾⁺ w))) ε̂ Z
      ∙ ev-φ (τ̂ ⨾⁺ (ε̂ ⨾⁺ w)) Z )

S6-refuted : ∀ w → ¬ (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂) ≡ ((τ̂ ⨾⁺ w) ⨾⁺ ε̂) ⨾⁻ ε̂)
S6-refuted w e =
  s≢z ( ap (λ A → evW A Z) e
      ∙ ev-comp (φW ((τ̂ ⨾⁺ w) ⨾⁺ ε̂)) ε̂ Z
      ∙ ev-φ ((τ̂ ⨾⁺ w) ⨾⁺ ε̂) Z )

S7-refuted : ∀ w → ¬ (τ̂ ⨾⁺ (τ̂ ⨾⁻ ε̂) ≡ (τ̂ ⨾⁺ τ̂) ⨾⁻ (w ⨾⁺ ε̂))
S7-refuted w e =
  miss₁ (evW w Z)
    ( ap (λ A → evW A Z) e
    ∙ ev-comp (φW (τ̂ ⨾⁺ τ̂)) (w ⨾⁺ ε̂) Z
    ∙ ap (evW (φW (τ̂ ⨾⁺ τ̂))) (ev-comp w ε̂ Z) )

S8-refuted : ∀ w → ¬ (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂) ≡ ((τ̂ ⨾⁺ ε̂) ⨾⁻ w) ⨾⁻ ε̂)
S8-refuted w e =
  s≢z ( ap (λ A → evW A Z) e
      ∙ ev-comp (φW ((τ̂ ⨾⁺ ε̂) ⨾⁻ w)) ε̂ Z
      ∙ ev-φ ((τ̂ ⨾⁺ ε̂) ⨾⁻ w) Z )
```

## The grade forgets the defect

Both corrections carry the winding grade of their unit, so the
collapse onto the grade group erases them. That group is the
quotient in which the reverse bicyclic composite is the unit, i.e.
where the twists cancel two-sidedly. `bicyclic-persists` keeps the
word model itself on the other side of that collapse.

```agda
add-zero-r : ∀ x → add x (pos Z) ≡ x
add-zero-r (pos n)    = ap pos (Nat.add.unitr n)
add-zero-r (negsuc n) = refl

shift-w⁺ : ∀ a → shift (w⁺ a) ≡ pos Z
shift-w⁺ Z     = refl
shift-w⁺ (S a) =
  shift-⨾⁺ τ̂ (w⁺ a ⨾⁺ δ̂)
  ∙ ap (add (pos (S Z)))
       ( shift-⨾⁺ (w⁺ a) δ̂
       ∙ ap (λ z → add z (negsuc Z)) (shift-w⁺ a)
       ∙ zero-l (negsuc Z) )

shift-pow⁺τ : ∀ a → shift (pow⁺ a τ̂) ≡ pos a
shift-pow⁺τ Z     = refl
shift-pow⁺τ (S a) =
  shift-⨾⁺ τ̂ (pow⁺ a τ̂) ∙ ap (add (pos (S Z))) (shift-pow⁺τ a)

shift-guard : ∀ j x s → shift x ≡ pos s → shift (guard j x) ≡ (s ⊖ j)
shift-guard Z     x s e = e
shift-guard (S j) x s e =
  shift-⨾⁻ (guard j x) ε̂
  ∙ ap zpred (add-zero-r (shift (guard j x)) ∙ shift-guard j x s e)
  ∙ sym (⊖-pred s j)

shift-w⁻ : ∀ k → shift (w⁻ k) ≡ pos (S Z)
shift-w⁻ k =
  shift-guard k (pow⁺ (S k) τ̂) (S k) (shift-pow⁺τ (S k)) ∙ suc-⊖ k
  where
  suc-⊖ : ∀ k → (S k ⊖ k) ≡ pos (S Z)
  suc-⊖ Z     = refl
  suc-⊖ (S k) = suc-⊖ k
```

The direct form: the two bracketings of `associates` always agree in
grade, so no grade obstruction separates them, and the whole defect
lives in the fiber the grade forgets.

```agda
pred-succ-r : ∀ x → zpred (add x (pos (S Z))) ≡ x
pred-succ-r (pos n) =
  ap (λ m → zpred (pos m)) (Nat.add.+suc n Z)
  ∙ ap pos (Nat.add.unitr n)
pred-succ-r (negsuc Z)     = refl
pred-succ-r (negsuc (S m)) = refl

shift-associates : ∀ f g h
                 → shift ((f ⨾⁺ g) ⨾⁻ h) ≡ shift (f ⨾⁺ (g ⨾⁻ h))
shift-associates f g h =
  ap shift (defect⁻ f g h)
  ∙ shift-⨾⁻ (f ⨾⁺ (g ⨾⁻ h)) (w⁻ (zrunW h))
  ∙ ap (λ z → zpred (add (shift (f ⨾⁺ (g ⨾⁻ h))) z))
       (shift-w⁻ (zrunW h))
  ∙ pred-succ-r (shift (f ⨾⁺ (g ⨾⁻ h)))
```
