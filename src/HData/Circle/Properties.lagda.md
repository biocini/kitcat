The winding equivalence: the loop space of the circle is the
integers, by encode–decode against the successor equivalence.

This module uses `--cubical` (not `--erased-cubical`) because it
needs `ua` and `ua-unglue` from `Core.Univalence` to build and read
the helix fibration.

The decode square rides `slide`: `loopⁿ` is defined so that its
successor cases are concatenations on the nose, making the square
from `loopⁿ (pred n)` to `loopⁿ n` over `loop` a `slide` at the
positive grades, its interval reversal at the negative grades, and a
direct interval term at zero. The only Kan filling in the module is
the one `hcom` correcting `decode`'s `pred`/`suc` round trip over the
loop; every face of its system reduces through the `PathP` boundary
types.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module HData.Circle.Properties where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-retr)
open import Core.Homotopy using (homotopy-natural)
open import Core.Transport.J using (J; subst)
open import Core.Transport.Base using (transport-refl; is-prop→PathP)
open import Core.Transport.Properties using (subst-∙; transport⁻-transport)
open import Core.HLevel.Base
  using (is-hlevel-is-prop; Π-is-prop; Π-is-hlevel; retract→is-hlevel)
open import Core.Equiv.Base using (_≃_; iso→equiv)
open import Core.Univalence using (ua; ua-β; ua-unglue)
open import Core.Data.Nat.Type using (Z; S)
open import Core.Data.Int using (Int; pos; negsuc; module Int)

open import Core.Data.Empty using (⊥)

open import HData.Circle.Type
open import HData.Circle.Base
open import HData.Circle.Mult
```

## The successor equivalence

```agda
suc : Int → Int
suc (pos n)        = pos (S n)
suc (negsuc Z)     = pos Z
suc (negsuc (S n)) = negsuc n

pred : Int → Int
pred (pos Z)     = negsuc Z
pred (pos (S n)) = pos n
pred (negsuc n)  = negsuc (S n)

suc-pred : ∀ n → suc (pred n) ≡ n
suc-pred (pos Z)     = refl
suc-pred (pos (S n)) = refl
suc-pred (negsuc n)  = refl

pred-suc : ∀ n → pred (suc n) ≡ n
pred-suc (pos n)        = refl
pred-suc (negsuc Z)     = refl
pred-suc (negsuc (S n)) = refl

suc-equiv : Int ≃ Int
suc-equiv = iso→equiv suc pred pred-suc suc-pred
```

## The helix and the winding number

```agda
helix : Circle → Type
helix = rec Int (ua suc-equiv)

loopⁿ : Int → base ≡ base
loopⁿ (pos Z)        = refl
loopⁿ (pos (S n))    = loopⁿ (pos n) ∙ loop
loopⁿ (negsuc Z)     = sym loop
loopⁿ (negsuc (S n)) = loopⁿ (negsuc n) ∙ sym loop

encode : (x : Circle) → base ≡ x → helix x
encode x p = subst helix p (pos Z)

winding : base ≡ base → Int
winding = encode base
```

## Decode

```agda
loopⁿ-square : (n : Int)
             → PathP (λ i → base ≡ loop i) (loopⁿ (pred n)) (loopⁿ n)
loopⁿ-square (pos Z) i j  = loop (i ∨ ~ j)
loopⁿ-square (pos (S n))  = slide (loopⁿ (pos n)) loop
loopⁿ-square (negsuc n) i = slide (loopⁿ (negsuc n)) (sym loop) (~ i)

decode : (x : Circle) → helix x → base ≡ x
decode base n = loopⁿ n
decode (loop i) y j = hcom (∂ i ∨ ∂ j) λ where
  k (k = i0) → loopⁿ-square (ua-unglue suc-equiv i y) i j
  k (i = i0) → loopⁿ (pred-suc y k) j
  k (i = i1) → loopⁿ y j
  k (j = i0) → base
  k (j = i1) → loop i
```

## The round trips and the equivalence

```agda
private
  subst-sym-loop : (m : Int) → subst helix (sym loop) m ≡ pred m
  subst-sym-loop m =
      sym (pred-suc (subst helix (sym loop) m))
    ∙ ap pred (sym (ua-β suc-equiv (subst helix (sym loop) m)))
    ∙ ap pred (transport⁻-transport (ua suc-equiv) m)

decode-encode : (x : Circle) (p : base ≡ x) → decode x (encode x p) ≡ p
decode-encode x p =
  J (λ x' p' → decode x' (encode x' p') ≡ p')
    (ap loopⁿ (transport-refl (pos Z))) p

winding-loopⁿ : (n : Int) → winding (loopⁿ n) ≡ n
winding-loopⁿ (pos Z) = transport-refl (pos Z)
winding-loopⁿ (pos (S n)) =
    subst-∙ helix (loopⁿ (pos n)) loop (pos Z)
  ∙ ua-β suc-equiv (subst helix (loopⁿ (pos n)) (pos Z))
  ∙ ap suc (winding-loopⁿ (pos n))
winding-loopⁿ (negsuc Z) = subst-sym-loop (pos Z)
winding-loopⁿ (negsuc (S n)) =
    subst-∙ helix (loopⁿ (negsuc n)) (sym loop) (pos Z)
  ∙ subst-sym-loop (subst helix (loopⁿ (negsuc n)) (pos Z))
  ∙ ap pred (winding-loopⁿ (negsuc n))

winding-equiv : (base ≡ base) ≃ Int
winding-equiv = iso→equiv winding loopⁿ (decode-encode base) winding-loopⁿ
```

## Nontriviality

The loop winds once, so it is not `refl`, and the rotation family is
not the constant family — the fact the instance work consumes: a
composite deformed pointwise by `rot` is genuinely deformed.

```agda
winding-loop : winding loop ≡ pos (S Z)
winding-loop = ua-β suc-equiv (pos Z)

private
  is-possuc : Int → Type
  is-possuc (pos Z)     = ⊥
  is-possuc (pos (S n)) = ⊤
  is-possuc (negsuc n)  = ⊥

loop-nontrivial : loop ≡ refl → ⊥
loop-nontrivial p =
  subst is-possuc
    (sym winding-loop ∙ ap winding p ∙ transport-refl (pos Z)) tt

rot-nontrivial : rot ≡ (λ x → refl) → ⊥
rot-nontrivial p = loop-nontrivial (happly p base)
```

## The groupoid structure

The loop space is a set — a retract of the integers along
`loopⁿ`/`winding` — and the circle is a groupoid by double induction
into the propositional h-level fibers.

```agda
Ω-is-set : is-set (base ≡ base)
Ω-is-set = retract→is-hlevel (S (S Z)) loopⁿ winding (decode-encode base) Int.set

Circle-is-groupoid : (x y : Circle) → is-set (x ≡ y)
Circle-is-groupoid =
  ind (λ x → (y : Circle) → is-set (x ≡ y))
    (ind (λ y → is-set (base ≡ y)) Ω-is-set
      (is-prop→PathP (λ i → is-hlevel-is-prop (S (S Z))) Ω-is-set Ω-is-set))
    (is-prop→PathP
      (λ i → Π-is-prop (λ y → is-hlevel-is-prop (S (S Z)))) _ _)
```

## The self-path evaluation equivalence

Evaluation at `base` identifies the self-path families with the loop
space. The inverse is conjugation through the multiplication —
`conj p x = ap (λ k → mult k x) p`, well-typed on the nose because
`mult base` is the definitional identity — and `conj loop` is `rot`
definitionally. The evaluation round trip is the `mult-unit-r`
homotopy applied along the path, and `ap-mult-base` computes it
directly; the family round trip is circle induction into fibers
that `Circle-is-groupoid` makes propositional.

```agda
conj : base ≡ base → (x : Circle) → x ≡ x
conj p x = ap (λ k → mult k x) p

conj-loop : conj loop ≡ rot
conj-loop = refl

ap-mult-base : (p : base ≡ base) → ap (λ k → mult k base) p ≡ p
ap-mult-base p =
  ap-retr mult-unit-r p ∙ Path.unitl (p ∙ refl) ∙ Path.unitr p

private
  conj-eval : (f : (x : Circle) → x ≡ x) → conj (f base) ≡ f
  conj-eval f = funext λ x →
    ind (λ x → conj (f base) x ≡ f x)
      (ap-mult-base (f base))
      (is-prop→PathP
        (λ i → Circle-is-groupoid (loop i) (loop i)
                 (conj (f base) (loop i)) (f (loop i)))
        (ap-mult-base (f base)) (ap-mult-base (f base)))
      x

self-path-equiv : ((x : Circle) → x ≡ x) ≃ (base ≡ base)
self-path-equiv = iso→equiv (λ f → f base) conj conj-eval ap-mult-base
```

## The multiplication coherences

`rot` is `mult`-equivariant, with a definitional base case
(`mult (loop i) r ≐ rot r i`) and a propositional loop case;
associativity follows by induction on the first argument, its loop
case the equivariance square transposed. Left translations cancel in
path families — evaluation at `base` is definitional one way, the
family round trip is circle induction into propositional fibers —
and the first slot is faithful: a path family between two left
translations is exactly a path of their representing points,
conjugated through the right unit law.

```agda
rot-mult : (y r : Circle) → ap (λ k → mult k r) (rot y) ≡ rot (mult y r)
rot-mult = ind (λ y → (r : Circle) → ap (λ k → mult k r) (rot y) ≡ rot (mult y r))
  (λ r → refl)
  (is-prop→PathP
    (λ i → Π-is-prop (λ r → Circle-is-groupoid _ _ _ _))
    (λ r → refl) (λ r → refl))

mult-assoc : (x y r : Circle) → mult (mult x y) r ≡ mult x (mult y r)
mult-assoc = ind (λ x → (y r : Circle) → mult (mult x y) r ≡ mult x (mult y r))
  (λ y r → refl)
  (λ i y r → transpose (rot-mult y r) i)

mult-l-cancel : {c c' : Circle → Circle}
  → ((l r : Circle) → mult l (c r) ≡ mult l (c' r)) ≃ ((r : Circle) → c r ≡ c' r)
mult-l-cancel {c} {c'} = iso→equiv to fro ret (λ p → refl)
  where
  to : ((l r : Circle) → mult l (c r) ≡ mult l (c' r)) → (r : Circle) → c r ≡ c' r
  to w = w base

  fro : ((r : Circle) → c r ≡ c' r) → (l r : Circle) → mult l (c r) ≡ mult l (c' r)
  fro p l r = ap (mult l) (p r)

  ret : ∀ w → fro (to w) ≡ w
  ret w = funext (ind (λ l → fro (to w) l ≡ w l) refl
    (is-prop→PathP
      (λ i → Π-is-hlevel (S (S Z)) (λ r → Circle-is-groupoid _ _) _ _)
      refl refl))

mult-faithful : (k m : Circle)
  → ((r : Circle) → mult k r ≡ mult m r) ≃ (k ≡ m)
mult-faithful k m = iso→equiv to fro ret sec
  where
  H : (t : Circle) → mult t base ≡ t
  H = mult-unit-r

  to : ((r : Circle) → mult k r ≡ mult m r) → k ≡ m
  to w = sym (H k) ∙ w base ∙ H m

  fro : k ≡ m → (r : Circle) → mult k r ≡ mult m r
  fro q r = ap (λ t → mult t r) q

  cancel-out : (v : k ≡ m) → sym (H k) ∙ (H k ∙ v ∙ sym (H m)) ∙ H m ≡ v
  cancel-out v =
      ap (sym (H k) ∙_)
         ( sym (Path.assoc (H k) (v ∙ sym (H m)) (H m))
         ∙ ap (H k ∙_) (sym (Path.assoc v (sym (H m)) (H m)))
         ∙ ap (λ z → H k ∙ v ∙ z) (Path.invl (H m))
         ∙ ap (H k ∙_) (Path.unitr v) )
    ∙ Path.assoc (sym (H k)) (H k) v
    ∙ ap (_∙ v) (Path.invl (H k))
    ∙ Path.unitl v

  cancel-in : (v : mult k base ≡ mult m base)
            → H k ∙ (sym (H k) ∙ v ∙ H m) ∙ sym (H m) ≡ v
  cancel-in v =
      ap (H k ∙_)
         ( sym (Path.assoc (sym (H k)) (v ∙ H m) (sym (H m)))
         ∙ ap (sym (H k) ∙_) (sym (Path.assoc v (H m) (sym (H m))))
         ∙ ap (λ z → sym (H k) ∙ v ∙ z) (Path.invr (H m))
         ∙ ap (sym (H k) ∙_) (Path.unitr v) )
    ∙ Path.assoc (H k) (sym (H k)) v
    ∙ ap (_∙ v) (Path.invr (H k))
    ∙ Path.unitl v

  sec : (q : k ≡ m) → to (fro q) ≡ q
  sec q = ap (λ z → sym (H k) ∙ z ∙ H m) (ap-retr H q) ∙ cancel-out q

  ret : (w : (r : Circle) → mult k r ≡ mult m r) → fro (to w) ≡ w
  ret w = funext (ind (λ r → fro (to w) r ≡ w r) ret-base
    (is-prop→PathP
      (λ i → Circle-is-groupoid _ _ _ _)
      ret-base ret-base))
    where
    ret-base : fro (to w) base ≡ w base
    ret-base = ap-retr H (to w) ∙ cancel-in (w base)
```

## Sliding the rotation across a path

`rot` is a self-path family, so it commutes past every path by
`homotopy-natural`. `slide-rot` reads that commutation as sliding the
inverse rotation from one endpoint of a path to the other.

```agda
slide-rot : {a b : Circle} (s : a ≡ b) → sym (rot a) ∙ s ≡ s ∙ sym (rot b)
slide-rot {a} {b} s =
    ap (sym (rot a) ∙_) (sym step)
  ∙ Path.lc (rot a) (s ∙ sym (rot b))
  where
    step : rot a ∙ (s ∙ sym (rot b)) ≡ s
    step = Path.assoc (rot a) s (sym (rot b))
         ∙ ap (_∙ sym (rot b))
              (sym (homotopy-natural {k = idfun Circle} {l = idfun Circle} rot s))
         ∙ Path.rc (rot b) s
```
