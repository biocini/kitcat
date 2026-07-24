Lane Biocini
July 2026

Countermodel: readback is independent structure. Over the one-object
graph with `hom = Int` and identity `0`, the embedding twisted by
negation still satisfies pull- and push-fiber contractibility, both
unit-action equivalences, idempotence of the derived identity
composite, and full interchange — negation is a bijection fixing `0`,
so everything phrased through the twisted composites survives. But
evaluation returns the negation of the embedded morphism, and
`neg 1 ≡ 1` is false in `Int`, so the readback law
`∀ f → ev (emb f) ≡ f` is refutable in this instance: none of the
listed data derives it.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.ReadbackTwist where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat.Type
import Core.Data.Nat.Properties as Nat
open import Core.Data.Int
open import Core.Equiv.Base using (is-equiv; id-equiv)
open import Core.HLevel.Base using (Π-is-hlevel)

open import Cat.Depreciated.Type

add = Int.add
neg = Int.negate
pn  = Int.add.pos-negsuc
```

## Integer kernel

Unit laws, involutivity of negation, and associativity of addition
by successor/predecessor induction over the `pos-negsuc` helper.

```agda
zero-l : ∀ x → add (pos Z) x ≡ x
zero-l (pos n)    = refl
zero-l (negsuc n) = refl

zero-r : ∀ x → add x (pos Z) ≡ x
zero-r (pos n)    = ap pos (Nat.add.unitr n)
zero-r (negsuc n) = refl

neg-neg : ∀ x → neg (neg x) ≡ x
neg-neg (pos Z)     = refl
neg-neg (pos (S n)) = refl
neg-neg (negsuc n)  = refl

neg-inj : ∀ x y → neg x ≡ neg y → x ≡ y
neg-inj x y p = sym (neg-neg x) ∙ ap neg p ∙ neg-neg y

zsuc : Int → Int
zsuc (pos n)        = pos (S n)
zsuc (negsuc Z)     = pos Z
zsuc (negsuc (S n)) = negsuc n

zpred : Int → Int
zpred (pos Z)     = negsuc Z
zpred (pos (S n)) = pos n
zpred (negsuc n)  = negsuc (S n)

pn-succ : ∀ m n → pn (S m) n ≡ zsuc (pn m n)
pn-succ Z     Z     = refl
pn-succ (S m) Z     = refl
pn-succ Z     (S n) = refl
pn-succ (S m) (S n) = pn-succ m n

pn-zero : ∀ n → zsuc (pn n Z) ≡ pos n
pn-zero Z     = refl
pn-zero (S n) = refl

succ-pn : ∀ n m → zsuc (pn n (S m)) ≡ pn n m
succ-pn Z     m     = refl
succ-pn (S n) Z     = pn-zero n
succ-pn (S n) (S m) = succ-pn n m

pred-pos : ∀ n → zpred (pos n) ≡ pn n Z
pred-pos Z     = refl
pred-pos (S n) = refl

pred-pn : ∀ m n → zpred (pn (S m) n) ≡ pn m n
pred-pn Z     Z     = refl
pred-pn (S m) Z     = refl
pred-pn Z     (S n) = refl
pred-pn (S m) (S n) = pred-pn m n

pred-pn-r : ∀ n m → zpred (pn n m) ≡ pn n (S m)
pred-pn-r Z     m     = refl
pred-pn-r (S n) Z     = pred-pos n
pred-pn-r (S n) (S m) = pred-pn-r n m

add-succ : ∀ m n → add (zsuc m) n ≡ zsuc (add m n)
add-succ (pos m)        (pos n)    = refl
add-succ (pos m)        (negsuc n) = pn-succ m n
add-succ (negsuc Z)     (pos n)    = sym (pn-zero n)
add-succ (negsuc Z)     (negsuc n) = refl
add-succ (negsuc (S m)) (pos n)    = sym (succ-pn n m)
add-succ (negsuc (S m)) (negsuc n) = refl

add-pred : ∀ m n → add (zpred m) n ≡ zpred (add m n)
add-pred (pos Z)     (pos n)    = sym (pred-pos n)
add-pred (pos Z)     (negsuc n) = refl
add-pred (pos (S m)) (pos n)    = refl
add-pred (pos (S m)) (negsuc n) = sym (pred-pn m n)
add-pred (negsuc m)  (pos n)    = sym (pred-pn-r n m)
add-pred (negsuc m)  (negsuc n) = refl

add-assoc : ∀ m n k → add m (add n k) ≡ add (add m n) k
add-assoc (pos Z) n k =
  zero-l (add n k) ∙ sym (ap (λ t → add t k) (zero-l n))
add-assoc (pos (S i)) n k =
  add-succ (pos i) (add n k)
  ∙ ap zsuc (add-assoc (pos i) n k)
  ∙ sym (add-succ (add (pos i) n) k)
  ∙ sym (ap (λ t → add t k) (add-succ (pos i) n))
add-assoc (negsuc Z) n k =
  (add-pred (pos Z) (add n k) ∙ ap zpred (zero-l (add n k)))
  ∙ sym (ap (λ t → add t k) (add-pred (pos Z) n ∙ ap zpred (zero-l n))
    ∙ add-pred n k)
add-assoc (negsuc (S i)) n k =
  add-pred (negsuc i) (add n k)
  ∙ ap zpred (add-assoc (negsuc i) n k)
  ∙ sym (add-pred (add (negsuc i) n) k)
  ∙ sym (ap (λ t → add t k) (add-pred (negsuc i) n))
```

## The twisted instance

One object, `hom = Int`, identity `0`; the embedding sends `g` to the
two-sided composite operator of `neg g`.

```agda
twist-graph : reflexive-graph 0ℓ 0ℓ
twist-graph .reflexive-graph.ob = ⊤
twist-graph .reflexive-graph.edge _ _ = Int
twist-graph .reflexive-graph.rx _ = pos Z

open virtual twist-graph

emb' : ∀ {x y} → hom x y → composite x y
emb' g γ = add (γ .fst .snd) (add (neg g) (γ .snd .snd))

open representable twist-graph emb'

composite-set : ∀ {x y} → is-set (composite x y)
composite-set = Π-is-hlevel (S (S Z)) (λ _ → Int.set)

ev-clean : (f : Int) → add (pos Z) (add (neg f) (pos Z)) ≡ neg f
ev-clean f = zero-l (add (neg f) (pos Z)) ∙ zero-r (neg f)
```

The fiber of `emb'` over any image point is contractible: `emb'` is
injective (reading at the identity context recovers `neg` of the
morphism, and `neg` is injective), and composites form a set.

```agda
emb'-image-contr : ∀ {x y} (k : hom x y) → is-contr (fiber emb' (emb' k))
emb'-image-contr k .center = k , refl
emb'-image-contr {x} {y} k .paths (j , p) i =
  q i , is-prop→PathP (λ i' → composite-set (emb' (q i')) (emb' k)) refl p i
  where
    q : k ≡ j
    q = sym (neg-inj j k
          (sym (ev-clean j) ∙ happly p (ov-idn x , un-idn y) ∙ ev-clean k))
```

Both one-sided composites against the twisted embedding collapse onto
the image of a single morphism, by the integer kernel alone.

```agda
▾-collapse : (f g : Int) → (emb' f ▾ g) ≡ emb' (neg (add (neg f) (neg g)))
▾-collapse f g = funext λ γ → inner (γ .fst .snd) (γ .snd .snd)
  where
    inner : ∀ a b
      → add a (add (neg f) (add (pos Z) (add (neg g) b)))
      ≡ add a (add (neg (neg (add (neg f) (neg g)))) b)
    inner a b = ap (add a)
      ( ap (add (neg f)) (zero-l (add (neg g) b))
      ∙ add-assoc (neg f) (neg g) b
      ∙ ap (λ t → add t b) (sym (neg-neg (add (neg f) (neg g)))) )

▴-collapse : (f g : Int) → (f ▴ emb' g) ≡ emb' (neg (add (neg f) (neg g)))
▴-collapse f g = funext λ γ → inner (γ .fst .snd) (γ .snd .snd)
  where
    inner : ∀ a b
      → add (add a (add (neg f) (pos Z))) (add (neg g) b)
      ≡ add a (add (neg (neg (add (neg f) (neg g)))) b)
    inner a b =
      ap (λ t → add (add a t) (add (neg g) b)) (zero-r (neg f))
      ∙ sym (add-assoc a (neg f) (add (neg g) b))
      ∙ ap (add a)
        ( add-assoc (neg f) (neg g) b
        ∙ ap (λ t → add t b) (sym (neg-neg (add (neg f) (neg g)))) )
```

## What the twist supports

Pull and push fibers contract, both unit actions are equivalences,
the derived identity composite is idempotent, and interchange holds
in full.

```agda
twist-pull-contr : (f g : Int) → is-contr (fiber emb' (emb' f ▾ g))
twist-pull-contr f g =
  subst (λ C → is-contr (fiber emb' C)) (sym (▾-collapse f g))
    (emb'-image-contr (neg (add (neg f) (neg g))))

twist-push-contr : (f g : Int) → is-contr (fiber emb' (f ▴ emb' g))
twist-push-contr f g =
  subst (λ C → is-contr (fiber emb' C)) (sym (▴-collapse f g))
    (emb'-image-contr (neg (add (neg f) (neg g))))

twist-eqvl : is-equiv (λ (b : Int) → pre (pos Z) b)
twist-eqvl =
  subst is-equiv (funext λ b → sym (zero-l (add (pos Z) b) ∙ zero-l b))
    id-equiv

twist-eqvr : is-equiv (λ (a : Int) → post (pos Z) a)
twist-eqvr = subst is-equiv (funext λ a → sym (zero-r a)) id-equiv

_⨾'_ : Int → Int → Int
f ⨾' g = twist-pull-contr f g .center .fst

twist-idem : (pos Z ⨾' pos Z) ≡ pos Z
twist-idem = refl

twist-interchange : (f g : Int) → (emb' f ▾ g) ≡ (f ▴ emb' g)
twist-interchange f g = ▾-collapse f g ∙ sym (▴-collapse f g)
```

## The kill

Evaluation at the identity context returns `neg f`, not `f`: any
readback law collapses `neg 1 ≡ 1`, and the constructors disagree.

```agda
is-negsuc : Int → Type
is-negsuc (pos _)    = ⊥
is-negsuc (negsuc _) = ⊤

twist-no-readback : ((f : Int) → ev (emb' f) ≡ f) → ⊥
twist-no-readback h = subst is-negsuc (h (pos (S Z))) tt
```
