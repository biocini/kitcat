Canonical descriptors for the eventual translations of the naturals.
An eventual translation adds a constant past some finite prefix. A
descriptor `(p , t)` presents one: the list `p` gives the values below
its length, and past the prefix the value at offset `m` is `m + t`.

Two decidable constraints cut the presentations down to canonical form.
Weak monotonicity bounds each explicit value by the next value of the
denotation. Minimality forbids a last explicit value one below the tail
value, so no prefix shortens. Distinct descriptors then denote distinct
functions, equality is decidable, and the descriptors form a set.

Composition is normalization by evaluation into the monoid of functions
`Nat → Nat`. The composite of two eventual translations is again one:
past the onset `length pB + (length pA ∸ tB)` the inner descriptor has
left both prefixes behind, so tabulating the composite below that onset
and taking its value there as the new tail value presents it. The
shifted composition `φ` guards a function by zero, with `φ f Z = Z` and
`φ f (S n) = f n`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Word.Carrier where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat
open import Core.Data.List
open import Core.Data.Bool
open import Core.Data.Dec using (Dec; DecEq; yes; no)
open import Core.HLevel.Base using (Σ-is-hlevel)

open Nat
  using ( _+_; _-_; _<_; _≤_; s<s; suc; step
        ; _≤ᵇ_; _==ᵇ_; ≤ᵇ-sound; ≤ᵇ-complete; ==ᵇ-sound; ==ᵇ-complete
        ; le-plus; monus-max )
open List using (length)
open Bool using (not; and; _&&_; So; so-prop; so-and; so-fst; so-snd; so-absurd)
```

## The carrier

A descriptor `(p , t)` denotes the function that reads `p` below its
length and translates by climbing from `t` at the first tail position.
`ev` is that denotation, by structural recursion so the tail case is
definitional.

```agda
ev : List Nat → Nat → Nat → Nat
ev []      t n     = n + t
ev (x ∷ p) t Z     = x
ev (x ∷ p) t (S n) = ev p t n
```

`incr?` demands each explicit value bounded by the next value of the
denotation, so the function is weakly monotone; `min?` demands that the
last explicit value not already sit one below the tail value, so the
prefix cannot be shortened.

```agda
incr? : List Nat → Nat → Bool
incr? []      t = true
incr? (x ∷ p) t = (x ≤ᵇ ev p t Z) && incr? p t

min? : List Nat → Nat → Bool
min? []          t = true
min? (x ∷ [])    t = not (S x ==ᵇ t)
min? (x ∷ y ∷ p) t = min? (y ∷ p) t

can? : List Nat → Nat → Bool
can? p t = incr? p t && min? p t

W : Type
W = Σ p ∶ List Nat , Σ t ∶ Nat , So (can? p t)

evW : W → Nat → Nat
evW A = ev (A .fst) (A .snd .fst)
```

The identity, the unit translation, and the double twist.

```agda
ε̂ τ̂ δ̂ : W
ε̂ = [] , Z , tt
τ̂ = [] , S Z , tt
δ̂ = Z ∷ [] , Z , tt
```

## Decidable equality and sets

Componentwise decidable equality; the constraint component is a
proposition, so it rides along by `is-prop→PathP`. Each component is a
set, and the Σ closes up.

```agda
nil? : List Nat → Type
nil? []      = ⊤
nil? (_ ∷ _) = ⊥

DecEq-W : DecEq W
DecEq-W (p , t , c) (q , u , d)
  with List.DecEq-List Nat.DecEq-Nat p q | Nat.DecEq-Nat t u
... | yes e | yes f =
  yes λ i → e i , f i
      , is-prop→PathP (λ j → so-prop (can? (e j) (f j))) c d i
... | yes e | no ¬f = no λ h → ¬f (ap (λ A → A .snd .fst) h)
... | no ¬e | yes f = no λ h → ¬e (ap fst h)
... | no ¬e | no ¬f = no λ h → ¬e (ap fst h)

W-set : is-set W
W-set = Σ-is-hlevel (S (S Z)) (List.set Nat.DecEq-Nat) λ p →
        Σ-is-hlevel (S (S Z)) Nat.set λ t →
        is-prop→is-set (so-prop (can? p t))

w-inc : (A : W) → So (incr? (A .fst) (A .snd .fst))
w-inc A = so-fst (incr? (A .fst) (A .snd .fst))
                 (min? (A .fst) (A .snd .fst)) (A .snd .snd)
```

## The denotation is an eventual translation

Past its prefix a descriptor translates: successor on the argument is
successor on the value, and at offset `m` past the prefix the value is
`m + t`. Under `incr?` the denotation is weakly monotone.

```agda
ev-tail : ∀ p t k → length p ≤ k → ev p t (S k) ≡ S (ev p t k)
ev-tail []      t k     q = refl
ev-tail (x ∷ p) t Z     q = ex-falso (Nat.lt.¬n<z (Nat.lt.peel Z q))
ev-tail (x ∷ p) t (S k) q = ev-tail p t k (Nat.lt.peel (S k) q)

ev-past : ∀ p t m → ev p t (length p + m) ≡ m + t
ev-past []      t m = refl
ev-past (x ∷ p) t m = ev-past p t m

ev-mono-suc : ∀ p t → So (incr? p t) → ∀ n → ev p t n ≤ ev p t (S n)
ev-mono-suc []      t s n     = step suc
ev-mono-suc (x ∷ p) t s Z     =
  ≤ᵇ-sound x (ev p t Z) (so-fst (x ≤ᵇ ev p t Z) (incr? p t) s)
ev-mono-suc (x ∷ p) t s (S n) =
  ev-mono-suc p t (so-snd (x ≤ᵇ ev p t Z) (incr? p t) s) n

ev-mono-lt : ∀ p t → So (incr? p t) → ∀ {j k} → j < k → ev p t j ≤ ev p t k
ev-mono-lt p t s {j} suc          = ev-mono-suc p t s j
ev-mono-lt p t s {j} (step {n} q) =
  Nat.le.cat (ev-mono-lt p t s q) (ev-mono-suc p t s n)

ev-mono-le : ∀ p t → So (incr? p t) → ∀ j k → j ≤ k → ev p t j ≤ ev p t k
ev-mono-le p t s j .j suc      = suc
ev-mono-le p t s j k (step q)  = ev-mono-lt p t s q
```

## Trim

`trim` pops the last prefix entry while it sits exactly one below the
tail value, replacing the tail value by it. The recursion runs from the
front: the popped run is a suffix, so a kept entry freezes everything
before it.

```agda
evp : List Nat × Nat → Nat → Nat
evp d = ev (d .fst) (d .snd)

trim-pop : Nat → Nat → Bool → List Nat × Nat
trim-pop x t' false .fst = x ∷ []
trim-pop x t' false .snd = t'
trim-pop x t' true  .fst = []
trim-pop x t' true  .snd = x

trim-step : Nat → List Nat × Nat → List Nat × Nat
trim-step x ([] , t')    = trim-pop x t' (S x ==ᵇ t')
trim-step x (y ∷ q , t') .fst = x ∷ y ∷ q
trim-step x (y ∷ q , t') .snd = t'

trim : List Nat → Nat → List Nat × Nat
trim []      t .fst = []
trim []      t .snd = t
trim (x ∷ p) t = trim-step x (trim p t)
```

Trim preserves the denotation and both constraints; minimality it
creates.

```agda
ev-pop : ∀ x t' b → (So b → S x ≡ t')
       → ∀ n → evp (trim-pop x t' b) n ≡ ev (x ∷ []) t' n
ev-pop x t' false h n     = refl
ev-pop x t' true  h Z     = refl
ev-pop x t' true  h (S m) = sym (Nat.add.+suc m x) ∙ ap (m +_) (h tt)

ev-step : ∀ x q t' n → evp (trim-step x (q , t')) n ≡ ev (x ∷ q) t' n
ev-step x []      t' n = ev-pop x t' (S x ==ᵇ t') (==ᵇ-sound (S x) t') n
ev-step x (y ∷ q) t' n = refl

ev-trim : ∀ p t n → evp (trim p t) n ≡ ev p t n
ev-trim []      t n     = refl
ev-trim (x ∷ p) t Z     = ev-step x (trim p t .fst) (trim p t .snd) Z
ev-trim (x ∷ p) t (S m) =
  ev-step x (trim p t .fst) (trim p t .snd) (S m) ∙ ev-trim p t m

min-pop : ∀ x t' b → b ≡ (S x ==ᵇ t')
        → So (min? (trim-pop x t' b .fst) (trim-pop x t' b .snd))
min-pop x t' true  e = tt
min-pop x t' false e = subst (λ z → So (not z)) e tt

min-step : ∀ x q t' → So (min? q t')
         → So (min? (trim-step x (q , t') .fst) (trim-step x (q , t') .snd))
min-step x []      t' s = min-pop x t' (S x ==ᵇ t') refl
min-step x (y ∷ q) t' s = s

min-trim : ∀ p t → So (min? (trim p t .fst) (trim p t .snd))
min-trim []      t = tt
min-trim (x ∷ p) t = min-step x (trim p t .fst) (trim p t .snd) (min-trim p t)

inc-pop : ∀ x t' b → So (x ≤ᵇ t')
        → So (incr? (trim-pop x t' b .fst) (trim-pop x t' b .snd))
inc-pop x t' true  s = tt
inc-pop x t' false s = so-and (x ≤ᵇ t') true s tt

inc-step : ∀ x q t' → So (x ≤ᵇ ev q t' Z) → So (incr? q t')
         → So (incr? (trim-step x (q , t') .fst) (trim-step x (q , t') .snd))
inc-step x []      t' hx hq = inc-pop x t' (S x ==ᵇ t') hx
inc-step x (y ∷ q) t' hx hq = so-and (x ≤ᵇ y) (incr? (y ∷ q) t') hx hq

inc-trim : ∀ p t → So (incr? p t)
         → So (incr? (trim p t .fst) (trim p t .snd))
inc-trim []      t s = tt
inc-trim (x ∷ p) t s =
  inc-step x (trim p t .fst) (trim p t .snd)
    (subst (λ v → So (x ≤ᵇ v)) (sym (ev-trim p t Z))
           (so-fst (x ≤ᵇ ev p t Z) (incr? p t) s))
    (inc-trim p t (so-snd (x ≤ᵇ ev p t Z) (incr? p t) s))
```

## Composition

Past the onset `N = length pB + (length pA ∸ tB)` the inner descriptor
has left both prefixes behind. Tabulate the composite below the onset,
take the value at the onset as tail value, and trim.

```agda
tabulate : Nat → (Nat → Nat) → List Nat
tabulate Z     g = []
tabulate (S n) g = g Z ∷ tabulate n (λ k → g (S k))

ev-tabulate : ∀ N g → (∀ k → N ≤ k → g (S k) ≡ S (g k))
            → ∀ n → ev (tabulate N g) (g N) n ≡ g n
ev-tabulate Z     g h Z     = refl
ev-tabulate Z     g h (S m) = ap S (ev-tabulate Z g h m) ∙ sym (h m Nat.lt.z<s)
ev-tabulate (S M) g h Z     = refl
ev-tabulate (S M) g h (S m) =
  ev-tabulate M (λ k → g (S k)) (λ k q → h (S k) (s<s q)) m

tab-head : ∀ M (g : Nat → Nat) → ev (tabulate M (λ k → g (S k))) (g (S M)) Z ≡ g (S Z)
tab-head Z     g = refl
tab-head (S M) g = refl

tabulate-incr : ∀ N g → (∀ k → g k ≤ g (S k))
              → So (incr? (tabulate N g) (g N))
tabulate-incr Z     g mono = tt
tabulate-incr (S M) g mono =
  so-and (g Z ≤ᵇ ev (tabulate M (λ k → g (S k))) (g (S M)) Z)
         (incr? (tabulate M (λ k → g (S k))) (g (S M)))
         (subst (λ v → So (g Z ≤ᵇ v)) (sym (tab-head M g))
                (≤ᵇ-complete (g Z) (g (S Z)) (mono Z)))
         (tabulate-incr M (λ k → g (S k)) (λ k → mono (S k)))

mk : (p : List Nat) (t : Nat) → So (incr? p t) → W
mk p t s .fst = trim p t .fst
mk p t s .snd .fst = trim p t .snd
mk p t s .snd .snd =
  so-and (incr? (trim p t .fst) (trim p t .snd))
         (min? (trim p t .fst) (trim p t .snd))
         (inc-trim p t s) (min-trim p t)

onset : W → W → Nat
onset A B = length (B .fst) + (length (A .fst) - B .snd .fst)

gW : W → W → Nat → Nat
gW A B k = evW A (evW B k)

gW-mono : ∀ A B k → gW A B k ≤ gW A B (S k)
gW-mono A B k =
  ev-mono-le (A .fst) (A .snd .fst) (w-inc A) (evW B k) (evW B (S k))
    (ev-mono-suc (B .fst) (B .snd .fst) (w-inc B) k)

gW-onset : ∀ A B → length (A .fst) ≤ evW B (onset A B)
gW-onset A B =
  subst (length (A .fst) ≤_) (sym eq)
        (Nat.max.≤l (length (A .fst)) (B .snd .fst))
  where
    eq : evW B (onset A B) ≡ Nat.max (length (A .fst)) (B .snd .fst)
    eq = ev-past (B .fst) (B .snd .fst) (length (A .fst) - B .snd .fst)
       ∙ monus-max (length (A .fst)) (B .snd .fst)

gW-trans : ∀ A B k → onset A B ≤ k → gW A B (S k) ≡ S (gW A B k)
gW-trans A B k q =
  ap (ev (A .fst) (A .snd .fst))
     (ev-tail (B .fst) (B .snd .fst) k
       (Nat.le.cat (le-plus (length (B .fst))
                            (length (A .fst) - B .snd .fst)) q))
  ∙ ev-tail (A .fst) (A .snd .fst) (evW B k)
      (Nat.le.cat (gW-onset A B)
        (ev-mono-le (B .fst) (B .snd .fst) (w-inc B) (onset A B) k q))

comp : W → W → W
comp A B = mk (tabulate (onset A B) (gW A B)) (gW A B (onset A B))
              (tabulate-incr (onset A B) (gW A B) (gW-mono A B))

ev-comp : ∀ A B n → evW (comp A B) n ≡ evW A (evW B n)
ev-comp A B n =
  ev-trim (tabulate (onset A B) (gW A B)) (gW A B (onset A B)) n
  ∙ ev-tabulate (onset A B) (gW A B) (gW-trans A B) n
```

## The shifted composition

`φ` guards a function by zero. On descriptors it prepends a zero to the
prefix, except at the unit translation, which collapses to the identity.

```agda
φ : (Nat → Nat) → Nat → Nat
φ f Z     = Z
φ f (S n) = f n

φW : W → W
φW ([] , Z , c)         = Z ∷ [] , Z , tt
φW ([] , S Z , c)       = [] , Z , tt
φW ([] , S (S u) , c)   = Z ∷ [] , S (S u) , tt
φW (x ∷ p , t , c)      = Z ∷ x ∷ p , t , c

ev-φ : ∀ A n → evW (φW A) n ≡ φ (evW A) n
ev-φ ([] , Z , c)       Z     = refl
ev-φ ([] , Z , c)       (S m) = refl
ev-φ ([] , S Z , c)     Z     = refl
ev-φ ([] , S Z , c)     (S m) = sym (Nat.add.+suc m Z)
ev-φ ([] , S (S u) , c) Z     = refl
ev-φ ([] , S (S u) , c) (S m) = refl
ev-φ (x ∷ p , t , c)    Z     = refl
ev-φ (x ∷ p , t , c)    (S m) = refl

cut⁻ : W → W → W
cut⁻ A B = comp (φW A) B
```

## Descriptors separate

Pointwise equal denotations force equal descriptors: a pure translation
can never match a minimal nonempty prefix, so the prefixes peel in
lockstep and the tails agree at the end.

```agda
push-min : ∀ t y q u → So (min? (y ∷ q) u)
         → (∀ n → n + t ≡ ev (y ∷ q) u n) → ⊥
push-min t y [] u s h =
  so-absurd (S y ==ᵇ u)
    (==ᵇ-complete (S y) u (ap S (sym (h Z)) ∙ h (S Z))) s
push-min t y (z ∷ q) u s h =
  push-min (S t) z q u s (λ n → Nat.add.+suc n t ∙ h (S n))

min-tail : ∀ x p t → So (min? (x ∷ p) t) → So (min? p t)
min-tail x []      t s = tt
min-tail x (y ∷ p) t s = s

desc-inj : ∀ pA tA pB tB
         → So (min? pA tA) → So (min? pB tB)
         → (∀ n → ev pA tA n ≡ ev pB tB n)
         → _≡_ {A = List Nat × Nat} (pA , tA) (pB , tB)
desc-inj [] tA [] tB mA mB h = λ i → [] , h Z i
desc-inj [] tA (y ∷ qB) tB mA mB h =
  ex-falso (push-min tA y qB tB mB h)
desc-inj (x ∷ qA) tA [] tB mA mB h =
  ex-falso (push-min tB x qA tA mA (λ n → sym (h n)))
desc-inj (x ∷ qA) tA (y ∷ qB) tB mA mB h = λ i →
  h Z i ∷ rest i .fst , rest i .snd
  where
    rest : _≡_ {A = List Nat × Nat} (qA , tA) (qB , tB)
    rest = desc-inj qA tA qB tB (min-tail x qA tA mA) (min-tail y qB tB mB)
                    (λ n → h (S n))

w-min : (A : W) → So (min? (A .fst) (A .snd .fst))
w-min A = so-snd (incr? (A .fst) (A .snd .fst))
                 (min? (A .fst) (A .snd .fst)) (A .snd .snd)

ev-inj : (A B : W) → (∀ n → evW A n ≡ evW B n) → A ≡ B
ev-inj A B h = λ i →
  Q i .fst , Q i .snd
  , is-prop→PathP (λ j → so-prop (can? (Q j .fst) (Q j .snd)))
                  (A .snd .snd) (B .snd .snd) i
  where
    Q : _≡_ {A = List Nat × Nat} (A .fst , A .snd .fst) (B .fst , B .snd .fst)
    Q = desc-inj (A .fst) (A .snd .fst) (B .fst) (B .snd .fst)
                 (w-min A) (w-min B) h
```

## Unit laws and associativity

Composition of functions is associative on the nose, so descriptor
composition associates through `ev-inj`; the identity descriptor absorbs
through `Nat` unit laws.

```agda
comp-assoc : ∀ f g h → comp (comp f g) h ≡ comp f (comp g h)
comp-assoc f g h = ev-inj (comp (comp f g) h) (comp f (comp g h)) λ n →
    ev-comp (comp f g) h n
  ∙ ev-comp f g (evW h n)
  ∙ sym (ap (evW f) (ev-comp g h n))
  ∙ sym (ev-comp f (comp g h) n)

comp-unitl : ∀ f → comp ε̂ f ≡ f
comp-unitl f = ev-inj (comp ε̂ f) f λ n →
  ev-comp ε̂ f n ∙ Nat.add.unitr (evW f n)

comp-unitr : ∀ f → comp f ε̂ ≡ f
comp-unitr f = ev-inj (comp f ε̂) f λ n →
  ev-comp f ε̂ n ∙ ap (evW f) (Nat.add.unitr n)

sandwich : ∀ f → comp (comp ε̂ f) ε̂ ≡ f
sandwich f = ap (λ u → comp u ε̂) (comp-unitl f) ∙ comp-unitr f

act-τ : ∀ a → comp (comp (φW a) τ̂) ε̂ ≡ a
act-τ a = ev-inj (comp (comp (φW a) τ̂) ε̂) a λ n →
    ev-comp (comp (φW a) τ̂) ε̂ n
  ∙ ev-comp (φW a) τ̂ (n + Z)
  ∙ ev-φ a ((n + Z) + S Z)
  ∙ ap (φ (evW a)) (Nat.add.+suc (n + Z) Z)
  ∙ ap (evW a) (Nat.add.unitr (n + Z) ∙ Nat.add.unitr n)
```
