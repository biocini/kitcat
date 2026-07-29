Spike: the free framed point has a computable word model. The model
is decidable and set-truncated, with no quotient anywhere.

The construction runs over one object, and its edges are eventual
translations. An eventual translation is a function on the naturals
that adds a constant past some finite prefix. A descriptor `(p , t)`
presents one. The list `p` gives the values below its length. Past
the prefix, the value at offset `m` is `m + t`.

Two decidable constraints make that presentation canonical. Weak
monotonicity bounds each explicit value by the next value of the
denotation. Minimality forbids a last explicit value one below the
tail value, so no prefix shortens. Distinct descriptors then denote
distinct functions. Equality is decidable and the carrier is a set
by Hedberg, so the model needs no quotient.

Composition is normalization by evaluation into the monoid of
functions `Nat → Nat`. The composite of two eventual translations is
again one. Past the onset `length pB + (length pA ∸ tB)` the inner
descriptor has left both prefixes behind. Tabulate the composite
below that onset, take its value there as the new tail value, and
trim. The negative cut composes through the shifted composition `φ`,
where `φ f Z = Z` and `φ f (S n) = f n`.

Reflection surrounds the edge with its argument. The coterm half
composes on the inside, and the term half through `φ` on the
outside. The positive twist is the identity descriptor, and the
negative twist is the unit translation. Readback is the sandwich
collapse, since `φ` of the negative twist computes to the identity.

Stability comes from the hom sets. Evaluating a reflection
sandwiches the edge between the two twists, and the unit laws make
that injective. Both cuts are representable, and each invertibility
fiber has its own twist as centre. So `virtual-graph` and
`is-deductive-system` instantiate on the carrier.

The `associates` triple `(τ̂ , ε̂ , ε̂)` is refuted, so the
positive-then-negative mixed word does not reassociate in general.
The negative twist is not thunkable, and the identity is not linear.
The double twist inverts the negative twist on one side only, the
bicyclic pair. The descriptor shift `t ⊖ length p` is a ℤ-grading,
additive for the positive cut and decremented by `φ`. Every grade is
inhabited, and the double twist is the `+1` generator. The two
twists are distinct edges.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.BalancedWord where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat
open import Core.Data.List
open import Core.Data.Bool
open import Core.Data.Int
open import Core.Data.Dec using (Dec; DecEq; yes; no; module Dec)
open Dec using (hedberg)
open import Core.HLevel.Base using (Π-is-prop; Π-is-hlevel; Σ-is-hlevel)

open import Cat.Logic.Type
open import Cat.Logic.Base

open Nat
  using ( _+_; _-_; _<_; _≤_; s<s; suc; step
        ; _≤ᵇ_; _==ᵇ_; ≤ᵇ-sound; ≤ᵇ-complete; ==ᵇ-sound; ==ᵇ-complete
        ; le-plus; monus-max )
open List using (length)
open Bool using (not; and; _&&_; So; so-prop; so-and; so-fst; so-snd; so-absurd)
open Int
  using ( add; zsuc; zpred; zero-l; add-succ; add-pred
        ; _⊖_; ⊖-suc; ⊖-pred; ⊖-hom; cancel-l; ⊖-balance )
```

## The carrier

A descriptor `(p , t)` denotes the function that reads `p` below its
length and translates by climbing from `t` at the first tail
position. `ev` is that denotation, by structural recursion so the
tail case is definitional.

```agda
ev : List Nat → Nat → Nat → Nat
ev []      t n     = n + t
ev (x ∷ p) t Z     = x
ev (x ∷ p) t (S n) = ev p t n
```

Two decidable constraints cut the descriptors down to canonical
form: `incr?` demands each explicit value bounded by the next value
of the denotation, so the function is weakly monotone; `min?` demands
that the last explicit value not already sit one below the tail
value, so the prefix cannot be shortened.

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

The identity, the negative twist, and the double twist.

```agda
ε̂ τ̂ δ̂ : W
ε̂ = [] , Z , tt
τ̂ = [] , S Z , tt
δ̂ = Z ∷ [] , Z , tt
```

## Decidable equality and sets

Componentwise decidable equality; the constraint component is a
proposition, so it rides along by `is-prop→PathP`. `hedberg` then
makes each component a set, and the Σ closes up.

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
tail value, replacing the tail value by it. The recursion runs from
the front: the popped run is a suffix, so a kept entry freezes
everything before it.

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

The composite of two eventual translations is one: past the onset
`N = length pB + (length pA ∸ tB)` the inner descriptor has left both
prefixes behind. Tabulate the composite below the onset, take the
value at the onset as tail value, and trim.

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

`φ` guards a function by zero: the negative cut's engine. On
descriptors it prepends a zero to the prefix, except at the negative
twist itself, which collapses to the identity.

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

Pointwise equal denotations force equal descriptors: a pure
translation can never match a minimal nonempty prefix, so the prefixes
peel in lockstep and the tails agree at the end.

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
composition associates through `ev-inj`; the identity descriptor
absorbs through `Nat` unit laws.

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

## The instance

One object, `hom = W`. Reflection surrounds the edge with the
argument: the coterm half composes on the inside, the term half
composes through `φ` on the outside. The twists are `ε̂` and `τ̂`,
and readback is the sandwich collapse, since `φW τ̂` computes to
`ε̂`.

```agda
BW : virtual-graph 0ℓ 0ℓ
BW .virtual-graph.ob = ⊤
BW .virtual-graph.hom _ _ = W
BW .virtual-graph.reflect f γ =
  comp (comp (φW (γ .fst .snd)) f) (γ .snd .snd)
BW .virtual-graph.twist⁺ _ = ε̂
BW .virtual-graph.twist⁻ _ = τ̂
BW .virtual-graph.readback f = sandwich f

open virtual-graph BW using (reflect; coact-π; act-π; term; coterm)
open sequents BW using (eval)
```

## Stability

`eval ∘ reflect` sandwiches an edge between the two twists, so it is
injective by the unit laws; with `W` a set this makes `reflect` an
embedding at every pair of objects.

```agda
BW-stable : is-stable BW
BW-stable =
  stable-from-hom-sets BW (λ {x} {y} → W-set)
    (λ {x} {y} {m} {n} p → sym (sandwich m) ∙ p ∙ sandwich n)
```

## Both cuts are representable

The candidate representatives are `comp` and `cut⁻`; each reflects to
its composite judgment pointwise, through the three semantic laws of
`φ`.

```agda
cut⁺-path : ∀ a f g b n
  → evW (comp (comp (φW a) (comp f g)) b) n
  ≡ evW (comp (comp (φW a) f) (comp (comp ε̂ g) b)) n
cut⁺-path a f g b n =
    ev-comp (comp (φW a) (comp f g)) b n
  ∙ ev-comp (φW a) (comp f g) (evW b n)
  ∙ ap (evW (φW a)) (ev-comp f g (evW b n))
  ∙ ap (λ m → evW (φW a) (evW f m)) (sym step-r)
  ∙ sym (ev-comp (φW a) f (evW (comp (comp ε̂ g) b) n))
  ∙ sym (ev-comp (comp (φW a) f) (comp (comp ε̂ g) b) n)
  where
    step-r : evW (comp (comp ε̂ g) b) n ≡ evW g (evW b n)
    step-r = ap (λ u → evW (comp u b) n) (comp-unitl g) ∙ ev-comp g b n

ρ⁺ : ∀ f g → reflect (comp f g) ≡ composite⁺ BW f g
ρ⁺ f g = funext λ γ →
  ev-inj (comp (comp (φW (γ .fst .snd)) (comp f g)) (γ .snd .snd))
         (comp (comp (φW (γ .fst .snd)) f)
               (comp (comp ε̂ g) (γ .snd .snd)))
         (cut⁺-path (γ .fst .snd) f g (γ .snd .snd))

φ-two : ∀ a f m → φ (evW a) (φ (evW f) m)
                ≡ φ (evW (comp (comp (φW a) f) ε̂)) m
φ-two a f Z     = refl
φ-two a f (S m) = sym
  ( ev-comp (comp (φW a) f) ε̂ m
  ∙ ev-comp (φW a) f (m + Z)
  ∙ ev-φ a (evW f (m + Z))
  ∙ ap (λ k → φ (evW a) (evW f k)) (Nat.add.unitr m) )

cut⁻-path : ∀ a f g b n
  → evW (comp (comp (φW a) (cut⁻ f g)) b) n
  ≡ evW (comp (comp (φW (comp (comp (φW a) f) ε̂)) g) b) n
cut⁻-path a f g b n =
    ev-comp (comp (φW a) (cut⁻ f g)) b n
  ∙ ev-comp (φW a) (cut⁻ f g) (evW b n)
  ∙ ap (evW (φW a)) (ev-comp (φW f) g (evW b n))
  ∙ ap (evW (φW a)) (ev-φ f (evW g (evW b n)))
  ∙ ev-φ a (φ (evW f) (evW g (evW b n)))
  ∙ φ-two a f (evW g (evW b n))
  ∙ sym (ev-φ (comp (comp (φW a) f) ε̂) (evW g (evW b n)))
  ∙ sym (ev-comp (φW (comp (comp (φW a) f) ε̂)) g (evW b n))
  ∙ sym (ev-comp (comp (φW (comp (comp (φW a) f) ε̂)) g) b n)

ρ⁻ : ∀ f g → reflect (cut⁻ f g) ≡ composite⁻ BW f g
ρ⁻ f g = funext λ γ →
  ev-inj (comp (comp (φW (γ .fst .snd)) (cut⁻ f g)) (γ .snd .snd))
         (comp (comp (φW (comp (comp (φW (γ .fst .snd)) f) ε̂)) g)
               (γ .snd .snd))
         (cut⁻-path (γ .fst .snd) f g (γ .snd .snd))

BW-composable : is-composable BW
BW-composable .is-composable.contr⁺ f g =
  contr-from-stable BW BW-stable (composite⁺ BW f g) (comp f g , ρ⁺ f g)
BW-composable .is-composable.contr⁻ f g =
  contr-from-stable BW BW-stable (composite⁻ BW f g) (cut⁻ f g , ρ⁻ f g)
```

## The framing is invertible

Each fiber has the expected twist as centre, and any inhabitant is
pinned to it by evaluating the fiber path at the other twist's
axiom half; the path component lives in a set-valued function type,
so it rides along as a proposition.

```agda
Π⁻-set : is-set ((γ : coterm tt) → W)
Π⁻-set = Π-is-hlevel (S (S Z)) (λ _ → W-set)

Π⁺-set : is-set ((t : term tt) → W)
Π⁺-set = Π-is-hlevel (S (S Z)) (λ _ → W-set)

coactε : coact-π {tt} {tt} ε̂ ≡ snd
coactε = funext λ γ → comp-unitl (γ .snd)

actτ : act-π {tt} {tt} τ̂ ≡ snd
actτ = funext λ t → act-τ (t .snd)

q⁻ : (e : W) → coact-π {tt} {tt} e ≡ snd → ε̂ ≡ e
q⁻ e pe = sym (sym (sandwich e) ∙ happly pe (tt , ε̂))

q⁺ : (e : W) → act-π {tt} {tt} e ≡ snd → τ̂ ≡ e
q⁺ e pe = sym (sym (sandwich e) ∙ happly pe (tt , τ̂))

BW-invertible : is-invertible BW
BW-invertible .is-invertible.fiber⁻ x .center = ε̂ , coactε
BW-invertible .is-invertible.fiber⁻ x .paths (e , pe) i =
  q⁻ e pe i
  , is-prop→PathP (λ j → Π⁻-set (coact-π (q⁻ e pe j)) snd) coactε pe i
BW-invertible .is-invertible.fiber⁺ x .center = τ̂ , actτ
BW-invertible .is-invertible.fiber⁺ x .paths (e , pe) i =
  q⁺ e pe i
  , is-prop→PathP (λ j → Π⁺-set (act-π (q⁺ e pe j)) snd) actτ pe i

BW-deductive : is-deductive-system BW
BW-deductive .is-deductive-system.composable = BW-composable
BW-deductive .is-deductive-system.invertible = BW-invertible
```

## The tower

Chosen representatives for both cuts, with the two hands' words
written through `tower`.

```agda
BW-comp⁺ : is-composable⁺ BW
BW-comp⁺ f g = comp f g , ρ⁺ f g

BW-comp⁻ : is-composable⁻ BW
BW-comp⁻ f g = cut⁻ f g , ρ⁻ f g

open tower BW BW-stable BW-comp⁺ BW-comp⁻
  using (_⨾⁺_; _⨾⁻_; associates; thunkable; linear)
```

## The winding grade

The shift of a descriptor is its eventual translation defect
`t ∸ length p` as an integer. Trim preserves it, the positive cut
adds it, and `φ` decrements it: the ℤ-grading, with winding
`1 − 2·shift` and the double twist the `+1` winding generator.

```agda
shift : W → Int
shift A = A .snd .fst ⊖ length (A .fst)

tab-len : ∀ N (g : Nat → Nat) → length (tabulate N g) ≡ N
tab-len Z     g = refl
tab-len (S M) g = ap S (tab-len M (λ k → g (S k)))

pop-shift : ∀ x t' b → (So b → S x ≡ t')
  → (trim-pop x t' b .snd ⊖ length (trim-pop x t' b .fst)) ≡ (t' ⊖ S Z)
pop-shift x t' false h = refl
pop-shift x t' true  h = ap (_⊖ S Z) (h tt)

step-shift : ∀ x q t'
  → (trim-step x (q , t') .snd ⊖ length (trim-step x (q , t') .fst))
  ≡ (t' ⊖ S (length q))
step-shift x []      t' = pop-shift x t' (S x ==ᵇ t') (==ᵇ-sound (S x) t')
step-shift x (y ∷ q) t' = refl

trim-shift : ∀ p t
  → (trim p t .snd ⊖ length (trim p t .fst)) ≡ (t ⊖ length p)
trim-shift []      t = refl
trim-shift (x ∷ p) t =
    step-shift x (trim p t .fst) (trim p t .snd)
  ∙ ⊖-pred (trim p t .snd) (length (trim p t .fst))
  ∙ ap zpred (trim-shift p t)
  ∙ sym (⊖-pred t (length p))

gN-val : ∀ A B → gW A B (onset A B)
       ≡ ((B .snd .fst - length (A .fst)) + A .snd .fst)
gN-val A B =
  ap (evW A)
     ( ev-past (B .fst) (B .snd .fst) (length (A .fst) - B .snd .fst)
     ∙ monus-max (length (A .fst)) (B .snd .fst)
     ∙ Nat.max.comm (length (A .fst)) (B .snd .fst)
     ∙ sym (monus-max (B .snd .fst) (length (A .fst)))
     ∙ Nat.add.comm (B .snd .fst - length (A .fst)) (length (A .fst)) )
  ∙ ev-past (A .fst) (A .snd .fst) (B .snd .fst - length (A .fst))

shift-⨾⁺ : ∀ A B → shift (A ⨾⁺ B) ≡ add (shift A) (shift B)
shift-⨾⁺ A B =
    trim-shift (tabulate (onset A B) (gW A B)) (gW A B (onset A B))
  ∙ ap (gW A B (onset A B) ⊖_) (tab-len (onset A B) (gW A B))
  ∙ ap (_⊖ onset A B) (gN-val A B)
  ∙ ⊖-balance ((tB - lA) + tA) (onset A B) (tA + tB) (lA + lB) bal
  ∙ sym (⊖-hom tA lA tB lB)
  where
    lA = length (A .fst)
    tA = A .snd .fst
    lB = length (B .fst)
    tB = B .snd .fst

    bal : ((tB - lA) + tA) + (lA + lB) ≡ ((tA + tB) + (lB + (lA - tB)))
    bal =
        ap (_+ (lA + lB)) (Nat.add.comm (tB - lA) tA)
      ∙ sym (Nat.add.assoc tA (tB - lA) (lA + lB))
      ∙ ap (tA +_) (Nat.add.assoc (tB - lA) lA lB)
      ∙ ap (λ w → tA + (w + lB)) (monus-max tB lA)
      ∙ sym ( sym (Nat.add.assoc tA tB (lB + (lA - tB)))
            ∙ ap (tA +_) (Nat.add.assoc tB lB (lA - tB))
            ∙ ap (λ w → tA + (w + (lA - tB))) (Nat.add.comm tB lB)
            ∙ ap (tA +_) (sym (Nat.add.assoc lB tB (lA - tB)))
            ∙ ap (λ w → tA + (lB + w)) (Nat.add.comm tB (lA - tB))
            ∙ ap (λ w → tA + (lB + w)) (monus-max lA tB)
            ∙ ap (λ w → tA + (lB + w)) (Nat.max.comm lA tB)
            ∙ ap (tA +_) (Nat.add.comm lB (Nat.max tB lA)) )

shift-φ : ∀ A → shift (φW A) ≡ zpred (shift A)
shift-φ ([] , Z , c)       = refl
shift-φ ([] , S Z , c)     = refl
shift-φ ([] , S (S u) , c) = refl
shift-φ (x ∷ p , t , c)    = ⊖-pred t (S (length p))

shift-⨾⁻ : ∀ A B → shift (A ⨾⁻ B) ≡ zpred (add (shift A) (shift B))
shift-⨾⁻ A B =
    shift-⨾⁺ (φW A) B
  ∙ ap (λ z → add z (shift B)) (shift-φ A)
  ∙ add-pred (shift A) (shift B)

zeros : Nat → List Nat
zeros Z     = []
zeros (S n) = Z ∷ zeros n

zeros-can : ∀ n → So (can? (Z ∷ zeros n) Z)
zeros-can Z     = tt
zeros-can (S n) = zeros-can n

zeros-len : ∀ n → length (zeros n) ≡ n
zeros-len Z     = refl
zeros-len (S n) = ap S (zeros-len n)

shift-onto : ∀ z → Σ A ∶ W , shift A ≡ z
shift-onto (pos n)    = ([] , n , tt) , refl
shift-onto (negsuc n) = (Z ∷ zeros n , Z , zeros-can n)
                      , λ i → Z ⊖ S (zeros-len n i)
```

## The measurements

The `associates` triple `(τ̂ , ε̂ , ε̂)` computes to `ε̂` on the left
bracketing and to the descriptor `([1] , 1)` on the right, so mixed
words do not reassociate; in particular the negative twist is not
thunkable and the identity is not linear. The double twist kills the
negative twist on one side only, and the twists are distinct.

```agda
w-nil : W → Type
w-nil A = nil? (A .fst)

pos? : Nat → Type
pos? Z     = ⊥
pos? (S _) = ⊤

associates-refuted : ¬ associates τ̂ ε̂ ε̂
associates-refuted e = subst w-nil e tt

thunkable-refuted : ¬ thunkable τ̂
thunkable-refuted th = associates-refuted (th ε̂ ε̂)

linear-refuted : ¬ linear ε̂
linear-refuted li = associates-refuted (li τ̂ ε̂)

bicyclic-collapse : (δ̂ ⨾⁺ τ̂) ≡ ε̂
bicyclic-collapse = refl

bicyclic-persists : ¬ ((τ̂ ⨾⁺ δ̂) ≡ ε̂)
bicyclic-persists e = subst w-nil (sym e) tt

twist-distinct : ¬ (τ̂ ≡ ε̂)
twist-distinct e = subst (λ A → pos? (A .snd .fst)) e tt
```
