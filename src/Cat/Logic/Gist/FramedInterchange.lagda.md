Spike: what does interchange cost in the presence of a twist?

Same carrier as an h-category, except that the term slot is filled by
`twist⁻` and the coterm slot by `twist⁺` — the twist and its inverse,
after balanced categories. Everything in the h-category derivation
transposes until its last step, which wants an edge that is a unit on
both sides; what stands in the way is the double twist.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.FramedInterchange where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding using (equiv→lc)
```

## The framed carrier

```agda
record framed o h : Type₊ (o ⊔ h) where
  field
    ob  : Type o
    hom : ob → ob → Type h

  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v

  argument : ob → ob → Type (o ⊔ h)
  argument x y = term x × coterm y

  conclusion : ∀ {x y} → argument x y → Type h
  conclusion γ = hom (γ .fst .fst) (γ .snd .fst)

  judgment : ob → ob → Type (o ⊔ h)
  judgment x y = (γ : argument x y) → conclusion γ

  field
    reflect : ∀ {x y} → hom x y → judgment x y
    twist⁺  : (x : ob) → hom x x
    twist⁻  : (x : ob) → hom x x

  var : (x : ob) → term x
  var x = x , twist⁻ x

  covar : (y : ob) → coterm y
  covar y = y , twist⁺ y

  eval : ∀ {x y} → judgment x y → hom x y
  eval {x} {y} α = α (var x , covar y)

  field
    readback : ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f

  coact-π : ∀ {x y} → hom x y → (k : coterm y) → hom x (k .fst)
  coact-π {x} f k = reflect f (var x , k)

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact f k = k .fst , coact-π f k

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (t , covar y)

  act : ∀ {x y} → hom x y → term x → term y
  act f t = t .fst , act-π f t

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect f (γ .fst , coact g (γ .snd))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect g (act f (γ .fst) , γ .snd)

  representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  representable = fiber reflect

  field
    cut⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (representable (composite⁺ f g))
    cut⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (representable (composite⁻ f g))
```

## One unit law per hand

```agda
module framing {o h} (F : framed o h) where
  open framed F public

  _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁺ g = cut⁺ f g .center .fst

  _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁻ g = cut⁻ f g .center .fst

  reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁺ g) ≡ composite⁺ f g
  reflect-⨾⁺ f g = cut⁺ f g .center .snd

  reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁻ g) ≡ composite⁻ f g
  reflect-⨾⁻ f g = cut⁻ f g .center .snd

  coact-covar : ∀ {x y} (f : hom x y) → coact f (covar y) ≡ (y , f)
  coact-covar {y = y} f = ap (y ,_) (readback f)

  act-var : ∀ {x y} (f : hom x y) → act f (var x) ≡ (x , f)
  act-var {x} f = ap (x ,_) (readback f)
```

A cut absorbs the twist filling its own slot, and only that one: the
positive cut closes its coterm at `twist⁺` and so is right-unital
there, the negative one closes its term at `twist⁻` and is left-unital
there. The other two laws have nothing to appeal to.

```agda
  unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ twist⁺ y ≡ f
  unitr⁺ {x} {y} f =
    sym (readback (f ⨾⁺ twist⁺ y))
    ∙ ap eval (reflect-⨾⁺ f (twist⁺ y))
    ∙ ap (λ c → reflect f (var x , c)) (coact-covar (twist⁺ y))
    ∙ readback f

  unitl⁻ : ∀ {x y} (f : hom x y) → twist⁻ x ⨾⁻ f ≡ f
  unitl⁻ {x} {y} f =
    sym (readback (twist⁻ x ⨾⁻ f))
    ∙ ap eval (reflect-⨾⁻ (twist⁻ x) f)
    ∙ ap (λ t → reflect f (t , covar y)) (act-var (twist⁻ x))
    ∙ readback f
```

## The two cuts differ by the double twist

Cutting the inverse against the twist lands on whichever of the two the
hand absorbs, so the two answers are `twist⁻` and `twist⁺`. Their gap
is `θ²`, and asking the cuts to agree is asking for it to vanish — the
twist becomes its own inverse.

```agda
  frame-⨾⁺ : (x : ob) → twist⁻ x ⨾⁺ twist⁺ x ≡ twist⁻ x
  frame-⨾⁺ x = unitr⁺ (twist⁻ x)

  frame-⨾⁻ : (x : ob) → twist⁻ x ⨾⁻ twist⁺ x ≡ twist⁺ x
  frame-⨾⁻ x = unitl⁻ (twist⁺ x)

  interchange→involutive
    : (∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁻ g ≡ f ⨾⁺ g)
    → (x : ob) → twist⁺ x ≡ twist⁻ x
  interchange→involutive X x =
    sym (frame-⨾⁻ x) ∙ X (twist⁻ x) (twist⁺ x) ∙ frame-⨾⁺ x
```

## Mixed associativity survives the frame

The two readings of a reflection meet here as well, so the whole of the
h-category derivation transposes except its last step.

```agda
  ⨾⁻-is-act : ∀ {w x y} (h : hom x y) (s : hom w x)
            → act-π h (w , s) ≡ s ⨾⁻ h
  ⨾⁻-is-act h s =
    (λ i → act-π h (act-var s (~ i)))
    ∙ sym (ap eval (reflect-⨾⁻ s h))
    ∙ readback (s ⨾⁻ h)

  ⨾⁺-is-coact : ∀ {x y z} (f : hom x y) (k : hom y z)
              → coact-π f (z , k) ≡ f ⨾⁺ k
  ⨾⁺-is-coact f k =
    (λ i → coact-π f (coact-covar k (~ i)))
    ∙ sym (ap eval (reflect-⨾⁺ f k))
    ∙ readback (f ⨾⁺ k)

  read⁺ : ∀ {u v w w'} (t : hom u v) (m : hom v w) (k : hom w w')
        → reflect m ((u , t) , (w' , k)) ≡ t ⨾⁻ (m ⨾⁺ k)
  read⁺ {u} {v} {w} {w'} t m k =
    (λ i → reflect m ((u , t) , coact-covar k (~ i)))
    ∙ (λ i → reflect-⨾⁺ m k (~ i) ((u , t) , covar w'))
    ∙ ⨾⁻-is-act (m ⨾⁺ k) t

  read⁻ : ∀ {u v w w'} (t : hom u v) (m : hom v w) (k : hom w w')
        → reflect m ((u , t) , (w' , k)) ≡ (t ⨾⁻ m) ⨾⁺ k
  read⁻ {u} {v} {w} {w'} t m k =
    (λ i → reflect m (act-var t (~ i) , (w' , k)))
    ∙ (λ i → reflect-⨾⁻ t m (~ i) (var u , (w' , k)))
    ∙ ⨾⁺-is-coact (t ⨾⁻ m) k

  mixed-assoc : ∀ {u v w w'} (t : hom u v) (m : hom v w) (k : hom w w')
              → t ⨾⁻ (m ⨾⁺ k) ≡ (t ⨾⁻ m) ⨾⁺ k
  mixed-assoc t m k = sym (read⁺ t m k) ∙ read⁻ t m k
```

## No edge is a unit on both sides

The last step of the derivation asks for an edge that is a left unit for
the positive cut and a right unit for the negative one. Mixed
associativity turns any such edge into interchange. So a reflexivity
edge serving both hands is available only where the twist is an
involution; otherwise the two missing laws are carried by two edges.

```agda
  two-sided→involutive
    : (n : (x : ob) → hom x x)
    → (∀ {x z} (k : hom x z) → n x ⨾⁺ k ≡ k)
    → (∀ {w x} (t : hom w x) → t ⨾⁻ n x ≡ t)
    → (x : ob) → twist⁺ x ≡ twist⁻ x
  two-sided→involutive n l r = interchange→involutive λ f g →
    sym (ap (f ⨾⁻_) (l g)) ∙ mixed-assoc f (n _) g ∙ ap (_⨾⁺ g) (r f)
```

## Does one cancellation imply the other?

Under `⨾⁻-is-act` and `⨾⁺-is-coact` the two cancellation axioms are the
two unit laws readback does not reach: `coact-π (twist⁺ x) ≡ snd` is
`twist⁺` being a left unit for the positive cut, and
`act-π (twist⁻ x) ≡ snd` is `twist⁻` being a right unit for the
negative one.

```agda
  act-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z) (t : term x)
         → act (f ⨾⁻ g) t ≡ act g (act f t)
  act-⨾⁻ f g t i = t .fst , reflect-⨾⁻ f g i (t , covar _)

  assoc⁻ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
         → f ⨾⁻ (g ⨾⁻ h) ≡ (f ⨾⁻ g) ⨾⁻ h
  assoc⁻ f g h =
    ap fst (is-contr→is-prop (cut⁻ (f ⨾⁻ g) h) a₁ (cut⁻ (f ⨾⁻ g) h .center))
    where
      a₁ : representable (composite⁻ (f ⨾⁻ g) h)
      a₁ = f ⨾⁻ (g ⨾⁻ h)
         , reflect-⨾⁻ f (g ⨾⁻ h)
         ∙ (λ i γ → reflect-⨾⁻ g h i (act f (γ .fst) , γ .snd))
         ∙ (λ i γ → reflect h (act-⨾⁻ f g (γ .fst) (~ i) , γ .snd))

  module cancellation
    (cancel⁻ : ∀ {x z} (k : hom x z) → twist⁺ x ⨾⁺ k ≡ k)
    where

    factor : ∀ {w x z} (t : hom w x) (k : hom x z)
           → t ⨾⁻ k ≡ (t ⨾⁻ twist⁺ x) ⨾⁺ k
    factor {x = x} t k =
      sym (ap (t ⨾⁻_) (cancel⁻ k)) ∙ mixed-assoc t (twist⁺ x) k

    twist⁺-absorbs : ∀ {w x} (t : hom w x)
                   → (t ⨾⁻ twist⁻ x) ⨾⁻ twist⁺ x ≡ t ⨾⁻ twist⁺ x
    twist⁺-absorbs {x = x} t =
      sym (assoc⁻ t (twist⁻ x) (twist⁺ x))
      ∙ ap (t ⨾⁻_) (frame-⨾⁻ x)

    cancel⁺-from-cancellable
      : (∀ {w x} {a b : hom w x} → a ⨾⁻ twist⁺ x ≡ b ⨾⁻ twist⁺ x → a ≡ b)
      → ∀ {w x} (t : hom w x) → t ⨾⁻ twist⁻ x ≡ t
    cancel⁺-from-cancellable ι t = ι (twist⁺-absorbs t)
```

So the second cancellation is not free: it reduces exactly to
right-cancellability of `_⨾⁻ twist⁺`, and nothing in readback or the
cuts supplies that.

## The inverse twist is determined by the twist

Fix only `twist⁺`. An edge satisfying readback against it is exactly a
left unit for the negative cut, and any right-cancellable endomorphism
makes such an edge unique — so `twist⁻` need not be posited. It is the
centre of a contractible fibre, and readback is that centre's defining
property rather than a field.

```agda
  readable : ∀ {x} → hom x x → Type (o ⊔ h)
  readable {x} r =
    ∀ {y} (f : hom x y) → reflect f ((x , r) , (y , twist⁺ y)) ≡ f

  readable→unitl⁻
    : ∀ {x} (r : hom x x) → readable r
    → ∀ {y} (f : hom x y) → r ⨾⁻ f ≡ f
  readable→unitl⁻ r P f = sym (⨾⁻-is-act f r) ∙ P f

  readable-unique
    : ∀ {x} (d : hom x x) → is-equiv (λ (g : hom x x) → g ⨾⁻ d)
    → (r r' : hom x x) → readable r → readable r' → r ≡ r'
  readable-unique d e r r' P P' = equiv→lc e
    (readable→unitl⁻ r P d ∙ sym (readable→unitl⁻ r' P' d))
```

The posited inverse inhabits it, so with any such `d` the fibre is
contractible.

```agda
  twist⁻-readable : ∀ {x} → readable (twist⁻ x)
  twist⁻-readable f = readback f
```
