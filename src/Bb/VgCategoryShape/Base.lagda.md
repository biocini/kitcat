The theory an h-category carries.

Readback alone gives left-cancellability, the two evaluations at the
axiom, and one unit law per hand at `rx`. The cuts then give the two
readings of a reflection, and with them mixed associativity. The unit
identifies `rx`, completes the other two unit laws, and from there
interchange and stability are theorems rather than axioms.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VgCategoryShape.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.Path.Base
open import Core.Equiv.Base using (_≃_; is-equiv; module Equiv)
open import Core.Function.Embedding
  using (equiv→lc; image-fibers-contr→is-embedding)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (prop-inhabited→is-contr)

open import Bb.VgCategoryShape.Type
```

```agda
module hcat {o h} (M : hcategory o h) where
  open hcategory M public
```

## What readback alone gives

```agda
  reflect-lc : ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-lc {m = m} {n} p = sym (readback m) ∙ ap eval p ∙ readback n

  coact-covar : ∀ {x y} (f : hom x y) → coact f (covar y) ≡ (y , f)
  coact-covar {y = y} f = ap (y ,_) (readback f)

  act-var : ∀ {x y} (f : hom x y) → act f (var x) ≡ (x , f)
  act-var {x} f = ap (x ,_) (readback f)
```

Each hand absorbs `rx` on the side its own action closes. These are the
two laws that need no unit.

```agda
  unitr⁺rx : ∀ {x y} (f : hom x y) → f ⨾⁺ rx y ≡ f
  unitr⁺rx {x} {y} f =
    sym (readback (f ⨾⁺ rx y))
    ∙ ap eval (reflect-⨾⁺ f (rx y))
    ∙ ap (λ c → reflect f (var x , c)) (coact-covar (rx y))
    ∙ readback f

  unitl⁻rx : ∀ {x y} (f : hom x y) → rx x ⨾⁻ f ≡ f
  unitl⁻rx {x} {y} f =
    sym (readback (rx x ⨾⁻ f))
    ∙ ap eval (reflect-⨾⁻ (rx x) f)
    ∙ ap (λ t → reflect f (t , covar y)) (act-var (rx x))
    ∙ readback f
```

## Each composition is an action read at the axiom

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
```

## Two readings of one reflection, and mixed associativity

```agda
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

## The two halves of neutrality are the two hands

```agda
  le-is-coact : ∀ {x} (e : hom x x) {z} (k : hom x z)
              → coact-π (e ⨾⁻ e) (z , k) ≡ reflect e ((x , e) , (z , k))
  le-is-coact {x} e {z} k =
    (λ i → reflect-⨾⁻ e e i (var x , (z , k)))
    ∙ ap (λ t → reflect e (t , (z , k))) (act-var e)

  re-is-act : ∀ {x} (e : hom x x) {w} (g : hom w x)
            → act-π (e ⨾⁺ e) (w , g) ≡ reflect e ((w , g) , (x , e))
  re-is-act {x} e {w} g =
    (λ i → reflect-⨾⁺ e e i ((w , g) , covar x))
    ∙ ap (λ c → reflect e ((w , g) , c)) (coact-covar e)
```

## The unit identifies `rx`

The unit's own idempotence turns the first half of its neutrality into
an equivalence of the positive action, hence of `idn ⨾⁺ _`. Mixed
associativity then makes `idn` a left unit for the negative hand, as
`rx` already is, and the second half of neutrality cancels the two
against each other.

```agda
  idn-pre : ∀ {x z} → is-equiv (λ (k : hom x z) → coact-π idn (z , k))
  idn-pre {x} {z} =
    subst (λ t → is-equiv (λ (k : hom x z) → coact-π t (z , k))) idn-idem⁻
      (subst is-equiv (funext λ k → sym (le-is-coact idn k)) (idn-neutral .fst))

  idn-⨾⁺-equiv : ∀ {x z} → is-equiv (λ (k : hom x z) → idn ⨾⁺ k)
  idn-⨾⁺-equiv {x} {z} =
    subst is-equiv (funext λ k → ⨾⁺-is-coact idn k) idn-pre

  unitl⁻ : ∀ {x z} (m : hom x z) → idn ⨾⁻ m ≡ m
  unitl⁻ {x} {z} m =
      ap (idn ⨾⁻_) (sym p)
    ∙ mixed-assoc idn idn k
    ∙ ap (_⨾⁺ k) idn-idem⁻
    ∙ p
    where
      E : hom x z ≃ hom x z
      E = (λ k → idn ⨾⁺ k) , idn-⨾⁺-equiv

      k : hom x z
      k = Equiv.inv E m

      p : idn ⨾⁺ k ≡ m
      p = Equiv.counit E m

  post-eqv : ∀ {w x} → is-equiv (λ (g : hom w x) → g ⨾⁻ (idn ⨾⁺ idn))
  post-eqv {w} {x} =
    subst is-equiv
      (funext λ g → sym (re-is-act idn g) ∙ ⨾⁻-is-act (idn ⨾⁺ idn) g)
      (idn-neutral .snd)

  rx≡idn : (x : ob) → rx x ≡ idn {x}
  rx≡idn x = equiv→lc post-eqv
    (unitl⁻rx (idn ⨾⁺ idn) ∙ sym (unitl⁻ (idn ⨾⁺ idn)))
```

## The other two unit laws

```agda
  unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ idn ≡ f
  unitr⁺ {x} {y} f = ap (f ⨾⁺_) (sym (rx≡idn y)) ∙ unitr⁺rx f

  idem⁺ : ∀ {x} → idn {x} ⨾⁺ idn ≡ idn
  idem⁺ = unitr⁺ idn

  coact-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z) (k : coterm z)
           → coact (f ⨾⁺ g) k ≡ coact f (coact g k)
  coact-⨾⁺ f g k i = k .fst , reflect-⨾⁺ f g i (var _ , k)

  act-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z) (t : term x)
         → act (f ⨾⁻ g) t ≡ act g (act f t)
  act-⨾⁻ f g t i = t .fst , reflect-⨾⁻ f g i (t , covar _)

  idn-post : ∀ {w x} → is-equiv (λ (t : hom w x) → act-π idn (w , t))
  idn-post {w} {x} =
    subst (λ s → is-equiv (λ (t : hom w x) → act-π s (w , t))) idem⁺
      (subst is-equiv (funext λ g → sym (re-is-act idn g)) (idn-neutral .snd))

  absorb⁺ : ∀ {y} (k : coterm y) → coact idn k ≡ k
  absorb⁺ {y} k i = k .fst , π i
    where
      double : coact-π idn (coact idn k) ≡ coact-π idn k
      double =
        sym (ap snd (coact-⨾⁺ idn idn k))
        ∙ ap (λ t → coact t k .snd) idem⁺

      π : coact-π idn k ≡ k .snd
      π = equiv→lc idn-pre double

  absorb⁻ : ∀ {x} (t : term x) → act idn t ≡ t
  absorb⁻ {x} t i = t .fst , π i
    where
      double : act-π idn (act idn t) ≡ act-π idn t
      double =
        sym (ap snd (act-⨾⁻ idn idn t))
        ∙ ap (λ s → act s t .snd) idn-idem⁻

      π : act-π idn t ≡ t .snd
      π = equiv→lc idn-post double

  unitl⁺ : ∀ {x y} (f : hom x y) → idn ⨾⁺ f ≡ f
  unitl⁺ {x} {y} f =
    sym (readback (idn ⨾⁺ f))
    ∙ ap eval (reflect-⨾⁺ idn f)
    ∙ ap (λ c → reflect idn (var x , c)) (coact-covar f)
    ∙ ap snd (absorb⁺ (y , f))

  unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ idn ≡ f
  unitr⁻ {x} {y} f =
    sym (readback (f ⨾⁻ idn))
    ∙ ap eval (reflect-⨾⁻ f idn)
    ∙ ap (λ t → reflect idn (t , covar y)) (act-var f)
    ∙ ap snd (absorb⁻ (x , f))
```

## Interchange is a theorem

Mixed associativity at the unit collapses on both sides, and what is
left is the agreement of the two hands. Nothing is assumed.

```agda
  interchange : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁻ g ≡ f ⨾⁺ g
  interchange f g =
    sym (ap (f ⨾⁻_) (unitl⁺ g))
    ∙ mixed-assoc f idn g
    ∙ ap (_⨾⁺ g) (unitr⁻ f)

  judgment-interchange : ∀ {x y z} (f : hom x y) (g : hom y z)
                       → composite⁺ f g ≡ composite⁻ f g
  judgment-interchange f g =
    sym (reflect-⨾⁺ f g)
    ∙ ap reflect (sym (interchange f g))
    ∙ reflect-⨾⁻ f g
```

## Stability is a theorem

A cut against the unit is the bare reflection, so each cut's
contractible fibre is a contractible fibre over a point of the image,
and a map whose image fibres are contractible is an embedding.

```agda
  composite⁻-idn : ∀ {x y} (g : hom x y) → composite⁻ idn g ≡ reflect g
  composite⁻-idn g i γ = reflect g (absorb⁻ (γ .fst) i , γ .snd)

  composite⁺-idn : ∀ {x y} (f : hom x y) → composite⁺ f idn ≡ reflect f
  composite⁺-idn f i γ = reflect f (γ .fst , absorb⁺ (γ .snd) i)

  reflect-image-contr
    : ∀ {x y} (f : hom x y) → is-contr (representable (reflect f))
  reflect-image-contr f =
    subst (λ α → is-contr (representable α)) (composite⁻-idn f) (cut⁻ idn f)

  stable : is-stable
  stable {x} {y} = image-fibers-contr→is-embedding (reflect-image-contr {x} {y})

  contr-representable
    : ∀ {x y} (α : judgment x y)
    → representable α → is-contr (representable α)
  contr-representable α = prop-inhabited→is-contr (stable α)
```

## Associativity, per hand

```agda
  assoc⁺ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
         → (f ⨾⁺ g) ⨾⁺ h ≡ f ⨾⁺ (g ⨾⁺ h)
  assoc⁺ f g h =
    ap fst (is-contr→is-prop (cut⁺ f (g ⨾⁺ h)) a₁ (cut⁺ f (g ⨾⁺ h) .center))
    where
      a₁ : representable (composite⁺ f (g ⨾⁺ h))
      a₁ = (f ⨾⁺ g) ⨾⁺ h
         , reflect-⨾⁺ (f ⨾⁺ g) h
         ∙ (λ i γ → reflect-⨾⁺ f g i (γ .fst , coact h (γ .snd)))
         ∙ (λ i γ → reflect f (γ .fst , coact-⨾⁺ g h (γ .snd) (~ i)))

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
```
