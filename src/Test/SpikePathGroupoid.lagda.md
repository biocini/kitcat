Spike: is the theory inhabited?

Every tier is a contractibility statement, and an unsatisfiable one is
propositional for uninteresting reasons. The path groupoid on a type is
the candidate model: objects are points, edges are identifications, and
the two-sided embedding is `Core.Groupoid.Virtual`'s ternary
representable, which is an *equivalence* rather than merely an
embedding — so representability here is total, and the composability
tier holds at every judgment rather than only at the composites.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikePathGroupoid where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom)
open import Core.Path.Base
open import Core.Equiv.Base using (_≃_; is-equiv; eqv-fibers; iso→equiv)
open import Core.Equiv.Properties using (_∙e_; Π-contr-dom)
open import Core.Function.Embedding using (equiv→lc)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; Σ-is-prop; ×-is-hlevel; is-groupoid)
open import Core.Transport.Properties using (is-prop→is-set; prop-inhabited→is-contr)
open import Core.Groupoid.Virtual using (module yon-unbiased)

-- The carrier and the tiers, inlined: a spike in an in-development
-- layer carries its own copy of the data it probes, so a change to the
-- layer cannot silently retune it.

record virtual-graph o h : Type₊ (o ⊔ h) where
  field
    ob : Type o
    hom : ob → ob → Type h
    idn : (x : ob) → hom x x

  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v

  argument : ob → ob → Type (o ⊔ h)
  argument x y = term x × coterm y

  var : (a : ob) → term a
  var a = a , idn a

  covar : (y : ob) → coterm y
  covar y = y , idn y

  conclusion : ∀ {x y} → argument x y → Type h
  conclusion γ = hom (γ .fst .fst) (γ .snd .fst)

  judgment : ob → ob → Type (o ⊔ h)
  judgment x y = (γ : argument x y) → conclusion γ

  field
    reflect : ∀ {x y} → hom x y → judgment x y

module sequents {o h} (G : virtual-graph o h) where
  open virtual-graph G

  argue : ∀ {x y} → term x → coterm y → argument x y
  argue h k = h , k

  intro : ∀ {x y} → hom x y → term y
  intro {x} f = x , f

  elim : ∀ {x y} → hom x y → coterm x
  elim {y = y} f = y , f

  eval : ∀ {x y} → judgment x y → hom x y
  eval {x} {y} α = α (var x , covar y)

  is-representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  is-representable = fiber reflect

  normal : ∀ {x y} (f : hom x y) → is-representable (reflect f)
  normal f = f , refl

module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (argue (var x) γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (argue t (covar y))

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact {x} f e = elim (reflect f (argue (var x) e))

  act : ∀ {x y} → hom x y → term x → term y
  act {y = y} f t = intro (reflect f (argue t (covar y)))

  inj⁻ : ∀ {x y z} → judgment x y → hom y z → judgment x z
  inj⁻ α p γ = α (argue (γ .fst) (coact p (γ .snd)))

  inj⁺ : ∀ {x y z} → hom x y → judgment y z → judgment x z
  inj⁺ p β γ = β (argue (act p (γ .fst)) (γ .snd))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g = inj⁻ (reflect f) g

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g = inj⁺ f (reflect g)

  readback : Type (o ⊔ h)
  readback = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f

  record is-composable : Type (o ⊔ h) where
    field
      contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → is-contr (is-representable (composite⁻ f g))
      contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → is-contr (is-representable (composite⁺ f g))

    _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾⁻ g = contr⁻ f g .center .fst

    _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾⁺ g = contr⁺ f g .center .fst

    reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → reflect (f ⨾⁻ g) ≡ composite⁻ f g
    reflect-⨾⁻ f g = contr⁻ f g .center .snd

    reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → reflect (f ⨾⁺ g) ≡ composite⁺ f g
    reflect-⨾⁺ f g = contr⁺ f g .center .snd

    act-⨾⁺ : ∀ {x y z} (p : hom x y) (q : hom y z) (t : term x)
           → act (p ⨾⁺ q) t ≡ act q (act p t)
    act-⨾⁺ {z = z} p q t i = t .fst , reflect-⨾⁺ p q i (argue t (covar z))

    coact-⨾⁻ : ∀ {x y z} (p : hom x y) (q : hom y z) (e : coterm z)
             → coact (p ⨾⁻ q) e ≡ coact p (coact q e)
    coact-⨾⁻ {x} p q e i = e .fst , reflect-⨾⁻ p q i (argue (var x) e)

  record is-unital : Type (o ⊔ h) where
    field
      unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
      unit-fiber⁺ : ∀ x → is-contr (fiber (act-π   {x} {x}) snd)

    unit⁻ unit⁺ : ∀ x → hom x x
    unit⁻ x = unit-fiber⁻ x .center .fst
    unit⁺ x = unit-fiber⁺ x .center .fst

    unit⁻-unique-pt : ∀ x (e : hom x x)
                    → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ unit⁻ x
    unit⁻-unique-pt x e p = sym (ap fst (unit-fiber⁻ x .paths (e , funext p)))

    unit⁺-unique-pt : ∀ x (e : hom x x)
                    → (∀ t → act-π e t ≡ t .snd) → e ≡ unit⁺ x
    unit⁺-unique-pt x e p = sym (ap fst (unit-fiber⁺ x .paths (e , funext p)))

    unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
    unit⁻-absorb x γ i = unit-fiber⁻ x .center .snd i γ

    unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
    unit⁺-absorb x t i = unit-fiber⁺ x .center .snd i t

  module _ (U : is-unital) where
    open is-unital U

    flank⁻-of : ∀ x → eval (reflect (unit⁻ x)) ≡ unit⁻ x
              → eval (reflect (idn x)) ≡ idn x
    flank⁻-of x p =
      ap (λ e → coact-π e (covar x)) (sym (sym p ∙ unit⁻-absorb x (covar x)))
      ∙ unit⁻-absorb x (covar x)

    flank⁺-of : ∀ x → eval (reflect (unit⁺ x)) ≡ unit⁺ x
              → eval (reflect (idn x)) ≡ idn x
    flank⁺-of x p =
      ap (λ e → act-π e (var x)) (sym (sym p ∙ unit⁺-absorb x (var x)))
      ∙ unit⁺-absorb x (var x)

    absorb-coh : readback → Type (o ⊔ h)
    absorb-coh u =
      ∀ x → (u (idn x) ≡ flank⁻-of x (u (unit⁻ x)))
          × (u (idn x) ≡ flank⁺-of x (u (unit⁺ x)))

    is-stable : Type (o ⊔ h)
    is-stable = is-contr (Σ {A = readback} absorb-coh)

  record is-deductive-system : Type (o ⊔ h) where
    field
      composable : is-composable
      unital     : is-unital
      stable     : is-stable unital
```

## The virtual graph

`reflect` is the ternary representable with its four curried arguments
read off one argument pair.

```agda
module _ {u} (A : Type u) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  emb-equiv : {x y : A} → is-equiv (emb {x} {y})
  emb-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob        = A
  PG .virtual-graph.hom x y   = x ≡ y
  PG .virtual-graph.idn x     = refl
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  open virtual-graph PG
  open sequents PG
```

## Representability is total

Currying the argument pair is an equivalence by η, so `reflect` is one
too. Every judgment is represented, uniquely — not only the composites.

```agda
  curry≃ : ∀ {x y} → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z) ≃ judgment x y
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  reflect-equiv : ∀ {x y} → is-equiv (reflect {x} {y})
  reflect-equiv = ((emb , emb-equiv) ∙e curry≃) .snd

  representable-contr
    : ∀ {x y} (α : judgment x y) → is-contr (is-representable α)
  representable-contr = eqv-fibers reflect-equiv
```

## Composability

Handed over from totality.

```agda
  PG-composable : is-composable PG
  PG-composable .is-composable.contr⁻ f g = representable-contr (composite⁻ PG f g)
  PG-composable .is-composable.contr⁺ f g = representable-contr (composite⁺ PG f g)
```

## Unitality

Terms and coterms are the based path spaces, so each is contractible
with its axiom half as centre. That makes each hand's action map a
composite of equivalences — `reflect`, then currying, then evaluation
at a contractible domain's centre — so its fiber over `snd` is
contractible without any further argument.

```agda
  term-contr : ∀ x → is-contr (term x)
  term-contr x .center = var x
  term-contr x .paths (w , p) i = p (~ i) , λ j → p (~ i ∨ j)

  coterm-contr : ∀ y → is-contr (coterm y)
  coterm-contr y .center = covar y
  coterm-contr y .paths (v , p) i = p i , λ j → p (i ∧ j)

  slot≃ : ∀ {x y}
        → judgment x y ≃ ((t : term x) (γ : coterm y) → hom (t .fst) (γ .fst))
  slot≃ = iso→equiv (λ α t γ → α (t , γ)) (λ Φ δ → Φ (δ .fst) (δ .snd))
                    (λ _ → refl) (λ _ → refl)

  slot-swap≃ : ∀ {x y}
             → judgment x y ≃ ((γ : coterm y) (t : term x) → hom (t .fst) (γ .fst))
  slot-swap≃ = iso→equiv (λ α γ t → α (t , γ)) (λ Φ δ → Φ (δ .snd) (δ .fst))
                         (λ _ → refl) (λ _ → refl)

  coact-π-equiv : ∀ x → is-equiv (coact-π PG {x} {x})
  coact-π-equiv x =
    ((reflect , reflect-equiv) ∙e slot≃ ∙e Π-contr-dom (term-contr x)) .snd

  act-π-equiv : ∀ x → is-equiv (act-π PG {x} {x})
  act-π-equiv x =
    ((reflect , reflect-equiv) ∙e slot-swap≃ ∙e Π-contr-dom (coterm-contr x)) .snd

  PG-unital : is-unital PG
  PG-unital .is-unital.unit-fiber⁻ x = eqv-fibers (coact-π-equiv x) snd
  PG-unital .is-unital.unit-fiber⁺ x = eqv-fibers (act-π-equiv x) snd
```

## Readback

Evaluation at the axiom is the ternary composite with both flanks
reflexive, which is `pcom`'s unit law.

```agda
  PG-readback : readback PG
  PG-readback f = pcom.unit f
```

## The chosen edge is the unit, untruncated

No hypothesis on `A`. Reflexivity absorbs on each hand by `pcom`'s two
idempotence laws, and the unit tier's uniqueness identifies it with the
projected unit.

```agda
  open is-unital PG-unital

  idn-absorbs⁻ : ∀ x (γ : coterm x) → coact-π PG (idn x) γ ≡ γ .snd
  idn-absorbs⁻ x γ = pcom.ideml (γ .snd)

  idn-absorbs⁺ : ∀ x (t : term x) → act-π PG (idn x) t ≡ t .snd
  idn-absorbs⁺ x t = pcom.idemr (t .snd)

  idn-is-unit⁻ : ∀ x → idn x ≡ unit⁻ x
  idn-is-unit⁻ x = unit⁻-unique-pt x (idn x) (idn-absorbs⁻ x)

  idn-is-unit⁺ : ∀ x → idn x ≡ unit⁺ x
  idn-is-unit⁺ x = unit⁺-unique-pt x (idn x) (idn-absorbs⁺ x)
```

## Associativity, free from totality

Because `reflect` is an equivalence here, left-cancellability is
immediate rather than a consequence of the unit laws: the fiber over a
reflection contains both the normal point and any competitor. The
engine of `Test.SpikeReflectFiber` recovers this from composability and
the flank absorptions in the general case, where representability is
only propositional.

```agda
  open is-composable PG-composable

  reflect-lc : ∀ {x y} {f g : hom x y} → reflect f ≡ reflect g → f ≡ g
  reflect-lc {f = f} {g} p =
    ap fst (sym (c .paths (f , p)) ∙ c .paths (normal g))
    where c = representable-contr (reflect g)

  composite⁻-assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
    → composite⁻ PG (f ⨾⁻ g) h ≡ composite⁻ PG f (g ⨾⁻ h)
  composite⁻-assoc f g h = funext λ γ →
    (λ i → reflect-⨾⁻ f g i (argue (γ .fst) (coact PG h (γ .snd))))
    ∙ (λ i → reflect f (argue (γ .fst) (coact-⨾⁻ g h (γ .snd) (~ i))))

  assoc⁻ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
         → (f ⨾⁻ g) ⨾⁻ h ≡ f ⨾⁻ (g ⨾⁻ h)
  assoc⁻ f g h = reflect-lc
    ( reflect-⨾⁻ (f ⨾⁻ g) h
    ∙ composite⁻-assoc f g h
    ∙ sym (reflect-⨾⁻ f (g ⨾⁻ h)) )

  composite⁺-assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
    → composite⁺ PG f (g ⨾⁺ h) ≡ composite⁺ PG (f ⨾⁺ g) h
  composite⁺-assoc f g h = funext λ γ →
    (λ i → reflect-⨾⁺ g h i (argue (act PG f (γ .fst)) (γ .snd)))
    ∙ (λ i → reflect h (argue (act-⨾⁺ f g (γ .fst) (~ i)) (γ .snd)))

  assoc⁺ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
         → f ⨾⁺ (g ⨾⁺ h) ≡ (f ⨾⁺ g) ⨾⁺ h
  assoc⁺ f g h = reflect-lc
    ( reflect-⨾⁺ f (g ⨾⁺ h)
    ∙ composite⁺-assoc f g h
    ∙ sym (reflect-⨾⁺ (f ⨾⁺ g) h) )
```

## What stability is asking

Readback is quantified over an edge and its far endpoint together —
that is, over a coterm — and coterms here are contractible. So a
readback family is exactly its values at the reflexive edges, and no
more.

```agda
  rb-fam : ∀ x → coterm x → Type u
  rb-fam x c = eval (reflect (c .snd)) ≡ c .snd

  readback≃ : ∀ x → ((c : coterm x) → rb-fam x c) ≃ rb-fam x (covar x)
  readback≃ x = Π-contr-dom {B = rb-fam x} (coterm-contr x)
```

The codomain is `eval (reflect (idn x)) ≡ idn x`: a path in `x ≡ x`
between the evaluation of the reflected reflexive edge and that edge.

So `readback` is a family of paths in `x ≡ x`, one per point, between
`eval (reflect refl)` and `refl`. That type is a proposition exactly
when each `x ≡ x` is a set — when `A` is a groupoid, `is-hlevel 3` in
the library's numbering — and not in general. Above that,
`is-stable`'s contractibility cannot come from the readback component
alone; the flank coherence has to pin it, and the coherence reads the
family only at the endomorphisms `idn x`, `unit⁻ x` and `unit⁺ x`.

Rigidity cuts the other way and is worth recording, since it is what
makes the endomorphism-only reading of the coherence less weak than it
looks here: two readback families agreeing at every reflexive edge are
equal, by based path induction.

```agda
  readback-rigid
    : (u v : ∀ x (c : coterm x) → rb-fam x c)
    → (∀ x → u x (covar x) ≡ v x (covar x))
    → ∀ x → u x ≡ v x
  readback-rigid u v agree x = equiv→lc (readback≃ x .snd) (agree x)
```

## Stability, when the carrier is a groupoid

The tier turns on one h-level. A readback family is a path between
homs, so it is propositional exactly when the homs are sets — that is,
when the carrier is a 1-type. There it is a proposition and inhabited,
hence contractible; the flank coherence is then a pair of
identifications inside a proposition, so it holds of every family and
is itself propositional. The third tier follows.

```agda
module groupoid-carrier {u} {A : Type u} (A-gpd : is-groupoid A) where

  open virtual-graph (PG A)
  open sequents (PG A)

  path-prop : ∀ {x y : A} (p q : hom x y) → is-prop (p ≡ q)
  path-prop {x} {y} = A-gpd x y

  readback-prop : is-prop (readback (PG A))
  readback-prop = Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → path-prop _ _

  coh-holds : (v : readback (PG A)) → absorb-coh (PG A) (PG-unital A) v
  coh-holds v x .fst = path-prop _ _ _ _
  coh-holds v x .snd = path-prop _ _ _ _

  coh-prop : (v : readback (PG A)) → is-prop (absorb-coh (PG A) (PG-unital A) v)
  coh-prop v = Π-is-prop λ _ →
    ×-is-hlevel 1 (is-prop→is-set (path-prop _ _) _ _)
                  (is-prop→is-set (path-prop _ _) _ _)

  PG-stable : is-stable (PG A) (PG-unital A)
  PG-stable = prop-inhabited→is-contr
    (Σ-is-prop readback-prop coh-prop)
    (PG-readback A , coh-holds (PG-readback A))
```

All three tiers, so the theory has a model.

```agda
  PG-deductive : is-deductive-system (PG A)
  PG-deductive .is-deductive-system.composable = PG-composable A
  PG-deductive .is-deductive-system.unital     = PG-unital A
  PG-deductive .is-deductive-system.stable     = PG-stable
```
