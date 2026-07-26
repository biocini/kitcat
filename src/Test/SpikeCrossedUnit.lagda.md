Spike: the two axiom halves, pinned against each other

`var` and `covar` fill opposite slots and there is no reason for them to
be the same edge. This spike takes them apart: the chosen family fills
the term slot only, the coterm slot is filled by the edge the
coterm-hand's fiber produces, and the term-hand's tier is stated over
that derived filler.

The question is what the term-hand's fiber then contains. Its centre is
forced back onto the chosen family — by contractibility, with no
absorption law assumed anywhere, at an arbitrary carrier and an
arbitrary choice of family.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeCrossedUnit where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (_≃_; is-equiv; eqv-fibers; iso→equiv)
open import Core.Equiv.Properties using (_∙e_; Π-contr-dom)
open import Core.Groupoid.Virtual using (module yon-unbiased)

-- The carrier, inlined: a spike in an in-development layer carries its
-- own copy of the data it probes, so a change to the layer cannot
-- silently retune it.

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
```

## The coterm-hand, on the chosen family

The chosen family enters once, in the held term slot, and the target is
the second projection.

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (argue (var x) γ)

  is-unital⁻ : Type (o ⊔ h)
  is-unital⁻ = ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
```

## The term-hand, on the derived filler

Its centre is an edge; that edge is what fills the coterm slot. The
chosen family is not consulted a second time.

```agda
module _ {o h} (G : virtual-graph o h) (U⁻ : is-unital⁻ G) where
  open virtual-graph G
  open sequents G

  unit⁻ : (x : ob) → hom x x
  unit⁻ x = U⁻ x .center .fst

  covar⁻ : (y : ob) → coterm y
  covar⁻ y = y , unit⁻ y

  act-π⁻ : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π⁻ {y = y} f t = reflect f (argue t (covar⁻ y))

  is-unital⁺ : Type (o ⊔ h)
  is-unital⁺ = ∀ x → is-contr (fiber (act-π⁻ {x} {x}) snd)

  module _ (U⁺ : is-unital⁺) where
    unit⁺ : (x : ob) → hom x x
    unit⁺ x = U⁺ x .center .fst

    unit⁺-unique : ∀ x (e : hom x x) → act-π⁻ e ≡ snd → e ≡ unit⁺ x
    unit⁺-unique x e w = sym (ap fst (U⁺ x .paths (e , w)))
```

## What the coterm-hand's composition gives on its own

The negative hand is untouched by the crossing — its injection reads the
coterm slot through `coact`, which consults the chosen family and
nothing else. So its composability is statable here verbatim.

```agda
  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact f γ = γ .fst , coact-π G f γ

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (γ .fst , coact g (γ .snd))

  is-composable⁻ : Type (o ⊔ h)
  is-composable⁻ = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → is-contr (is-representable (composite⁻ f g))

  module _ (C⁻ : is-composable⁻) where
    _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾⁻ g = C⁻ f g .center .fst

    reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → reflect (f ⨾⁻ g) ≡ composite⁻ f g
    reflect-⨾⁻ f g = C⁻ f g .center .snd
```

The centre's defining path is a statement about the coterm slot alone,
so it lifts to the coterm transport and rewrites the composite judgment
back to its head.

```agda
    absorb-coact : ∀ {y} (γ : coterm y) → coact (unit⁻ y) γ ≡ γ
    absorb-coact {y} γ i = γ .fst , U⁻ y .center .snd i γ

    composite⁻-unitr : ∀ {x y} (f : hom x y) → composite⁻ f (unit⁻ y) ≡ reflect f
    composite⁻-unitr f i γ = reflect f (γ .fst , absorb-coact (γ .snd) i)
```

Every reflected judgment is therefore a composite judgment, which makes
`reflect` an embedding and hands back the coterm-hand's right unit law.

```agda
    reflect-image-contr
      : ∀ {x y} (f : hom x y) → is-contr (is-representable (reflect f))
    reflect-image-contr {y = y} f =
      subst (λ α → is-contr (is-representable α))
            (composite⁻-unitr f) (C⁻ f (unit⁻ y))

    reflect-lc : ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
    reflect-lc {n = n} p =
      sym (ap fst (reflect-image-contr n .paths (_ , p)))
      ∙ ap fst (reflect-image-contr n .paths (n , refl))

    ⨾⁻-unitr : ∀ {x y} (f : hom x y) → f ⨾⁻ unit⁻ y ≡ f
    ⨾⁻-unitr f = reflect-lc (reflect-⨾⁻ f (unit⁻ _) ∙ composite⁻-unitr f)
```

## The exchange, located

The term-hand's condition on the chosen family compares the edge
`⟨u , a , unit⁻⟩` with `u`. Composability collapses the *composite
judgment* of `u` and `unit⁻` to `u` on its own; what it does not supply
is that this edge represents that judgment. Naming that step and
deriving the condition from it locates the content exactly — the two are
interderivable over composability, so this is where the coherence lives
rather than a reduction of it.

```agda
    exchange-hypothesis : Type (o ⊔ h)
    exchange-hypothesis =
      ∀ {w x} (u : hom w x)
      → reflect (act-π⁻ (idn x) (w , u)) ≡ composite⁻ u (unit⁻ x)

    module _ (E : exchange-hypothesis) where
      chosen-absorbs⁺-from-exchange
        : ∀ x (t : term x) → act-π⁻ (idn x) t ≡ t .snd
      chosen-absorbs⁺-from-exchange x t =
        reflect-lc (E (t .snd) ∙ sym (reflect-⨾⁻ (t .snd) (unit⁻ x)))
        ∙ ⨾⁻-unitr (t .snd)
```

## The path groupoid, at an arbitrary chosen family

Nothing distinguishes reflexivity here: `a` is any family of endo-edges.

```agda
module path {u} {A : Type u} (a : (x : A) → x ≡ x) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  emb-equiv : {x y : A} → is-equiv (emb {x} {y})
  emb-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob          = A
  PG .virtual-graph.hom x y     = x ≡ y
  PG .virtual-graph.idn         = a
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  open virtual-graph PG
  open sequents PG
```

Terms and coterms are the based path spaces. Recentring a contractible
type at any of its points is what lets the collapse land on the chosen
filler rather than on reflexivity.

```agda
  term-contr : ∀ x → is-contr (term x)
  term-contr x .center = x , refl
  term-contr x .paths (w , p) i = p (~ i) , λ j → p (~ i ∨ j)

  coterm-contr : ∀ y → is-contr (coterm y)
  coterm-contr y .center = y , refl
  coterm-contr y .paths (v , p) i = p i , λ j → p (i ∧ j)

  recentre : ∀ {ℓ} {T : Type ℓ} → is-contr T → T → is-contr T
  recentre c t .center = t
  recentre c t .paths s = sym (c .paths t) ∙ c .paths s
```

Representability is total, so each hand's projection is an equivalence
and every fiber of it is contractible.

```agda
  curry≃ : ∀ {x y} → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z) ≃ judgment x y
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  reflect-equiv : ∀ {x y} → is-equiv (reflect {x} {y})
  reflect-equiv = ((emb , emb-equiv) ∙e curry≃) .snd

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
    ( (reflect , reflect-equiv)
    ∙e slot≃
    ∙e Π-contr-dom (recentre (term-contr x) (var x)) ) .snd

  PG-unital⁻ : is-unital⁻ PG
  PG-unital⁻ x = eqv-fibers (coact-π-equiv x) snd

  act-π⁻-equiv : ∀ x → is-equiv (act-π⁻ PG PG-unital⁻ {x} {x})
  act-π⁻-equiv x =
    ( (reflect , reflect-equiv)
    ∙e slot-swap≃
    ∙e Π-contr-dom (recentre (coterm-contr x) (covar⁻ PG PG-unital⁻ x)) ) .snd

  PG-unital⁺ : is-unital⁺ PG PG-unital⁻
  PG-unital⁺ x = eqv-fibers (act-π⁻-equiv x) snd
```

## The crossed fixpoint

Read the coterm-hand's centre at the axiom half of the coterm, and the
term-hand's candidate at the axiom half of the term. The two are the
same ternary composite with its flanks exchanged, which is `pcom.lr`.

```agda
  centre⁻ : ∀ x → coact-π PG (unit⁻ PG PG-unital⁻ x) ≡ snd
  centre⁻ x = PG-unital⁻ x .center .snd

  centre⁻-pt
    : ∀ x → pcom.composite (sym (a x)) (unit⁻ PG PG-unital⁻ x) refl ≡ refl
  centre⁻-pt x i = centre⁻ x i (x , refl)

  at-axiom : ∀ x → act-π⁻ PG PG-unital⁻ (a x) (x , refl) ≡ refl
  at-axiom x = pcom.lr (a x) (unit⁻ PG PG-unital⁻ x) ∙ centre⁻-pt x
```

The term slot is a contractible domain, so one point suffices.

```agda
  chosen-absorbs⁺ : ∀ x → act-π⁻ PG PG-unital⁻ (a x) ≡ snd
  chosen-absorbs⁺ x = funext λ t →
    subst (λ s → act-π⁻ PG PG-unital⁻ (a x) s ≡ s .snd)
          (term-contr x .paths t) (at-axiom x)

  crossed : ∀ x → a x ≡ unit⁺ PG PG-unital⁻ PG-unital⁺ x
  crossed x = unit⁺-unique PG PG-unital⁻ PG-unital⁺ x (a x) (chosen-absorbs⁺ x)
```

## What the spike settles

`crossed` identifies the chosen family with the term-hand's canonical
unit, and `unit⁺-unique` says any other candidate meets it there. That
is unitality characterised, with the chosen edge on the characterised
side — and nothing was assumed about it. `a` is arbitrary, no absorption
law appears in the carrier or the hypotheses, and no h-level condition
is imposed on `A`.

What buys it is the exchange. The coterm-hand consults the chosen family
in its held term slot and returns an edge; that edge, not the chosen
family, fills the term-hand's held coterm slot; and the term-hand's
condition then reads the same ternary composite from the other side. The
two flank arrangements are `pcom.lr` apart, so the second tier's fiber
contains exactly what the first tier's centre was built against.

The self-referential form fails precisely where this one does not.
Filling both held slots with the same edge asks it to absorb against
itself — `Test.SpikeSelfUnit` computes that to squaring — while filling
them with the two *different* edges asks them to absorb against each
other, which is a statement about a pair and carries no square.

The same difference disposes of `Test.SpikeAbsorbObstruction` here. That
argument perturbs the chosen family and finds the absorption statement
moving by the doubling of the perturbation, because the chosen edge
occurs twice in it. In the crossed form the derived filler is a function
of the chosen family, so a perturbation moves both sides of `crossed`
together and the doubling does not arise.
