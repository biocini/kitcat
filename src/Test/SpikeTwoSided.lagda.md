Spike: over which base is `judgment` one-variance, and what kind of
structure is a mediation?

Displayed over the graph's own vertices, `judgment` has mixed variance
and reaches only the unbiased lens. Mixed variance is however a fact
about the base, not about the family: over the graph paired with its
opposite, `judgment` transports covariantly in a single move, and the
whole apparatus collapses to one *oplax covariant* lens.

That base is where the two composite judgments become two pushforwards
into a common fiber, so interchange becomes the agreement of a cospan
rather than a unitor — and where the failure of a lens to be functorial
is exactly the gap between the two compositions.

Composability and the unit data are hypothesised separately, because
the two halves of the answer consume them separately: the distributive
laws and the composition of `bipush` need only the first, the lens and
its unitor only the second.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeTwoSided where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Path.Base

open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base
open import Cat.Graph.Refl.Properties
open import Cat.Graph.Refl.Lens
open import Cat.Logic.Type
```

## The vocabulary, axiom-free

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact {x} f e = elim (reflect f (argue (var x) e))

  act : ∀ {x y} → hom x y → term x → term y
  act {y = y} f t = intro (reflect f (argue t (covar y)))

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (argue (var x) γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (argue t (covar y))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (argue (γ .fst) (coact g (γ .snd)))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect g (argue (act f (γ .fst)) (γ .snd))

  readback : Type (o ⊔ h)
  readback = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f

  graph : reflexive-graph o h
  graph .reflexive-graph.vtx  = ob
  graph .reflexive-graph.edge = hom
  graph .reflexive-graph.rx   = idn
```

## The two-sided base

Nothing new is needed to build it: it is the suite's binary product of
the underlying graph with its own opposite. A vertex is a pair of
objects, and an edge into `(x' , y')` from `(x , y)` is an edge
*backward* on the first coordinate and forward on the second — the
shape `judgment`'s two variances ask for.

```agda
  two-sided : reflexive-graph o h
  two-sided = rx.binary-product (rx.op graph) graph

  two-sided-vtx : reflexive-graph.vtx two-sided ≡ (ob × ob)
  two-sided-vtx = refl

  two-sided-edge : ∀ x y x' y'
                 → reflexive-graph.edge two-sided (x , y) (x' , y')
                 ≡ (hom x' x × hom y y')
  two-sided-edge _ _ _ _ = refl

  two-sided-rx : ∀ x y → reflexive-graph.rx two-sided (x , y) ≡ (idn x , idn y)
  two-sided-rx _ _ = refl
```

## The two-sided action

Both slots at once: the term slot travels by `act`, the coterm slot by
`coact`, and the conclusion's endpoints are untouched because each
action preserves the anonymous endpoint on the nose. Axiom-free.

```agda
  bipush : ∀ {x y x' y'} → hom x' x → hom y y' → judgment x y → judgment x' y'
  bipush a b α γ = α (argue (act a (γ .fst)) (coact b (γ .snd)))

  judgment-fam : rx.vfam two-sided (o ⊔ h) (o ⊔ h)
  judgment-fam (x , y) = discrete (judgment x y)

  interchange : Type (o ⊔ h)
  interchange = ∀ {x y z} (f : hom x y) (g : hom y z)
              → composite⁻ f g ≡ composite⁺ f g
```

## What composability alone gives

Each action distributes over its own hand's composition, with no
mediation: the head-rewriting witness is the whole proof, and the
anonymous endpoint never moves.

```agda
  module composable
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable (composite⁻ f g)))
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable (composite⁺ f g)))
    where

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
```

A lens carries a transport and a unitor and asks nothing about
composites of base edges. Ask it anyway: the two-sided action does
compose, but the composite base edge it produces uses **the `⁺`
composition on the backward leg and the `⁻` composition on the forward
leg**.

```agda
    bipush-comp
      : ∀ {x y x' y' x'' y''}
        (a : hom x' x) (a' : hom x'' x') (b : hom y y') (b' : hom y' y'')
        (α : judgment x y)
      → bipush a' b' (bipush a b α) ≡ bipush (a' ⨾⁺ a) (b ⨾⁻ b') α
    bipush-comp a a' b b' α = funext λ γ → λ i →
      α (argue (act-⨾⁺ a' a (γ .fst) (~ i)) (coact-⨾⁻ b b' (γ .snd) (~ i)))
```

So the two-sided base carries no single composition for which the lens
is functorial: its first coordinate wants `_⨾⁺_` and its second wants
`_⨾⁻_`. A mediation is exactly what makes those one operation, and
with it the composite base edge is formed by one composition
throughout.

```agda
    mediation : Type (o ⊔ h)
    mediation = ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁻ g ≡ f ⨾⁺ g

    bipush-comp-mediated
      : mediation
      → ∀ {x y x' y' x'' y''}
        (a : hom x' x) (a' : hom x'' x') (b : hom y y') (b' : hom y' y'')
        (α : judgment x y)
      → bipush a' b' (bipush a b α) ≡ bipush (a' ⨾⁻ a) (b ⨾⁻ b') α
    bipush-comp-mediated M a a' b b' α =
      bipush-comp a a' b b' α
      ∙ ap (λ c → bipush c (b ⨾⁻ b') α) (sym (M a' a))
```

## The lens

The unitor is the one place the unit data enters, and it enters for
the reason it always does: a lens states its unitors at the base's own
reflexive edge, which is `idn`.

```agda
  module unital
    (unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd))
    (unit-fiber⁺ : ∀ x → is-contr (fiber (act-π   {x} {x}) snd))
    (rb : readback)
    where

    unit⁻ unit⁺ : ∀ x → hom x x
    unit⁻ x = unit-fiber⁻ x .center .fst
    unit⁺ x = unit-fiber⁺ x .center .fst

    unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
    unit⁻-absorb x γ i = unit-fiber⁻ x .center .snd i γ

    unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
    unit⁺-absorb x t i = unit-fiber⁺ x .center .snd i t

    idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
    idn-absorb⁻ x γ =
      ap (λ e → coact-π e γ) (sym (sym (rb (unit⁻ x)) ∙ unit⁻-absorb x (covar x)))
      ∙ unit⁻-absorb x γ

    idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
    idn-absorb⁺ x t =
      ap (λ e → act-π e t) (sym (sym (rb (unit⁺ x)) ∙ unit⁺-absorb x (var x)))
      ∙ unit⁺-absorb x t

    coact-idn : ∀ {y} (e : coterm y) → coact (idn y) e ≡ e
    coact-idn {y} e i = e .fst , idn-absorb⁻ y e i

    act-idn : ∀ {x} (t : term x) → act (idn x) t ≡ t
    act-idn {x} t i = t .fst , idn-absorb⁺ x t i

    bipush-idn : ∀ {x y} (α : judgment x y) → bipush (idn x) (idn y) α ≡ α
    bipush-idn α = funext λ γ → λ i →
      α (argue (act-idn (γ .fst) i) (coact-idn (γ .snd) i))

    judgment-lens : oplax-cov-lens two-sided judgment-fam
    judgment-lens .oplax-cov-lens.has-push _ _ (a , b) = bipush a b
    judgment-lens .oplax-cov-lens.has-unitor = bipush-idn

    judgment-disp : rx.disp two-sided (o ⊔ h) (o ⊔ h)
    judgment-disp = oplax-cov-lens.display judgment-lens

    judgment-disp-path-object : is-displayed-univalent judgment-disp
    judgment-disp-path-object =
      cov-disp-path-object judgment-lens (λ _ → disc-path-object _)
```

So the mixed variance is base-relative. Displayed over the objects,
`judgment` needs the unbiased lens and its two injections; displayed
over the objects paired twice, it is an ordinary covariant lens with
one transport and one unitor, and `cov-disp-path-object` applies for
the same reason its unbiased counterpart does.

## The composites are two pushforwards into one fiber

Each composite judgment is the two-sided action with one leg held at
reflexivity, applied to one factor's reflection. The two land in the
same fiber — the one at `(x , z)` — from *different* vertices.

```agda
    push-is-composite⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
                       → bipush (idn x) g (reflect f) ≡ composite⁻ f g
    push-is-composite⁻ f g = funext λ γ → λ i →
      reflect f (argue (act-idn (γ .fst) i) (coact g (γ .snd)))

    push-is-composite⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
                       → bipush f (idn z) (reflect g) ≡ composite⁺ f g
    push-is-composite⁺ f g = funext λ γ → λ i →
      reflect g (argue (act f (γ .fst)) (coact-idn (γ .snd) i))
```

```text
            (x , y)                     (y , z)
               \                           /
        (idn x , g)                 (f , idn z)
                 \                     /
                     ‾‾‾ (x , z) ‾‾‾
```

Neither leg is the other's reversal, and the two sources are distinct
vertices. Interchange is the statement that the two pushforwards agree
— a *cospan* coherence, which is neither a unitor nor an edge of the
display.

```agda
    interchange-is-cospan
      : interchange
      → ∀ {x y z} (f : hom x y) (g : hom y z)
      → bipush (idn x) g (reflect f) ≡ bipush f (idn z) (reflect g)
    interchange-is-cospan I f g =
      push-is-composite⁻ f g ∙ I f g ∙ sym (push-is-composite⁺ f g)

    cospan-is-interchange
      : (∀ {x y z} (f : hom x y) (g : hom y z)
         → bipush (idn x) g (reflect f) ≡ bipush f (idn z) (reflect g))
      → interchange
    cospan-is-interchange C f g =
      sym (push-is-composite⁻ f g) ∙ C f g ∙ push-is-composite⁺ f g
```

## Interchange delivers the mediation

The one statement needing both halves of the hypotheses: reflect both
compositions onto the same judgment, and read the result back.

```agda
    module with-composition
      (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
                → is-contr (is-representable (composite⁻ f g)))
      (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
                → is-contr (is-representable (composite⁺ f g)))
      where
      open composable contr⁻ contr⁺

      interchange→mediation : interchange → mediation
      interchange→mediation I f g =
        sym (rb (f ⨾⁻ g))
        ∙ ap eval (reflect-⨾⁻ f g ∙ I f g ∙ sym (reflect-⨾⁺ f g))
        ∙ rb (f ⨾⁺ g)
```

## What the spike settles

Mixed variance is a property of the display, not of `judgment`. Over
the graph paired with its opposite — `rx.binary-product (rx.op graph)
graph`, built from the suite's own operations — `judgment` is the
vertex family of an oplax covariant lens, with one transport `bipush`,
one unitor, and a univalent display. The unbiased lens is what the
same family requires when the base is kept one-sided.

Over that base the two composite judgments are the two pushforwards of
`reflect f` and `reflect g` into the fiber at `(x , z)`, along
`(idn x , g)` and `(f , idn z)`. The sources are distinct vertices and
the legs point the same way, so the configuration is a cospan.
Interchange is the agreement of its two pushforwards, and that is why
no display of `judgment` has it as an edge: a displayed edge relates
data over the *two ends of one base edge*, and an unbiased lens'
injections source at diagonal components, whereas `reflect f` and
`reflect g` sit at `(x , y)` and `(y , z)`. A base making those two
diagonal would have to make the composability relation reflexive,
which it is not — the semi-Segal obstruction, met in the lens
vocabulary.

What interchange *is*, in this vocabulary, is the missing functoriality
of the lens. Each action distributes over its own hand's composition
from composability alone, so `bipush` does compose — but the composite
base edge it lands on carries `_⨾⁺_` on the backward coordinate and
`_⨾⁻_` on the forward one. A mediation makes those a single operation;
the two-sided base then carries one composition, and the lens becomes a
functor over it. Interchange implies the mediation.

A lens is therefore precisely the amount of structure that survives
without a mediation: transport and a unitor, no functoriality. That the
fragment is expressible in reflexive-graph language, and interchange is
not, is one statement.
