Spike: can a propositional unit tier certify that the reflexive
graph's chosen edge is the canonical unit?

The tension. A unit datum is propositional when it is stated as a
*fiber of the action map* over the identity action, and every
formulation of that shape projects its unit from the fiber's center.
A virtual graph, being a reflexive graph, instead supplies a chosen
edge `idn` at every object, wired into `var`, `covar` and `eval`. A
tier that projects its own unit would therefore leave two candidate
units side by side, identified only by an extra datum.

The question is whether the extra datum is needed at all: with the
tier stated so as never to mention `idn`, do the other tiers force
the chosen edge to *be* the projected unit?

They do, and readback is what does it. The projected unit absorbs
every edge, in particular `idn` itself; readback says evaluation of a
reflected edge returns that edge; and evaluation at the axiom is
definitionally the action applied to `idn`. Composing the two paths
identifies the projected unit with `idn`, whence the chosen edge
inherits absorption. Nothing here mentions composability, so the
argument is available at the unit tier alone, and it runs the same
way on both hands.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeUnitCanonical where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Path.Base
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; Σ-is-prop)
open import Core.Transport.Properties using (is-contr-is-prop)

open import Cat.Logic.Type

module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G
```

## The action maps, at the level of edges

Each hand's action holds one slot of the argument at its axiom half.
Stated on edges rather than on terms and coterms, the anonymous
endpoint is a parameter rather than a component, so a fiber over one
of these maps is a plain fiber with no `Σ` to unpack.

```agda
  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (argue (var x) γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (argue t (covar y))
```

Evaluation at the axiom is either action applied to `idn`. Both are
definitional, and they are what carries readback into the argument
below.

```agda
  eval-is-coact : ∀ {x} (e : hom x x) → eval (reflect e) ≡ coact-π e (covar x)
  eval-is-coact _ = refl

  eval-is-act : ∀ {x} (e : hom x x) → eval (reflect e) ≡ act-π e (var x)
  eval-is-act _ = refl
```

## The composability tier

Carried along for the bundle at the end: the two composite judgments
and the contractibility of their representability fibers.

```agda
  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact {x} f e = elim (reflect f (argue (var x) e))

  act : ∀ {x y} → hom x y → term x → term y
  act {y = y} f t = intro (reflect f (argue t (covar y)))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (argue (γ .fst) (coact g (γ .snd)))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect g (argue (act f (γ .fst)) (γ .snd))

  is-composable⁻ : Type (o ⊔ h)
  is-composable⁻ = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → is-contr (is-representable (composite⁻ f g))

  is-composable⁺ : Type (o ⊔ h)
  is-composable⁺ = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → is-contr (is-representable (composite⁺ f g))

  is-composable⁻-is-prop : is-prop is-composable⁻
  is-composable⁻-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _

  is-composable⁺-is-prop : is-prop is-composable⁺
  is-composable⁺-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _
```

## The unit tier

Per hand, the fiber of that hand's action map over the identity
action. The tier does not mention `idn`, and its unit is the fiber's
center.

```agda
  is-unital⁻ : Type (o ⊔ h)
  is-unital⁻ = ∀ x → is-contr (fiber (coact-π {x} {x}) snd)

  is-unital⁺ : Type (o ⊔ h)
  is-unital⁺ = ∀ x → is-contr (fiber (act-π {x} {x}) snd)
```

Propositional by construction, and uniformly so: contractibility is a
proposition at each object, and a product of propositions is one.

```agda
  is-unital⁻-is-prop : is-prop is-unital⁻
  is-unital⁻-is-prop = Π-is-prop λ _ → is-contr-is-prop _

  is-unital⁺-is-prop : is-prop is-unital⁺
  is-unital⁺-is-prop = Π-is-prop λ _ → is-contr-is-prop _
```

## Readback

The stability tier's projection, assumed here in its bare family form
— weaker than the pinned fiber, so a derivation from it holds a
fortiori of the tier.

```agda
  readback : Type (o ⊔ h)
  readback = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f
```

## The chosen edge is the canonical unit

The projected unit absorbs everything; instantiating that at `idn`
and composing with readback at the projected unit identifies the two.
Absorption then transports onto the chosen edge.

```agda
  module canonical (U⁻ : is-unital⁻) (U⁺ : is-unital⁺) (rb : readback) where

    unit⁻ unit⁺ : ∀ x → hom x x
    unit⁻ x = U⁻ x .center .fst
    unit⁺ x = U⁺ x .center .fst

    unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
    unit⁻-absorb x γ i = U⁻ x .center .snd i γ

    unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
    unit⁺-absorb x t i = U⁺ x .center .snd i t

    unit⁻-is-idn : ∀ x → unit⁻ x ≡ idn x
    unit⁻-is-idn x = sym (rb (unit⁻ x)) ∙ unit⁻-absorb x (covar x)

    unit⁺-is-idn : ∀ x → unit⁺ x ≡ idn x
    unit⁺-is-idn x = sym (rb (unit⁺ x)) ∙ unit⁺-absorb x (var x)
```

The chosen edge inherits both absorptions, and the two hands' units
coincide with it and so with each other.

```agda
    idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
    idn-absorb⁻ x γ =
      ap (λ e → coact-π e γ) (sym (unit⁻-is-idn x)) ∙ unit⁻-absorb x γ

    idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
    idn-absorb⁺ x t =
      ap (λ e → act-π e t) (sym (unit⁺-is-idn x)) ∙ unit⁺-absorb x t

    units-agree : ∀ x → unit⁻ x ≡ unit⁺ x
    units-agree x = unit⁻-is-idn x ∙ sym (unit⁺-is-idn x)
```

Uniqueness in the polymorphic form: any edge whose action is the
identity action is the chosen edge, on either hand.

```agda
    unit⁻-unique : ∀ {x} (e : hom x x)
                 → (∀ γ → coact-π e γ ≡ γ .snd)
                 → e ≡ idn x
    unit⁻-unique {x} e abs = sym (rb e) ∙ abs (covar x)

    unit⁺-unique : ∀ {x} (e : hom x x)
                 → (∀ t → act-π e t ≡ t .snd)
                 → e ≡ idn x
    unit⁺-unique {x} e abs = sym (rb e) ∙ abs (var x)
```

## The stability tier

Readback bare is a torsor: two families differ by a loop at every
edge, so it cannot be a predicate as it stands. What pins it is the
one place where a second route to the same endpoints exists. At the
identity flank, evaluation of the reflected identity reaches `idn`
twice over — once by the readback family, once by transporting the
projected unit's absorption along the identification the family
itself induces. Requiring the two to agree, on both hands, is the
`absorb-coh` coherence in this setting; taking it inside the fiber
leaves the tier propositional for the same reason the other two are.

```agda
  module stability (U⁻ : is-unital⁻) (U⁺ : is-unital⁺) where

    unit⁻ unit⁺ : ∀ x → hom x x
    unit⁻ x = U⁻ x .center .fst
    unit⁺ x = U⁺ x .center .fst

    unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
    unit⁻-absorb x γ i = U⁻ x .center .snd i γ

    unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
    unit⁺-absorb x t i = U⁺ x .center .snd i t
```

Each readback family identifies both projected units with the chosen
edge, and transports their absorptions onto it. The two transported
paths are the flank canonicals.

```agda
    unit⁻-is-idn : (u : readback) → ∀ x → unit⁻ x ≡ idn x
    unit⁻-is-idn u x = sym (u (unit⁻ x)) ∙ unit⁻-absorb x (covar x)

    unit⁺-is-idn : (u : readback) → ∀ x → unit⁺ x ≡ idn x
    unit⁺-is-idn u x = sym (u (unit⁺ x)) ∙ unit⁺-absorb x (var x)
```

Each flank canonical reads only one value of the family — the
family's path at that hand's projected unit — so it is stated as a
function of that value.

```agda
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

    flank⁻ : (u : readback) → ∀ x → eval (reflect (idn x)) ≡ idn x
    flank⁻ u x = flank⁻-of x (u (unit⁻ x))

    flank⁺ : (u : readback) → ∀ x → eval (reflect (idn x)) ≡ idn x
    flank⁺ u x = flank⁺-of x (u (unit⁺ x))
```

The coherence, and the tier. Asking agreement on both hands makes the
two flank canonicals agree with each other as well, which is the one
cross-hand fact the record asserts.

```agda
    absorb-coh : readback → Type (o ⊔ h)
    absorb-coh u = ∀ x → (u (idn x) ≡ flank⁻ u x) × (u (idn x) ≡ flank⁺ u x)

    is-stable : Type (o ⊔ h)
    is-stable = is-contr (Σ {A = readback} absorb-coh)

    is-stable-is-prop : is-prop is-stable
    is-stable-is-prop = is-contr-is-prop _
```

The projections: readback itself, and the agreement of the two hands
at the flank.

```agda
    module _ (S : is-stable) where
      unit : readback
      unit = S .center .fst

      flanks-agree : ∀ x → flank⁻ unit x ≡ flank⁺ unit x
      flanks-agree x =
        sym (S .center .snd x .fst) ∙ S .center .snd x .snd
```

## The half-adjoint form, and why it fails

The question is whether the coherence alone makes the pair
propositional, without wrapping it in contractibility. It does not,
and the obstruction is exact: every value the coherence reads is at
an *endomorphism* — `idn x` and the two projected units — so a family
may be perturbed anywhere else and still satisfy it.

A perturbation is a twist: a loop at every edge, composed onto the
family pointwise.

```agda
    twist : Type (o ⊔ h)
    twist = ∀ {x y} (f : hom x y) → f ≡ f

    _∙ᵗ_ : readback → twist → readback
    (u ∙ᵗ t) f = u f ∙ t f

    half-adjoint : Type (o ⊔ h)
    half-adjoint = Σ {A = readback} absorb-coh
```

A twist that vanishes on endomorphisms leaves every value the
coherence reads untouched, so it carries one inhabitant to another.

```agda
    module _ (t : twist) (te : ∀ x (e : hom x x) → t e ≡ refl) where

      agree : ∀ (u : readback) x (e : hom x x) → (u ∙ᵗ t) e ≡ u e
      agree u x e = ap (u e ∙_) (te x e) ∙ Path.unitr (u e)

      coh-twist : (u : readback) → absorb-coh u → absorb-coh (u ∙ᵗ t)
      coh-twist u c x .fst =
        agree u x (idn x) ∙ c x .fst
        ∙ sym (ap (flank⁻-of x) (agree u x (unit⁻ x)))
      coh-twist u c x .snd =
        agree u x (idn x) ∙ c x .snd
        ∙ sym (ap (flank⁺-of x) (agree u x (unit⁺ x)))
```

So propositionality of the pair would force every such twist to be
trivial — a truncation condition on the hom types, which the library
refuses by design.

```agda
    private
      cancel : ∀ {u} {A : Type u} {a b : A} (p : a ≡ b) (q : b ≡ b)
             → p ≡ p ∙ q → q ≡ refl
      cancel p q e =
        sym (Path.unitl q)
        ∙ ap (_∙ q) (sym (Path.invl p))
        ∙ sym (Path.assoc (sym p) p q)
        ∙ ap (sym p ∙_) (sym e)
        ∙ Path.invl p

    half-adjoint-forces-truncation
      : is-prop half-adjoint
      → (S : half-adjoint)
      → (t : twist) (te : ∀ x (e : hom x x) → t e ≡ refl)
      → ∀ {x y} (f : hom x y) → t f ≡ refl
    half-adjoint-forces-truncation P S t te {x} {y} f =
      cancel (S .fst f) (t f) (ap (λ w → w {x} {y} f) (ap fst step))
      where
        step : S ≡ (S .fst ∙ᵗ t , coh-twist t te (S .fst) (S .snd))
        step = P S _
```

## The bundle

The three tiers together, as one predicate on the virtual graph. The
stability tier depends on the unit tiers — its flanks are stated at
their projected units — so the bundle is iterated `Σ` rather than a
product, and its propositionality is the corresponding iteration.

```agda
  is-deductive-system : Type (o ⊔ h)
  is-deductive-system =
    Σ {A = is-composable⁻} λ _ →
    Σ {A = is-composable⁺} λ _ →
    Σ {A = is-unital⁻} λ U⁻ →
    Σ {A = is-unital⁺} λ U⁺ →
    stability.is-stable U⁻ U⁺

  is-deductive-system-is-prop : is-prop is-deductive-system
  is-deductive-system-is-prop =
    Σ-is-prop is-composable⁻-is-prop λ _ →
    Σ-is-prop is-composable⁺-is-prop λ _ →
    Σ-is-prop is-unital⁻-is-prop λ U⁻ →
    Σ-is-prop is-unital⁺-is-prop λ U⁺ →
    stability.is-stable-is-prop U⁻ U⁺
```

## What the spike settles

A unit tier that never mentions `idn` is propositional by
construction, and together with readback alone — composability is not
consumed — it forces the chosen edge of the underlying reflexive
graph to be its own projected unit, on both hands, hence forces the
two hands' units to agree. The bridge that seemed to be owed as a
datum is a theorem.

The uniqueness statements need no unit tier at all: readback by
itself makes any edge acting as the identity equal to `idn`. What the
tier adds is the existence of such an edge, propositionally.

The three tiers bundle into one predicate on a virtual graph, and it
is propositional. Composability and unitality are contractibility
statements outright; stability is contractibility of the pair of a
readback family with the coherence pinning it at the flanks.

That wrapper is not decoration. Dropping it — asking the pair itself
to be propositional, in the half-adjoint manner — fails, and fails
for a reason internal to the coherence rather than for want of a
better proof: every value the coherence reads lies at an
endomorphism, so a twist supported away from the endomorphisms
carries an inhabitant to another inhabitant. Propositionality of the
bare pair would therefore make every such twist trivial, which is a
truncation condition on the homs.
