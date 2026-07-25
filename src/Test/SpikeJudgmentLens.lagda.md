Spike: is `judgment` displayable, and by which lens?

`judgment x y` is contravariant in `x` and covariant in `y`, so it is
the vertex family of neither biased lens. Weakened over the edges
running between its two indices it becomes an `rx.efam`, and the
injections carrying that family's diagonal components into a general
one are the two composite operations, one per hand.

Three questions. Does `unbiased-lens` accept that family? What data do
its unitors consume — in particular, do they reach the flank
coherence? And is the resulting display the `judgment[_]` a displayed
deductive system needs?

Hypotheses are taken as parameters rather than as a bundle, so each
answer names the tier data it consumes and nothing more.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeJudgmentLens where

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

Holding one slot of an argument at its axiom half leaves an action on
the other; leaving a slot packaged and letting the head stay a
judgment leaves an injection. Both moves are available on a bare
virtual graph, and the composite judgments are the injections at a
reflected head.

```agda
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

  graph : reflexive-graph o h
  graph .reflexive-graph.vtx  = ob
  graph .reflexive-graph.edge = hom
  graph .reflexive-graph.rx   = idn
```

The component at an edge `p : hom x y` is `judgment x y` with
identifications as edges; the endpoints are named, the edge is not
consulted. The diagonal is then the endo-judgments.

```agda
  judgment± : rx.efam graph (o ⊔ h) (o ⊔ h)
  judgment± x y _ = discrete (judgment x y)

  hom± : rx.efam graph h h
  hom± x y _ = discrete (hom x y)
```

## The lens on judgments

A lens over `graph` states its unitors at that graph's own reflexive
edge, which is `idn`. Absorption holds at the units the fibers below
project and says nothing about `idn`; readback bridges the two. Those
three hypotheses are the whole of what the lens consumes — no
contractibility over readback, and no flank coherence.

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

    unit⁻-is-idn : ∀ x → unit⁻ x ≡ idn x
    unit⁻-is-idn x = sym (rb (unit⁻ x)) ∙ unit⁻-absorb x (covar x)

    unit⁺-is-idn : ∀ x → unit⁺ x ≡ idn x
    unit⁺-is-idn x = sym (rb (unit⁺ x)) ∙ unit⁺-absorb x (var x)

    idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
    idn-absorb⁻ x γ =
      ap (λ e → coact-π e γ) (sym (unit⁻-is-idn x)) ∙ unit⁻-absorb x γ

    idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
    idn-absorb⁺ x t =
      ap (λ e → act-π e t) (sym (unit⁺-is-idn x)) ∙ unit⁺-absorb x t
```

Each unitor is one absorption read under a judgment, at whichever slot
that hand consumes.

```agda
    absorb⁻ : ∀ {x} (α : judgment x x) → inj⁻ α (idn x) ≡ α
    absorb⁻ {x} α = funext λ γ →
      ap (λ b → α (argue (γ .fst) (γ .snd .fst , b))) (idn-absorb⁻ x (γ .snd))

    absorb⁺ : ∀ {x} (α : judgment x x) → inj⁺ (idn x) α ≡ α
    absorb⁺ {x} α = funext λ γ →
      ap (λ a → α (argue (γ .fst .fst , a) (γ .snd))) (idn-absorb⁺ x (γ .fst))

    judgment-lens : unbiased-lens graph judgment±
    judgment-lens .unbiased-lens.linj    _ _ p α = inj⁻ α p
    judgment-lens .unbiased-lens.rinj    _ _ p β = inj⁺ p β
    judgment-lens .unbiased-lens.munitor _   α   = absorb⁻ α ∙ sym (absorb⁺ α)
    judgment-lens .unbiased-lens.runitor _   α   = sym (absorb⁺ α)

    judgment-disp : rx.disp graph (o ⊔ h) (o ⊔ h)
    judgment-disp = unbiased-lens.display judgment-lens
```

The display's vertices at `x` are the endo-judgments there, and a
displayed edge over `p` says the two hands agree on `p`: injecting the
source judgment on the right meets injecting the target judgment on
the left.

```agda
    judgment-disp-vtx : ∀ x → reflexive-graphᴰ.vtx judgment-disp x ≡ judgment x x
    judgment-disp-vtx _ = refl

    judgment-disp-edge
      : ∀ x y (p : hom x y) (α : judgment x x) (β : judgment y y)
      → reflexive-graphᴰ.edge judgment-disp x y p α β ≡ (inj⁻ α p ≡ inj⁺ p β)
    judgment-disp-edge _ _ _ _ _ = refl
```

Its components are discrete, hence path objects, so the display is
univalent — no hypothesis on the base. The `Lens` uniqueness theorems
need `rx.is-univalent` of the *base*, which a deductive system fails;
`unb-disp-path-object` needs it only of the diagonal components, which
here is free.

```agda
    judgment-disp-path-object : is-displayed-univalent judgment-disp
    judgment-disp-path-object =
      unb-disp-path-object judgment-lens (λ _ → disc-path-object _)
```

## The mid unitor against the flank coherence

Read at the reflexive edge, the mid unitor compares the two
injections on an endo-judgment. The flank coherence compares two
*derivations of a path* in a hom type. They sit one dimension apart,
and the lens has no field at the higher dimension: an unbiased lens'
unitors are edges of a component, and the components here are
discrete, so their edges are identifications of judgments and nothing
above that.

```agda
    munitor-at-rx : ∀ x (α : judgment x x) → inj⁻ α (idn x) ≡ inj⁺ (idn x) α
    munitor-at-rx = unbiased-lens.munitor judgment-lens

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

    flanks-agree : Type (o ⊔ h)
    flanks-agree = ∀ x → flank⁻-of x (rb (unit⁻ x)) ≡ flank⁺-of x (rb (unit⁺ x))
```

`flanks-agree` is the statement the stability tier delivers, written
here without it. Nothing above consumes it, which is the answer to the
second question: the lens is inhabited by the three hypotheses alone.

## The lens on homs

Beneath the judgment lens is one on the hom family, whose injections
are the two compositions. Its unitors are the two unit laws, which
readback supplies: a composite and its factor have the same
reflection, and evaluation of a reflection is the identity. This is
the first result needing composability as well.

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

      coact-idn : ∀ {y} (e : coterm y) → coact (idn y) e ≡ e
      coact-idn {y} e i = e .fst , idn-absorb⁻ y e i

      act-idn : ∀ {x} (t : term x) → act (idn x) t ≡ t
      act-idn {x} t i = t .fst , idn-absorb⁺ x t i

      composite⁻-unitr : ∀ {a y} (u : hom a y) → reflect u ≡ composite⁻ u (idn y)
      composite⁻-unitr u = funext λ γ →
        ap (λ e → reflect u (argue (γ .fst) e)) (sym (coact-idn (γ .snd)))

      composite⁺-unitl : ∀ {x c} (u : hom x c) → reflect u ≡ composite⁺ (idn x) u
      composite⁺-unitl u = funext λ γ →
        ap (λ t → reflect u (argue t (γ .snd))) (sym (act-idn (γ .fst)))

      unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ idn y ≡ f
      unitr⁻ {y = y} f =
        sym (rb (f ⨾⁻ idn y))
        ∙ ap eval (reflect-⨾⁻ f (idn y) ∙ sym (composite⁻-unitr f))
        ∙ rb f

      unitl⁺ : ∀ {x y} (f : hom x y) → idn x ⨾⁺ f ≡ f
      unitl⁺ {x} f =
        sym (rb (idn x ⨾⁺ f))
        ∙ ap eval (reflect-⨾⁺ (idn x) f ∙ sym (composite⁺-unitl f))
        ∙ rb f

      hom-lens : unbiased-lens graph hom±
      hom-lens .unbiased-lens.linj    _ _ p e = e ⨾⁻ p
      hom-lens .unbiased-lens.rinj    _ _ p e = p ⨾⁺ e
      hom-lens .unbiased-lens.munitor _   e   = unitr⁻ e ∙ sym (unitl⁺ e)
      hom-lens .unbiased-lens.runitor _   e   = sym (unitl⁺ e)

      hom-disp : rx.disp graph h h
      hom-disp = unbiased-lens.display hom-lens

      hom-disp-path-object : is-displayed-univalent hom-disp
      hom-disp-path-object =
        unb-disp-path-object hom-lens (λ _ → disc-path-object _)
```

Reflection carries one display's edges to the other's: over `p`, an
edge from `d` to `e` in the hom display is `d ⨾⁻ p ≡ p ⨾⁺ e`, and its
reflection is an edge between the reflected endpoints.

```agda
      reflect-disp-edge
        : ∀ {x y} (p : hom x y) (d : hom x x) (e : hom y y)
        → d ⨾⁻ p ≡ p ⨾⁺ e
        → inj⁻ (reflect d) p ≡ inj⁺ p (reflect e)
      reflect-disp-edge p d e q =
        sym (reflect-⨾⁻ d p) ∙ ap reflect q ∙ reflect-⨾⁺ p e
```

## What the display is not

Neither display is the `judgment[_]` a displayed deductive system
needs. The lens display is indexed by base objects and its vertices
*are* judgments; `judgment[_]` is indexed by a base judgment together
with a displayed object over each endpoint, and its elements are
displayed conclusions over the base ones.

The displaced form is the Σ-by-Σ one, built from the displayed
reflexive graph with no lens in sight. Each combinator of the sequent
calculus displaces by replacing every type by its displayed
counterpart over the corresponding base datum, the base argument
visible so that the displayed one determines it.

```agda
  record virtual-graphᴰ (o' h' : Level) : Type₊ (o ⊔ h ⊔ o' ⊔ h') where
    field
      ob[_]  : ob → Type o'
      hom[_] : ∀ {x y} → hom x y → ob[ x ] → ob[ y ] → Type h'
      idn[_] : ∀ {x} (x' : ob[ x ]) → hom[ idn x ] x' x'

    term[_] : ∀ {x} (t : term x) → ob[ x ] → Type (o' ⊔ h')
    term[ t ] x' = Σ w' ∶ ob[ t .fst ] , hom[ t .snd ] w' x'

    coterm[_] : ∀ {y} (e : coterm y) → ob[ y ] → Type (o' ⊔ h')
    coterm[ e ] y' = Σ v' ∶ ob[ e .fst ] , hom[ e .snd ] y' v'

    argument[_] : ∀ {x y} (γ : argument x y) → ob[ x ] → ob[ y ] → Type (o' ⊔ h')
    argument[ γ ] x' y' = term[ γ .fst ] x' × coterm[ γ .snd ] y'

    conclusion[_] : ∀ {x y} {γ : argument x y} → conclusion γ
                  → ∀ {x' y'} → argument[ γ ] x' y' → Type h'
    conclusion[ c ] γ' = hom[ c ] (γ' .fst .fst) (γ' .snd .fst)

    judgment[_] : ∀ {x y} → judgment x y → ob[ x ] → ob[ y ] → Type (o ⊔ h ⊔ o' ⊔ h')
    judgment[ α ] x' y' = ∀ γ (γ' : argument[ γ ] x' y') → conclusion[ α γ ] γ'

    field
      reflect[_] : ∀ {x y} {f : hom x y} {x' y'}
                 → hom[ f ] x' y' → judgment[ reflect f ] x' y'
```

The displaced actions and injections follow from `reflect[_]` exactly
as the base ones follow from `reflect`.

```agda
    var[_] : ∀ {a} (a' : ob[ a ]) → term[ var a ] a'
    var[ a' ] = a' , idn[ a' ]

    covar[_] : ∀ {y} (y' : ob[ y ]) → coterm[ covar y ] y'
    covar[ y' ] = y' , idn[ y' ]

    act-π[_] : ∀ {x y} {f : hom x y} {x' y'} → hom[ f ] x' y'
             → ∀ {t : term x} (t' : term[ t ] x')
             → hom[ act-π f t ] (t' .fst) y'
    act-π[_] {y' = y'} f' t' = reflect[ f' ] _ (t' , covar[ y' ])

    coact-π[_] : ∀ {x y} {f : hom x y} {x' y'} → hom[ f ] x' y'
               → ∀ {e : coterm y} (e' : coterm[ e ] y')
               → hom[ coact-π f e ] x' (e' .fst)
    coact-π[_] {x' = x'} f' e' = reflect[ f' ] _ (var[ x' ] , e')

    inj⁻[_] : ∀ {x y z} {α : judgment x y} {x' y'} → judgment[ α ] x' y'
            → ∀ {p : hom y z} {z'} → hom[ p ] y' z'
            → judgment[ inj⁻ α p ] x' z'
    inj⁻[ α' ] p' _ γ' = α' _ (γ' .fst , (γ' .snd .fst , coact-π[ p' ] (γ' .snd)))

    inj⁺[_] : ∀ {x y z} {p : hom x y} {x' y'} → hom[ p ] x' y'
            → ∀ {β : judgment y z} {z'} → judgment[ β ] y' z'
            → judgment[ inj⁺ p β ] x' z'
    inj⁺[ p' ] β' _ γ' = β' _ ((γ' .fst .fst , act-π[ p' ] (γ' .fst)) , γ' .snd)
```

## What the spike settles

The mixed variance of `judgment` is the edge-indexed kind. Weakening
it over the edge gives an `rx.efam` whose diagonal is the
endo-judgments, and the two injections into a component are the two
composite operations with the head left general — `linj` the hand that
consumes the coterm slot, `rinj` the hand that consumes the term slot.
The lens formalism sees them only where the head is an endo-judgment;
`inj⁻` and `inj⁺` are defined off the diagonal too, and it is there
that they specialise to `composite⁻` and `composite⁺`.

Both unitors come from the unit fibers and readback. The absorptions
hold at the units those fibers project, the lens states its unitors at
`idn`, and readback is the bridge; `flanks-agree` is stated in the
same module and plays no part, and could not: the mid unitor is an
identification of judgments, while the flank coherence is an
identification of identifications in a hom type.

Both unitor shapes are available here. `absorb⁻` is the oplax one —
`linj` at reflexivity is the identity — and `absorb⁺` the lax one that
`runitor` records. Sterling admits either and warns against a lens
carrying both, on pain of losing propositionality of the structure
over a path-object base (`resources/sterling-reflexive-graph-lenses`,
`paper.tex:2203`; SOURCE-CHECKED), and draws the same analogy with
half-adjoint equivalences that `Test.SpikeUnitCanonical` makes
concrete for readback. This family carries both, so no propositionality
is claimed for the structure — a base that is not a path object had
already put it out of reach.

What does transfer is univalence of the display. `unb-disp-path-object`
hypothesises path objects of the diagonal components only, never of
the base; the components here are discrete, so both displays are
univalent outright.

The display is not the `judgment[_]` of a displayed deductive system.
That family is indexed by a base judgment and a displayed object over
each endpoint, and it displaces Σ-by-Σ from the displayed reflexive
graph, with `reflect[_]` the single field and the displaced actions
and injections its projections.
