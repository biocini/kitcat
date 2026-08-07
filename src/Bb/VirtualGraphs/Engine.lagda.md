The chosen-edge carrier: one family `idn` fills both argument
slots, and nothing aligns the reflection with it. A hand is named
for the slot its second factor enters — `⁻` the coterm slot, `⁺`
the term slot — so this dialect's `⁻` hand is `Framing`'s `⁺` hand
read at the diagonal `rx = corx = idn`, and dually; every
definition below is that diagonal instance, restated in its own
register. The engine is contractibility of `reflect`'s fiber over
its own image, from two tiers — composability and unitality — with
no readback, no interchange, and no embedding-condition hypothesis: each
hand's projected unit makes a reflected edge its own composite, so
the fiber is a composability fiber transported along one unit law.
The dictionary at the end reads the same carrier in
reflexive-graph terms, where every answer is definitional.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Engine where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Path.Base
open import Core.Transport.J using (subst; J)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding
  using (is-embedding; is-embedding→ap-equiv; ap-is-embedding)

open import Core.Rx.Type
open import Core.Rx.Base

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding using (is-representable; normal; opⱽ)
open import Bb.VirtualGraphs.Graph using (rxgraph; op-rxgraph)
```

## The vocabulary, axiom-free

```agda
module chosen {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  var : (a : ob) → term a
  var a = a , idn a

  covar : (y : ob) → coterm y
  covar y = y , idn y

  argue : ∀ {x y} → term x → coterm y → argument x y
  argue h k = h , k

  intro : ∀ {x y} → hom x y → term y
  intro {x} f = x , f

  elim : ∀ {x y} → hom x y → coterm x
  elim {y = y} f = y , f

  eval : ∀ {x y} → judgment x y → hom x y
  eval {x} {y} α = α (var x , covar y)

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (argue (var x) γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (argue t (covar y))

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact {x} f e = elim (reflect f (argue (var x) e))

  act : ∀ {x y} → hom x y → term x → term y
  act {y = y} f t = intro (reflect f (argue t (covar y)))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (argue (γ .fst) (coact g (γ .snd)))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect g (argue (act f (γ .fst)) (γ .snd))
```

## Composability, and the distributive laws

Each action distributes over its own hand's composition. Stated at
the edge level the anonymous endpoint is a parameter rather than a
component, so the two forms below are the same witness read at one
argument and then bundled.

```agda
  module composable
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable G (composite⁻ f g)))
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable G (composite⁺ f g)))
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

    coact-π-⨾⁻ : ∀ {x y z} (p : hom x y) (q : hom y z) (e : coterm z)
               → coact-π (p ⨾⁻ q) e ≡ coact-π p (coact q e)
    coact-π-⨾⁻ {x} p q e i = reflect-⨾⁻ p q i (argue (var x) e)

    act-π-⨾⁺ : ∀ {x y z} (p : hom x y) (q : hom y z) (t : term x)
             → act-π (p ⨾⁺ q) t ≡ act-π q (act p t)
    act-π-⨾⁺ {z = z} p q t i = reflect-⨾⁺ p q i (argue t (covar z))

    coact-⨾⁻ : ∀ {x y z} (p : hom x y) (q : hom y z) (e : coterm z)
             → coact (p ⨾⁻ q) e ≡ coact p (coact q e)
    coact-⨾⁻ p q e i = e .fst , coact-π-⨾⁻ p q e i

    act-⨾⁺ : ∀ {x y z} (p : hom x y) (q : hom y z) (t : term x)
           → act (p ⨾⁺ q) t ≡ act q (act p t)
    act-⨾⁺ p q t i = t .fst , act-π-⨾⁺ p q t i
```

## The engine

The chosen edge plays no part below. Everything runs on the unit
tier's own projected units — the tier's fiber centre is an edge
whose action is the identity action, which is the only property the
argument uses. `idn` is needed to state the vocabulary, and no
result here asks it to be a unit.

```agda
    module engine
      (unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd))
      (unit-fiber⁺ : ∀ x → is-contr (fiber (act-π   {x} {x}) snd))
      where

      unit⁻ unit⁺ : ∀ x → hom x x
      unit⁻ x = unit-fiber⁻ x .center .fst
      unit⁺ x = unit-fiber⁺ x .center .fst

      unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
      unit⁻-absorb x γ i = unit-fiber⁻ x .center .snd i γ

      unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
      unit⁺-absorb x t i = unit-fiber⁺ x .center .snd i t

      unit⁻-unique : ∀ x (e : hom x x)
                   → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ unit⁻ x
      unit⁻-unique x e abs = ap fst (sym (unit-fiber⁻ x .paths (e , funext abs)))

      unit⁺-unique : ∀ x (e : hom x x)
                   → (∀ t → act-π e t ≡ t .snd) → e ≡ unit⁺ x
      unit⁺-unique x e abs = ap fst (sym (unit-fiber⁺ x .paths (e , funext abs)))

      coact-unit : ∀ {y} (e : coterm y) → coact (unit⁻ y) e ≡ e
      coact-unit {y} e i = e .fst , unit⁻-absorb y e i

      act-unit : ∀ {x} (t : term x) → act (unit⁺ x) t ≡ t
      act-unit {x} t i = t .fst , unit⁺-absorb x t i

      composite⁻-unitr : ∀ {a y} (u : hom a y) → reflect u ≡ composite⁻ u (unit⁻ y)
      composite⁻-unitr u i γ = reflect u (argue (γ .fst) (coact-unit (γ .snd) (~ i)))

      composite⁺-unitl : ∀ {x c} (u : hom x c) → reflect u ≡ composite⁺ (unit⁺ x) u
      composite⁺-unitl u i γ = reflect u (argue (act-unit (γ .fst) (~ i)) (γ .snd))
```

A reflected edge is its own hand's composite with the projected
unit, so the composability fiber over that composite is the fiber
over the reflection: each hand delivers the same contractibility,
and with it left-cancellability, embedding-hood, and the iterated
`ap`-equivalence.

```agda
      reflect-fiber-contr⁻
        : ∀ {x y} (f : hom x y) → is-contr (is-representable G (reflect f))
      reflect-fiber-contr⁻ {y = y} f =
        subst (λ α → is-contr (is-representable G α))
              (sym (composite⁻-unitr f)) (contr⁻ f (unit⁻ y))

      reflect-fiber-contr⁺
        : ∀ {x y} (f : hom x y) → is-contr (is-representable G (reflect f))
      reflect-fiber-contr⁺ {x} f =
        subst (λ α → is-contr (is-representable G α))
              (sym (composite⁺-unitl f)) (contr⁺ (unit⁺ x) f)

      reflect-lc : ∀ {x y} {f g : hom x y} → reflect f ≡ reflect g → f ≡ g
      reflect-lc {y = y} {f} {g} p =
        ap fst (sym (c .paths (f , p)) ∙ c .paths (normal G g))
        where c = reflect-fiber-contr⁻ g

      reflect-embedding : ∀ {x y} → is-embedding (reflect {x} {y})
      reflect-embedding α c@(f , p) =
        subst (λ β → is-prop (is-representable G β)) p
              (is-contr→is-prop (reflect-fiber-contr⁻ f)) c

      ap-reflect-equiv
        : ∀ {x y} {f g : hom x y} → is-equiv (ap (reflect {x} {y}) {f} {g})
      ap-reflect-equiv = is-embedding→ap-equiv reflect-embedding

      ap-reflect-embedding
        : ∀ {x y} {f g : hom x y} → is-embedding (ap (reflect {x} {y}) {f} {g})
      ap-reflect-embedding = ap-is-embedding reflect-embedding
```

Associativity and the unit laws come per hand: both bracketings
represent one judgment, by the outer head's rewriting followed by
that hand's distributive law, and left-cancellation descends the
identity from judgments to edges. Readback is not among the inputs.

```agda
      composite⁻-assoc
        : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → composite⁻ (f ⨾⁻ g) h ≡ composite⁻ f (g ⨾⁻ h)
      composite⁻-assoc f g h = funext λ γ →
        (λ i → reflect-⨾⁻ f g i (argue (γ .fst) (coact h (γ .snd))))
        ∙ (λ i → reflect f (argue (γ .fst) (coact-⨾⁻ g h (γ .snd) (~ i))))

      assoc⁻ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
             → (f ⨾⁻ g) ⨾⁻ h ≡ f ⨾⁻ (g ⨾⁻ h)
      assoc⁻ f g h = reflect-lc
        ( reflect-⨾⁻ (f ⨾⁻ g) h
        ∙ composite⁻-assoc f g h
        ∙ sym (reflect-⨾⁻ f (g ⨾⁻ h)) )

      composite⁺-assoc
        : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → composite⁺ f (g ⨾⁺ h) ≡ composite⁺ (f ⨾⁺ g) h
      composite⁺-assoc f g h = funext λ γ →
        (λ i → reflect-⨾⁺ g h i (argue (act f (γ .fst)) (γ .snd)))
        ∙ (λ i → reflect h (argue (act-⨾⁺ f g (γ .fst) (~ i)) (γ .snd)))

      assoc⁺ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
             → f ⨾⁺ (g ⨾⁺ h) ≡ (f ⨾⁺ g) ⨾⁺ h
      assoc⁺ f g h = reflect-lc
        ( reflect-⨾⁺ f (g ⨾⁺ h)
        ∙ composite⁺-assoc f g h
        ∙ sym (reflect-⨾⁺ (f ⨾⁺ g) h) )

      unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ unit⁻ y ≡ f
      unitr⁻ {y = y} f =
        reflect-lc (reflect-⨾⁻ f (unit⁻ y) ∙ sym (composite⁻-unitr f))

      unitl⁺ : ∀ {x y} (f : hom x y) → unit⁺ x ⨾⁺ f ≡ f
      unitl⁺ {x} f =
        reflect-lc (reflect-⨾⁺ (unit⁺ x) f ∙ sym (composite⁺-unitl f))
```

## Stability

A third tier rests on one hypothesis, `rb`. It gives a path for every
edge, identifying that edge with the evaluation of its own
reflection. Composability plays no part below. The unit tier lends
only its two projected units and their absorptions.

The tier does not need the unit tier's own contractibility.
Evaluation at either hand's axiom is that hand's action applied to
its own fiber point. Both facts hold by `refl`.

```agda
      module stability (rb : ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f) where

        eval-is-coact : ∀ {x} (e : hom x x) → eval (reflect e) ≡ coact-π e (covar x)
        eval-is-coact _ = refl

        eval-is-act : ∀ {x} (e : hom x x) → eval (reflect e) ≡ act-π e (var x)
        eval-is-act _ = refl
```

Compose a projected unit's absorption at its own axiom with `rb` at
that unit. The composite identifies the unit with `idn`. Each hand's
absorption then transports onto the chosen edge. The two hands'
units coincide. The same composite identifies any edge whose action
is the identity action with `idn` directly. It needs no detour
through a projected unit.

```agda
        unit⁻-is-idn : ∀ x → unit⁻ x ≡ idn x
        unit⁻-is-idn x = sym (rb (unit⁻ x)) ∙ unit⁻-absorb x (covar x)

        unit⁺-is-idn : ∀ x → unit⁺ x ≡ idn x
        unit⁺-is-idn x = sym (rb (unit⁺ x)) ∙ unit⁺-absorb x (var x)

        units-agree : ∀ x → unit⁻ x ≡ unit⁺ x
        units-agree x = unit⁻-is-idn x ∙ sym (unit⁺-is-idn x)

        idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
        idn-absorb⁻ x γ =
          ap (λ e → coact-π e γ) (sym (unit⁻-is-idn x)) ∙ unit⁻-absorb x γ

        idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
        idn-absorb⁺ x t =
          ap (λ e → act-π e t) (sym (unit⁺-is-idn x)) ∙ unit⁺-absorb x t

        unit⁻-canonical : ∀ x (e : hom x x)
                        → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ idn x
        unit⁻-canonical x e abs = sym (rb e) ∙ abs (covar x)

        unit⁺-canonical : ∀ x (e : hom x x)
                        → (∀ t → act-π e t ≡ t .snd) → e ≡ idn x
        unit⁺-canonical x e abs = sym (rb e) ∙ abs (var x)
```

A candidate unit is an edge together with a proof that its action is
the identity action. It is an element of the fiber the unit tier
contracts. Such a candidate reaches `idn` two ways: through the
fiber's own projected unit, or straight through `rb`. Both routes
come from one function of the candidate, `route⁻` and `route⁺`
below.

The two routes agree naturally in a path between two candidates.
`route⁻-natural` and `route⁺-natural` prove this by induction on
that path. The detour through the projected unit then cancels
against the direct route. `unique-agrees⁻` and `unique-agrees⁺`
state that cancellation.

```agda
        route⁻ : ∀ x (c : fiber (coact-π {x} {x}) snd) → c .fst ≡ idn x
        route⁻ x c = sym (rb (c .fst)) ∙ (λ i → c .snd i (covar x))

        route⁺ : ∀ x (c : fiber (act-π {x} {x}) snd) → c .fst ≡ idn x
        route⁺ x c = sym (rb (c .fst)) ∙ (λ i → c .snd i (var x))

        route⁻-natural
          : ∀ x (c₀ c₁ : fiber (coact-π {x} {x}) snd) (γ : c₀ ≡ c₁)
          → route⁻ x c₀ ≡ ap fst γ ∙ route⁻ x c₁
        route⁻-natural x c₀ c₁ γ =
          J (λ c₁' γ' → route⁻ x c₀ ≡ ap fst γ' ∙ route⁻ x c₁')
            (sym (Path.unitl (route⁻ x c₀))) γ

        route⁺-natural
          : ∀ x (c₀ c₁ : fiber (act-π {x} {x}) snd) (γ : c₀ ≡ c₁)
          → route⁺ x c₀ ≡ ap fst γ ∙ route⁺ x c₁
        route⁺-natural x c₀ c₁ γ =
          J (λ c₁' γ' → route⁺ x c₀ ≡ ap fst γ' ∙ route⁺ x c₁')
            (sym (Path.unitl (route⁺ x c₀))) γ

        unique-agrees⁻
          : ∀ x (e : hom x x) (abs : ∀ γ → coact-π e γ ≡ γ .snd)
          → unit⁻-unique x e abs ∙ unit⁻-is-idn x ≡ unit⁻-canonical x e abs
        unique-agrees⁻ x e abs =
          ap (sym (ap fst γ) ∙_) (route⁻-natural x (unit-fiber⁻ x .center) c γ)
          ∙ Path.assoc (sym (ap fst γ)) (ap fst γ) (route⁻ x c)
          ∙ ap (_∙ route⁻ x c) (Path.invl (ap fst γ))
          ∙ Path.unitl (route⁻ x c)
          where
            c : fiber (coact-π {x} {x}) snd
            c = e , funext abs

            γ : unit-fiber⁻ x .center ≡ c
            γ = unit-fiber⁻ x .paths c

        unique-agrees⁺
          : ∀ x (e : hom x x) (abs : ∀ t → act-π e t ≡ t .snd)
          → unit⁺-unique x e abs ∙ unit⁺-is-idn x ≡ unit⁺-canonical x e abs
        unique-agrees⁺ x e abs =
          ap (sym (ap fst γ) ∙_) (route⁺-natural x (unit-fiber⁺ x .center) c γ)
          ∙ Path.assoc (sym (ap fst γ)) (ap fst γ) (route⁺ x c)
          ∙ ap (_∙ route⁺ x c) (Path.invl (ap fst γ))
          ∙ Path.unitl (route⁺ x c)
          where
            c : fiber (act-π {x} {x}) snd
            c = e , funext abs

            γ : unit-fiber⁺ x .center ≡ c
            γ = unit-fiber⁺ x .paths c
```

The coherence pins a readback family at the flanks. It reads the
family's value at each hand's projected unit. It transports that
value to `idn` through that hand's own absorption. It then asks the
family's own value at `idn` to agree with the transported value.

`flank⁻-of` and `flank⁺-of` compute the transported side.
`absorb-coh` states the agreement for both hands at once. The
stability tier wraps a readback family together with a witness of
this coherence inside contractibility. It does not assume that the
pair is a mere proposition on its own.

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

        readback : Type (o ⊔ h)
        readback = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f

        absorb-coh : readback → Type (o ⊔ h)
        absorb-coh u =
          ∀ x → (u (idn x) ≡ flank⁻-of x (u (unit⁻ x)))
              × (u (idn x) ≡ flank⁺-of x (u (unit⁺ x)))

        is-stable : Type (o ⊔ h)
        is-stable = is-contr (Σ {A = readback} absorb-coh)

        is-stable-is-prop : is-prop is-stable
        is-stable-is-prop = is-contr-is-prop _
```

Wrapping the pair in contractibility matters, and is not decoration.
The coherence alone does not make the pair propositional as a
structural fact. Every value the coherence reads sits at an
endomorphism: `idn`, or one of the two projected units. A `half-twist` is
a self-path attached to every edge. Take a half-twist that vanishes at
every endomorphism, the hypothesis `coh-half-twist` calls `te`.

Composing it onto a readback family perturbs the family without
touching any value the coherence reads. The perturbed pair is
coherent again, by `coh-half-twist`. Suppose the pair type were a mere
proposition on its own. Then the perturbed pair and the original
pair would be equal. `half-adjoint-forces-truncation` reads that
equality apart.

It shows the half-twist is trivial everywhere, at every edge and not only
at the endomorphisms. Untruncated hom types can carry self-paths
that are not trivial. This route does not make the pair propositional
in general. This tier instead posits contractibility directly, as a
hypothesis about the graph. It does not derive contractibility from
the coherence.

```agda
        half-twist : Type (o ⊔ h)
        half-twist = ∀ {x y} (f : hom x y) → f ≡ f

        _∙ᵗ_ : readback → half-twist → readback
        (u ∙ᵗ t) f = u f ∙ t f

        half-adjoint : Type (o ⊔ h)
        half-adjoint = Σ {A = readback} absorb-coh

        module _ (t : half-twist) (te : ∀ x (e : hom x x) → t e ≡ refl) where

          agree : ∀ (u : readback) x (e : hom x x) → (u ∙ᵗ t) e ≡ u e
          agree u x e = ap (u e ∙_) (te x e) ∙ Path.unitr (u e)

          coh-half-twist : (u : readback) → absorb-coh u → absorb-coh (u ∙ᵗ t)
          coh-half-twist u c x .fst =
            agree u x (idn x) ∙ c x .fst
            ∙ sym (ap (flank⁻-of x) (agree u x (unit⁻ x)))
          coh-half-twist u c x .snd =
            agree u x (idn x) ∙ c x .snd
            ∙ sym (ap (flank⁺-of x) (agree u x (unit⁺ x)))

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
          → (t : half-twist) (te : ∀ x (e : hom x x) → t e ≡ refl)
          → ∀ {x y} (f : hom x y) → t f ≡ refl
        half-adjoint-forces-truncation P S t te {x} {y} f =
          cancel (S .fst f) (t f) (ap (λ w → w {x} {y} f) (ap fst step))
          where
            step : S ≡ (S .fst ∙ᵗ t , coh-half-twist t te (S .fst) (S .snd))
            step = P S _
```

## The reflexive-graph dictionary

The chosen edge is a reflexivity datum: a term at `x` is the cofan
of `x`, a coterm the fan, and the two axiom halves are the centres
reflexivity provides. Every proof is `refl`, so each answer is a
definitional equality: the two languages describe one object.

```agda
module dict {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  open chosen G idn

  graph : reflexive-graph o h
  graph = rxgraph G idn

  term-is-cofan  : ∀ x → term x ≡ rx.cofan graph x
  term-is-cofan  _ = refl

  coterm-is-fan  : ∀ y → coterm y ≡ rx.fan graph y
  coterm-is-fan  _ = refl

  var-is-center   : ∀ x → var x ≡ rx.cofan-center graph x
  var-is-center   _ = refl

  covar-is-center : ∀ y → covar y ≡ rx.fan-center graph y
  covar-is-center _ = refl

  term-op   : ∀ x → rx.fan (rx.op graph) x ≡ term x
  term-op   _ = refl

  coterm-op : ∀ y → rx.cofan (rx.op graph) y ≡ coterm y
  coterm-op _ = refl
```

Each action acts fiberwise over the anonymous endpoint, and at its
own axiom half returns the evaluation of the reflected edge —
readback is the single statement that both actions are the identity
there, the one place the two hands meet.

```agda
  act-fiberwise : ∀ {x y} (f : hom x y) (t : term x) → act f t .fst ≡ t .fst
  act-fiberwise _ _ = refl

  coact-fiberwise : ∀ {x y} (f : hom x y) (e : coterm y) → coact f e .fst ≡ e .fst
  coact-fiberwise _ _ = refl

  act-axiom : ∀ {x y} (f : hom x y) → act f (var x) ≡ (x , eval (reflect f))
  act-axiom _ = refl

  coact-axiom : ∀ {x y} (f : hom x y) → coact f (covar y) ≡ (y , eval (reflect f))
  coact-axiom _ = refl
```

The coslice at `a` carries the edges out of `a`, with a displayed
edge over `p` recording that its target is a composite; displayed
reflexivity is the flank absorption. Against that display the `⁻`
hand's composability is the covariant fibration condition, its
pushforward the composition, and its lift the head-rewriting
witness. The `⁺` hand is the mirror: the slice at a fixed target is
a contravariant fibration whose pullback is the composition.

```agda
  module hand⁻
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁻ f g)))
    where

    _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾ g = contr⁻ f g .center .fst

    reflect-⨾ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → reflect (f ⨾ g) ≡ composite⁻ f g
    reflect-⨾ f g = contr⁻ f g .center .snd

    module unital
      (absorb⁻ : ∀ {x y} (f : hom x y) → reflect f ≡ composite⁻ f (idn y))
      where

      coslice : ob → rx.disp graph h (o ⊔ h)
      coslice a .reflexive-graphᴰ.vtx z          = hom a z
      coslice a .reflexive-graphᴰ.edge y z p u w = reflect w ≡ composite⁻ u p
      coslice a .reflexive-graphᴰ.rx u           = absorb⁻ u

      coslice-fibration : ∀ a → rx.is-cov-fibration graph (coslice a)
      coslice-fibration _ _ _ p u = contr⁻ u p

      module F (a : ob) = rx.cov-fibration graph (coslice a) (coslice-fibration a)

      push-is-comp : ∀ a y z (p : hom y z) (u : hom a y) → F.push a y z p u ≡ u ⨾ p
      push-is-comp _ _ _ _ _ = refl

      lift-is-witness : ∀ a y z (p : hom y z) (u : hom a y)
                      → F.lift a y z p u ≡ reflect-⨾ u p
      lift-is-witness _ _ _ _ _ = refl

  module hand⁺
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁺ f g)))
    (absorb⁺ : ∀ {x y} (f : hom x y) → reflect f ≡ composite⁺ (idn x) f)
    where

    _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾ g = contr⁺ f g .center .fst

    slice : ob → rx.disp graph h (o ⊔ h)
    slice c .reflexive-graphᴰ.vtx x          = hom x c
    slice c .reflexive-graphᴰ.edge x y p u w = reflect u ≡ composite⁺ p w
    slice c .reflexive-graphᴰ.rx u           = absorb⁺ u

    slice-fibration : ∀ c → rx.is-ctrv-fibration graph (slice c)
    slice-fibration _ _ _ p w = contr⁺ p w

    module F (c : ob) = rx.ctrv-fibration graph (slice c) (slice-fibration c)

    pull-is-comp : ∀ c x y (p : hom x y) (w : hom y c) → F.pull c x y p w ≡ p ⨾ w
    pull-is-comp _ _ _ _ _ = refl
```

## The involution

The opposite graph of the dictionary is the opposite of its graph
(`op-rxgraph`), and opposition is involutive on the nose. The two
actions exchange on elements; judgments exchange only against the
swap of the argument pair, which is its own inverse definitionally,
and both `reflect` and the composite judgments commute with it at
the level of functions — so the exchange carries no coherence data,
and a tier statement transfers along `swap-judgment` by one `ap`.

```agda
module _ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  private
    module L  = chosen G idn
    module Lᵒ = chosen (opⱽ G) idn

  act-op : ∀ {x y} (f : hom y x) (t : coterm x) → Lᵒ.act f t ≡ L.coact f t
  act-op _ _ = refl

  coact-op : ∀ {x y} (f : hom y x) (t : term y) → Lᵒ.coact f t ≡ L.act f t
  coact-op _ _ = refl

  swap-arg  : ∀ {x z} → virtual-graph.argument (opⱽ G) x z → argument z x
  swap-arg  γ = γ .snd , γ .fst

  swap-arg⁻ : ∀ {x z} → argument z x → virtual-graph.argument (opⱽ G) x z
  swap-arg⁻ δ = δ .snd , δ .fst

  swap-judgment : ∀ {x z} → judgment z x → virtual-graph.judgment (opⱽ G) x z
  swap-judgment α γ = α (swap-arg γ)

  swap-invol : ∀ {x z} (γ : virtual-graph.argument (opⱽ G) x z)
             → swap-arg⁻ (swap-arg γ) ≡ γ
  swap-invol _ = refl

  reflect-op : ∀ {x z} (f : hom z x)
             → virtual-graph.reflect (opⱽ G) f ≡ swap-judgment (reflect f)
  reflect-op _ = refl

  composite-op : ∀ {x y z} (f : hom y x) (g : hom z y)
               → Lᵒ.composite⁻ f g ≡ swap-judgment (L.composite⁺ g f)
  composite-op _ _ = refl
```
