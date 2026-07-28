The stability tier in the form the design note specifies: the fiber of
flank-restriction over a canonically constructed flank family.

The unit tier is the emb-action package — each hand's action at the
chosen edge an equivalence, together with that hand's idempotence — and
not the composition-action forms. That choice is what makes the
canonical flank paths exist *readback-free*, so that the stability
tier's statement is not circular over them.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.NaiveVirtualGraph.Gist.StableFiber where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom)
open import Core.Path.Base
open import Core.Equiv.Base using (_≃_; is-equiv; iso→equiv; eqv-fibers; is-contr-equiv)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; ×-is-hlevel)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Equiv.Properties using (_∙e_; esym; is-equiv-is-prop; Σ-equiv-snd)
open import Core.Function.Embedding
  using (equiv→lc; is-equiv→is-embedding; is-embedding→ap-equiv)
open import Core.Groupoid.Virtual using (module yon-unbiased)

open import Bb.NaiveVirtualGraph.Base
```

## The vocabulary

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G
  open vocab G

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (argue (γ .fst) (coact g (γ .snd)))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect g (argue (act f (γ .fst)) (γ .snd))
```

## Composability

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

    coact-π-⨾⁻ : ∀ {x y z} (p : hom x y) (q : hom y z) (e : coterm z)
               → coact-π (p ⨾⁻ q) e ≡ coact-π p (coact q e)
    coact-π-⨾⁻ {x} p q e i = reflect-⨾⁻ p q i (argue (var x) e)

    act-π-⨾⁺ : ∀ {x y z} (p : hom x y) (q : hom y z) (t : term x)
             → act-π (p ⨾⁺ q) t ≡ act-π q (act p t)
    act-π-⨾⁺ {z = z} p q t i = reflect-⨾⁺ p q i (argue t (covar z))
```

## The unit tier, emb-action form

Each hand's action at the chosen edge is an equivalence at every far
endpoint, and that hand's composition is idempotent there. Neither
half suffices alone — the equivalences are powerless without the
idempotence, and the idempotence is slack without the equivalences.

```agda
    module unital
      (eqv⁻ : ∀ {x v} → is-equiv (λ (b : hom x v) → coact-π (idn x) (v , b)))
      (eqv⁺ : ∀ {w x} → is-equiv (λ (a : hom w x) → act-π (idn x) (w , a)))
      (rep-idem⁻ : ∀ x → reflect (idn x) ≡ composite⁻ (idn x) (idn x))
      (rep-idem⁺ : ∀ x → reflect (idn x) ≡ composite⁺ (idn x) (idn x))
      where
```

The chosen edge represents its own composite with itself, on each
hand. Stated at the judgment rather than at the edge, the datum needs
no composition to be written down — and the composition's uniqueness
turns it into the edge-level idempotence.

```agda
      idem⁻ : ∀ x → idn x ⨾⁻ idn x ≡ idn x
      idem⁻ x = ap fst (contr⁻ (idn x) (idn x) .paths (idn x , rep-idem⁻ x))

      idem⁺ : ∀ x → idn x ⨾⁺ idn x ≡ idn x
      idem⁺ x = ap fst (contr⁺ (idn x) (idn x) .paths (idn x , rep-idem⁺ x))
```

Absorption follows by cancelling the equivalence against the
idempotence, over that hand's distributive law. Readback is not in
scope.

```agda
      idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
      idn-absorb⁻ x γ = equiv→lc eqv⁻ step
        where
          step : coact-π (idn x) (γ .fst , coact-π (idn x) γ)
               ≡ coact-π (idn x) (γ .fst , γ .snd)
          step = sym (coact-π-⨾⁻ (idn x) (idn x) γ)
               ∙ ap (λ s → coact-π s γ) (idem⁻ x)

      idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
      idn-absorb⁺ x t = equiv→lc eqv⁺ step
        where
          step : act-π (idn x) (t .fst , act-π (idn x) t)
               ≡ act-π (idn x) (t .fst , t .snd)
          step = sym (act-π-⨾⁺ (idn x) (idn x) t)
               ∙ ap (λ s → act-π s t) (idem⁺ x)
```

## The canonical flank, and the tier

Evaluation at the axiom is each action read at its own axiom half, so
each hand's absorption instantiated there is a flank canonical —
constructed, not assumed.

```agda
      canonical-flank⁻ : ∀ x → eval (reflect (idn x)) ≡ idn x
      canonical-flank⁻ x = idn-absorb⁻ x (covar x)

      canonical-flank⁺ : ∀ x → eval (reflect (idn x)) ≡ idn x
      canonical-flank⁺ x = idn-absorb⁺ x (var x)

      flank-restrict : readback → (∀ x → eval (reflect (idn x)) ≡ idn x)
      flank-restrict u x = u (idn x)

      is-stable : Type (o ⊔ h)
      is-stable = is-contr (Σ u ∶ readback , (∀ x → u (idn x) ≡ canonical-flank⁻ x))

      unit : is-stable → readback
      unit S = S .center .fst
```

The pin lemma is generic in the pin, so the same statement with the
other hand's canonical is available on the same terms. Asking for both
at once is a different thing: it forces the two canonicals to agree,
which is a path *between* flank paths.

```agda
      is-stable⁺ : Type (o ⊔ h)
      is-stable⁺ = is-contr (Σ u ∶ readback , (∀ x → u (idn x) ≡ canonical-flank⁺ x))

      is-stable± : Type (o ⊔ h)
      is-stable± = is-contr
        (Σ u ∶ readback , (∀ x → u (idn x) ≡ canonical-flank⁻ x)
                        × (∀ x → u (idn x) ≡ canonical-flank⁺ x))

      both→agree
        : (Σ u ∶ readback , (∀ x → u (idn x) ≡ canonical-flank⁻ x)
                          × (∀ x → u (idn x) ≡ canonical-flank⁺ x))
        → ∀ x → canonical-flank⁻ x ≡ canonical-flank⁺ x
      both→agree (u , p , q) x = sym (p x) ∙ q x

      stable±→agree : is-stable± → ∀ x → canonical-flank⁻ x ≡ canonical-flank⁺ x
      stable±→agree S = both→agree (S .center)
```

Taking the two as a *product of contractibility statements* rather
than one contractibility of a joint package avoids that: each factor
is separately a fiber over a constructed pin, and the pair is
symmetric under the exchange of hands.

```agda
      is-stable-pair : Type (o ⊔ h)
      is-stable-pair = is-stable × is-stable⁺
```

The pin is a *constructed* family, and the tier is the fiber of
restriction over it. That is what distinguishes this from asking a
readback family to cohere with itself: nothing here reads `u` twice.

## The op dictionary

`opⱽ` reverses edges and reads `reflect` against the swapped argument.
Terms and coterms exchange, and each axiom half becomes the other, so
the two actions exchange **definitionally** — and with them readback,
which evaluates at both halves at once.

```agda
opⱽ : ∀ {o h} → virtual-graph o h → virtual-graph o h
opⱽ G .virtual-graph.ob          = virtual-graph.ob G
opⱽ G .virtual-graph.hom x y     = virtual-graph.hom G y x
opⱽ G .virtual-graph.idn         = virtual-graph.idn G
opⱽ G .virtual-graph.reflect f γ = virtual-graph.reflect G f (γ .snd , γ .fst)

opⱽ-invol : ∀ {o h} (G : virtual-graph o h) → opⱽ (opⱽ G) ≡ G
opⱽ-invol _ = refl

module dict {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G

  term-op : ∀ x → virtual-graph.term (opⱽ G) x ≡ coterm x
  term-op _ = refl

  coterm-op : ∀ y → virtual-graph.coterm (opⱽ G) y ≡ term y
  coterm-op _ = refl

  var-op : ∀ x → virtual-graph.var (opⱽ G) x ≡ virtual-graph.covar G x
  var-op _ = refl

  covar-op : ∀ x → virtual-graph.covar (opⱽ G) x ≡ virtual-graph.var G x
  covar-op _ = refl

  coact-π-op : ∀ {x y} (f : hom y x) (t : term y)
             → vocab.coact-π (opⱽ G) f t ≡ vocab.act-π G f t
  coact-π-op _ _ = refl

  act-π-op : ∀ {x y} (f : hom y x) (e : coterm x)
           → vocab.act-π (opⱽ G) f e ≡ vocab.coact-π G f e
  act-π-op _ _ = refl

  readback-op : vocab.readback (opⱽ G) ≃ vocab.readback G
  readback-op = iso→equiv (λ u f → u f) (λ u f → u f) (λ _ → refl) (λ _ → refl)
```

So the unit tier's two equivalence fields exchange on the nose.
Readback's two graphs give the same family pointwise — evaluation at
the axiom reads both halves at once, and opposition swaps them — and
differ only in the order of the two implicit endpoints, so they are
interconvertible with `refl` round trips. What does not
exchange definitionally is the composite judgment: an argument's two
slots swap, so `composite⁻` at the opposite is `composite⁺` read
against the swap.

```agda
  swap-arg : ∀ {x z} → virtual-graph.argument (opⱽ G) x z → argument z x
  swap-arg γ = γ .snd , γ .fst

  swap-judgment : ∀ {x z} → judgment z x → virtual-graph.judgment (opⱽ G) x z
  swap-judgment α γ = α (swap-arg γ)

  composite⁻-op : ∀ {x y z} (f : hom y x) (g : hom z y)
                → composite⁻ (opⱽ G) f g ≡ swap-judgment (composite⁺ G g f)
  composite⁻-op _ _ = refl

  reflect-op : ∀ {x z} (f : hom z x)
             → virtual-graph.reflect (opⱽ G) f ≡ swap-judgment (reflect f)
  reflect-op _ = refl

  composite⁺-op : ∀ {x y z} (f : hom y x) (g : hom z y)
                → composite⁺ (opⱽ G) f g ≡ swap-judgment (composite⁻ G g f)
  composite⁺-op _ _ = refl
```

The swap is a definitional involution on judgments, so it is an
equivalence with `refl` round trips, and `ap` of it is an equivalence
too. Representability therefore transports across the swap.

```agda
  swap-judgment⁻ : ∀ {x z} → virtual-graph.judgment (opⱽ G) x z → judgment z x
  swap-judgment⁻ β δ = β (δ .snd , δ .fst)

  swap-eqv : ∀ {x z} → judgment z x ≃ virtual-graph.judgment (opⱽ G) x z
  swap-eqv = iso→equiv swap-judgment swap-judgment⁻ (λ _ → refl) (λ _ → refl)

  ap-swap : ∀ {x z} {α β : judgment z x}
          → is-equiv (ap (swap-judgment {x} {z}) {α} {β})
  ap-swap = is-embedding→ap-equiv (is-equiv→is-embedding (swap-eqv .snd))

  rep-op : ∀ {x z} (β : judgment z x)
         → is-representable β
         ≃ sequents.is-representable (opⱽ G) (swap-judgment β)
  rep-op β = Σ-equiv-snd (λ m → ap swap-judgment , ap-swap)
```

## The composability tier, transported

Stated as a pair so that opposition can exchange the two fields. Each
is a contractibility, so the tier is a proposition and the round trip
needs no coherence.

```agda
is-composable : ∀ {o h} (G : virtual-graph o h) → Type (o ⊔ h)
is-composable G =
    (∀ {x y z} (f : virtual-graph.hom G x y) (g : virtual-graph.hom G y z)
       → is-contr (sequents.is-representable G (composite⁻ G f g)))
  × (∀ {x y z} (f : virtual-graph.hom G x y) (g : virtual-graph.hom G y z)
       → is-contr (sequents.is-representable G (composite⁺ G f g)))

is-composable-is-prop : ∀ {o h} (G : virtual-graph o h) → is-prop (is-composable G)
is-composable-is-prop G =
  ×-is-hlevel 1
    (Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
     Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _)
    (Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
     Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _)

composable-op : ∀ {o h} (G : virtual-graph o h)
              → is-composable G → is-composable (opⱽ G)
composable-op G (c⁻ , c⁺) =
    (λ f g → is-contr-equiv (esym (dict.rep-op G _)) (c⁺ g f))
  , (λ f g → is-contr-equiv (esym (dict.rep-op G _)) (c⁻ g f))

composable-op-invol
  : ∀ {o h} (G : virtual-graph o h) (C : is-composable G)
  → composable-op (opⱽ G) (composable-op G C) ≡ C
composable-op-invol G C = is-composable-is-prop G _ _
```

Each hand's composition at the opposite is the other hand's here, by
the fiber's uniqueness rather than by conversion — the reflected
composite differs from its mate by the swap.

```agda
⨾-op : ∀ {o h} (G : virtual-graph o h) (C : is-composable G)
       {x y z} (f : virtual-graph.hom G y x) (g : virtual-graph.hom G z y)
     → composable-op G C .fst f g .center .fst ≡ C .snd g f .center .fst
⨾-op G C f g =
  ap fst (composable-op G C .fst f g .paths
           (C .snd g f .center .fst
           , ap (dict.swap-judgment G) (C .snd g f .center .snd)))
```

## The unit tier, transported

The two equivalence fields exchange definitionally; only the two
idempotences move, and they move along `⨾-op`.

```agda
is-unital : ∀ {o h} (G : virtual-graph o h) → Type (o ⊔ h)
is-unital G =
    (∀ {x v} → is-equiv (λ (b : virtual-graph.hom G x v)
                           → vocab.coact-π G (virtual-graph.idn G x) (v , b)))
  × (∀ {w x} → is-equiv (λ (a : virtual-graph.hom G w x)
                           → vocab.act-π G (virtual-graph.idn G x) (w , a)))
  × (∀ x → virtual-graph.reflect G (virtual-graph.idn G x)
         ≡ composite⁻ G (virtual-graph.idn G x) (virtual-graph.idn G x))
  × (∀ x → virtual-graph.reflect G (virtual-graph.idn G x)
         ≡ composite⁺ G (virtual-graph.idn G x) (virtual-graph.idn G x))
```

The tier no longer mentions a composition, so it is a predicate on the
bare virtual graph. Opposition exchanges the two equivalences on the
nose and carries each idempotence across the swap.

```agda
unital-op : ∀ {o h} (G : virtual-graph o h) → is-unital G → is-unital (opⱽ G)
unital-op G (e⁻ , e⁺ , i⁻ , i⁺) =
  e⁺ , e⁻ , (λ x → ap (dict.swap-judgment G) (i⁺ x))
          , (λ x → ap (dict.swap-judgment G) (i⁻ x))
```

The swap is a definitional involution, so `ap` of it squares to the
identity on the nose and the round trip is `refl` — no coherence to
supply.

```agda
unital-op-invol
  : ∀ {o h} (G : virtual-graph o h) (U : is-unital G)
  → unital-op (opⱽ G) (unital-op G U) ≡ U
unital-op-invol G U = refl
```

## Stability as an equivalence

Restriction to the identities does not mention either hand, and it
does not mention the unit tier at all — only `idn` and `readback`. Ask
it to be an *equivalence* and every pinned package becomes a fiber of
it, so both canonical flanks are covered by one statement, and the
statement is a proposition because `is-equiv` always is.

```agda
module stable {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G

  flank : Type (o ⊔ h)
  flank = ∀ x → eval (reflect (idn x)) ≡ idn x

  restrict : vocab.readback G → flank
  restrict u x = u (idn x)

  is-stable : Type (o ⊔ h)
  is-stable = is-equiv restrict

  pinned-contr : is-stable → (t₀ : flank) → is-contr (fiber restrict t₀)
  pinned-contr S t₀ = eqv-fibers S t₀
```

The codomain is fixed by the graph, so *any* pin gives a contractible
package — in particular either hand's canonical flank, with neither
privileged and no comparison between them.

## Opposition

Evaluation at the axiom reads both halves at once, and opposition
swaps them, so the flank type is literally shared between a graph and
its opposite; restriction differs only by the endpoint-swapping
isomorphism on readback.

```agda
flank-op : ∀ {o h} (G : virtual-graph o h) → stable.flank (opⱽ G) ≡ stable.flank G
flank-op _ = refl

restrict-op
  : ∀ {o h} (G : virtual-graph o h) (u : vocab.readback (opⱽ G))
  → stable.restrict (opⱽ G) u ≡ stable.restrict G (dict.readback-op G .fst u)
restrict-op _ _ = refl

stable-op : ∀ {o h} (G : virtual-graph o h)
          → stable.is-stable G → stable.is-stable (opⱽ G)
stable-op G S = (dict.readback-op G ∙e (stable.restrict G , S)) .snd

stable-op-invol
  : ∀ {o h} (G : virtual-graph o h) (S : stable.is-stable G)
  → stable-op (opⱽ G) (stable-op G S) ≡ S
stable-op-invol G S = is-equiv-is-prop _ _ _
```

## The bundle, and its opposition

```agda
record is-deductive-system {o h} (G : virtual-graph o h) : Type (o ⊔ h) where
  field
    composable : is-composable G
    unital     : is-unital G
    stable     : stable.is-stable G

deductive-op : ∀ {o h} (G : virtual-graph o h)
             → is-deductive-system G → is-deductive-system (opⱽ G)
deductive-op G D .is-deductive-system.composable =
  composable-op G (D .is-deductive-system.composable)
deductive-op G D .is-deductive-system.unital =
  unital-op G (D .is-deductive-system.unital)
deductive-op G D .is-deductive-system.stable =
  stable-op G (D .is-deductive-system.stable)
```

Two of the three components round-trip for free, being propositional.

```agda
deductive-op-composable-invol
  : ∀ {o h} (G : virtual-graph o h) (D : is-deductive-system G)
  → is-deductive-system.composable (deductive-op (opⱽ G) (deductive-op G D))
  ≡ is-deductive-system.composable D
deductive-op-composable-invol G D = is-composable-is-prop G _ _

deductive-op-stable-invol
  : ∀ {o h} (G : virtual-graph o h) (D : is-deductive-system G)
  → is-deductive-system.stable (deductive-op (opⱽ G) (deductive-op G D))
  ≡ is-deductive-system.stable D
deductive-op-stable-invol G D = is-equiv-is-prop _ _ _
```

The unital component round-trips *definitionally*. The swap is an
involution on the nose, so `ap` of it squares to the identity on
paths, and the two equivalence fields simply change places twice.

```agda
deductive-op-unital-invol
  : ∀ {o h} (G : virtual-graph o h) (D : is-deductive-system G)
  → is-deductive-system.unital (deductive-op (opⱽ G) (deductive-op G D))
  ≡ is-deductive-system.unital D
deductive-op-unital-invol G D = refl
```

No component depends on another, so the record's round trip is the
three component round trips.

```agda
deductive-op-invol
  : ∀ {o h} (G : virtual-graph o h) (D : is-deductive-system G)
  → deductive-op (opⱽ G) (deductive-op G D) ≡ D
deductive-op-invol G D i .is-deductive-system.composable =
  deductive-op-composable-invol G D i
deductive-op-invol G D i .is-deductive-system.unital =
  deductive-op-unital-invol G D i
deductive-op-invol G D i .is-deductive-system.stable =
  deductive-op-stable-invol G D i
```

## The path groupoid, untruncated

```agda
module path {u} (A : Type u) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob        = A
  PG .virtual-graph.hom x y   = x ≡ y
  PG .virtual-graph.idn x     = refl
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  open virtual-graph PG
  open sequents PG
  open vocab PG
```

The two emb-action equivalences are `pcom`'s idempotence laws, each
witnessing that the map is homotopic to the identity in both
directions.

```agda
  eqv⁻ : ∀ {x v : A} → is-equiv (λ (b : hom x v) → coact-π (idn x) (v , b))
  eqv⁻ = iso→equiv _ (λ b → b) (λ b → pcom.ideml b) (λ b → pcom.ideml b) .snd

  eqv⁺ : ∀ {w x : A} → is-equiv (λ (a : hom w x) → act-π (idn x) (w , a))
  eqv⁺ = iso→equiv _ (λ a → a) (λ a → pcom.idemr a) (λ a → pcom.idemr a) .snd
```

Representability is total, so composability is handed over.

```agda
  curry≃ : ∀ {x y} → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z) ≃ judgment x y
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  reflect-equiv : ∀ {x y} → is-equiv (reflect {x} {y})
  reflect-equiv = ((emb , yon-unbiased.emb-equiv {A = λ _ → A}) ∙e curry≃) .snd

  contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable (composite⁻ PG f g))
  contr⁻ f g = eqv-fibers reflect-equiv (composite⁻ PG f g)

  contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable (composite⁺ PG f g))
  contr⁺ f g = eqv-fibers reflect-equiv (composite⁺ PG f g)

  module Cmp = composable PG contr⁻ contr⁺
  open Cmp using (_⨾⁻_; _⨾⁺_)
```

Each hand's composition is idempotent at reflexivity: reflexivity
represents the composite judgment, by the corresponding action's
idempotence read under `reflect`, and the fiber's uniqueness names it.

```agda
  coact-idn : ∀ {y : A} (e : coterm y) → coact (idn y) e ≡ e
  coact-idn e i = e .fst , pcom.ideml (e .snd) i

  act-idn : ∀ {x : A} (t : term x) → act (idn x) t ≡ t
  act-idn t i = t .fst , pcom.idemr (t .snd) i

  rep-idem⁻ : ∀ x → reflect (idn x) ≡ composite⁻ PG (idn x) (idn x)
  rep-idem⁻ x i γ = reflect (idn x) (argue (γ .fst) (coact-idn (γ .snd) (~ i)))

  rep-idem⁺ : ∀ x → reflect (idn x) ≡ composite⁺ PG (idn x) (idn x)
  rep-idem⁺ x i γ = reflect (idn x) (argue (act-idn (γ .fst) (~ i)) (γ .snd))

  module Unt = Cmp.unital eqv⁻ eqv⁺ rep-idem⁻ rep-idem⁺
  open Unt using (canonical-flank⁻; canonical-flank⁺; is-stable; is-stable⁺)
```

Readback restricted to the identities is evaluation at `refl`, and a
family over every `(y , p : x ≡ y)` is determined by its value there —
singleton contraction, which needs no hypothesis on `A`. The two
readback types differ only in whether the endpoints are written, so
the packages are interconvertible by η.

```agda
  stable-package
    : (t₀ : ∀ (x : A) → emb (refl {x = x}) x refl x refl ≡ refl)
    → is-contr (Σ rd ∶ (∀ (x y : A) (p : x ≡ y) → emb p x refl y refl ≡ p)
               , (∀ x → rd x x refl ≡ t₀ x))
  stable-package t₀ = pin.pin-contr (λ {x} {y} p → emb p x refl y refl) t₀

  bridge
    : (t₀ : ∀ (x : A) → eval (reflect (idn x)) ≡ idn x)
    → (Σ u ∶ readback , (∀ x → u (idn x) ≡ t₀ x))
    ≃ (Σ rd ∶ (∀ (x y : A) (p : x ≡ y) → emb p x refl y refl ≡ p)
      , (∀ x → rd x x refl ≡ t₀ x))
  bridge t₀ = iso→equiv (λ (u , k) → (λ _ _ p → u p) , k)
                        (λ (rd , k) → (λ {x} {y} p → rd x y p) , k)
                        (λ _ → refl) (λ _ → refl)

  PG-stable : is-stable
  PG-stable = is-contr-equiv (bridge canonical-flank⁻) (stable-package canonical-flank⁻)

  PG-stable⁺ : is-stable⁺
  PG-stable⁺ = is-contr-equiv (bridge canonical-flank⁺) (stable-package canonical-flank⁺)

  PG-stable-pair : Unt.is-stable-pair
  PG-stable-pair = PG-stable , PG-stable⁺
```

Restriction itself is an equivalence, with the J-extension as inverse
— the singleton contraction of the slices, needing no hypothesis on
`A`. That is the tier in equivalence form, and every pinned package
follows from it as a fiber.

```agda
  T : ∀ {x y : A} → x ≡ y → x ≡ y
  T {x} {y} p = emb p x refl y refl

  t₀ : ∀ (x : A) → T (refl {x = x}) ≡ refl
  t₀ x = pcom.unit refl

  rb≃ : readback ≃ (∀ (x y : A) (p : x ≡ y) → T p ≡ p)
  rb≃ = iso→equiv (λ u _ _ p → u p) (λ rd p → rd _ _ p) (λ _ → refl) (λ _ → refl)

  at-refl-equiv : is-equiv (pin.at-refl T t₀)
  at-refl-equiv =
    iso→equiv (pin.at-refl T t₀) (pin.extend T t₀)
              (pin.extend-retract T t₀)
              (λ v → funext (pin.extend-refl T t₀ v)) .snd

  PG-is-stable : stable.is-stable PG
  PG-is-stable = (rb≃ ∙e (pin.at-refl T t₀ , at-refl-equiv)) .snd
```

All three tiers, for an arbitrary carrier.

```agda
  PG-composable : is-composable PG
  PG-composable = contr⁻ , contr⁺

  PG-unital : is-unital PG
  PG-unital = eqv⁻ , eqv⁺ , rep-idem⁻ , rep-idem⁺

  PG-deductive : is-deductive-system PG
  PG-deductive .is-deductive-system.composable = PG-composable
  PG-deductive .is-deductive-system.unital     = PG-unital
  PG-deductive .is-deductive-system.stable     = PG-is-stable
```
