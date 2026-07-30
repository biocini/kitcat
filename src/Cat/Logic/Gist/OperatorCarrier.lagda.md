Spike: a deductive system as a category with one operator.

`Cat.Logic.Gist.PolarityCollapse` rewrote every negative cut as one
positive cut after the operator `_⨾⁻ twist⁺`. This spike asks what
carrier that rewriting leaves. The answer is `presentation`: a wild
category, one endo-operator on its edges, a second endo-edge family,
and three laws relating them.

The structure of a deductive system is that data. `reflect` returns as
the flanked word, readback follows from the laws, and both cuts and
both invertibility centres are words the operator writes. The axioms
do not return. Each of the four tiers asks one fiber to be
contractible. The presentation forces each fiber's edge and says
nothing about the fiber's paths.

`residue` names what is left: stability, and one propositionality
demand per invertibility tier. Hom sets discharge all three, so the
correspondence is complete at the set level. The residue is not an
equation between operator words, and this spike does not derive it.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Gist.OperatorCarrier where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Data.Sigma
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-hlevel; Σ-prop-path)
open import Core.Transport.Base using (is-prop→PathP)

open import Cat.Logic.Type
open import Cat.Logic.Base

open import Cat.Logic.Gist.PolarityTwist using (module polarity)
open import Cat.Logic.Gist.PolarityCollapse using (module collapse)
```

## The carrier

The category is the positive cut, with `twist⁺` for its identity. The
operator is `cross`, and the second endo-edge family is `pivot`, which
plays `twist⁻`. Each law is a theorem of a deductive system, so the
record demands nothing new, and the backward direction below consumes
every one of them.

```agda
record presentation o h : Type₊ (o ⊔ h) where
  field
    ob  : Type o
    hom : ob → ob → Type h

    unit  : (x : ob) → hom x x
    _⨾_   : ∀ {x y z} → hom x y → hom y z → hom x z
    assoc : ∀ {w x y z} (f : hom w x) (g : hom x y) (k : hom y z)
          → (f ⨾ g) ⨾ k ≡ f ⨾ (g ⨾ k)
    unitl : ∀ {x y} (f : hom x y) → unit x ⨾ f ≡ f
    unitr : ∀ {x y} (f : hom x y) → f ⨾ unit y ≡ f

    cross : ∀ {x y} → hom x y → hom x y
    pivot : (x : ob) → hom x x
    cross-pivot : (x : ob) → cross (pivot x) ≡ unit x
    pivot-unitr : ∀ {x y} (f : hom x y) → cross f ⨾ pivot y ≡ f
    cross-cut : ∀ {x y z} (f : hom x y) (g : hom y z)
              → cross (cross f ⨾ g) ≡ cross f ⨾ cross g
```

The pivot's left law is the cross law and one unit law. The reflection
is the flanked word: the operator runs on the term half, the coterm
half stays where it is, and readback is the word at the axiom.

```agda
  pivot-unitl : ∀ {x y} (f : hom x y) → cross (pivot x) ⨾ f ≡ f
  pivot-unitl {x} f = ap (_⨾ f) (cross-pivot x) ∙ unitl f

  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v

  reflect : ∀ {x y} → hom x y
          → (γ : term x × coterm y) → hom (γ .fst .fst) (γ .snd .fst)
  reflect f γ = (cross (γ .fst .snd) ⨾ f) ⨾ (γ .snd .snd)

  readback : ∀ {x y} (f : hom x y)
           → reflect f ((x , pivot x) , (y , unit y)) ≡ f
  readback {y = y} f = ap (_⨾ unit y) (pivot-unitl f) ∙ unitr f
```

## The graph of a presentation

```agda
module carrier {o h} (P : presentation o h) where
  open presentation P using
    ( unit; _⨾_; assoc; unitl; unitr; cross; pivot
    ; cross-pivot; pivot-unitr; pivot-unitl; cross-cut )

  graph : virtual-graph o h
  graph .virtual-graph.ob       = presentation.ob P
  graph .virtual-graph.hom      = presentation.hom P
  graph .virtual-graph.reflect  = presentation.reflect P
  graph .virtual-graph.twist⁺   = presentation.unit P
  graph .virtual-graph.twist⁻   = presentation.pivot P
  graph .virtual-graph.readback = presentation.readback P

  open virtual-graph graph
  open sequents graph
```

Each cut's representative is a word the operator writes. The positive
cut is the category's composition. The negative cut is that
composition after the operator. Neither witness needs a hypothesis.

```agda
  cut⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → reflect (f ⨾ g) ≡ composite⁺ graph f g
  cut⁺ f g = funext λ γ →
      ap (_⨾ (γ .snd .snd)) (sym (assoc (cross (γ .fst .snd)) f g))
    ∙ assoc (cross (γ .fst .snd) ⨾ f) g (γ .snd .snd)
    ∙ ap ((cross (γ .fst .snd) ⨾ f) ⨾_)
         (sym (ap (_⨾ (γ .snd .snd)) (pivot-unitl g)))

  cut⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → reflect (cross f ⨾ g) ≡ composite⁻ graph f g
  cut⁻ f g = funext λ γ →
      ap (_⨾ (γ .snd .snd)) (sym (assoc (cross (γ .fst .snd)) (cross f) g))
    ∙ ap (λ e → (e ⨾ g) ⨾ (γ .snd .snd)) (sym (cross-cut (γ .fst .snd) f))
    ∙ ap (λ e → (cross e ⨾ g) ⨾ (γ .snd .snd))
         (sym (unitr (cross (γ .fst .snd) ⨾ f)))

  composable⁺ : is-composable⁺ graph
  composable⁺ f g = (f ⨾ g) , cut⁺ f g

  composable⁻ : is-composable⁻ graph
  composable⁻ f g = (cross f ⨾ g) , cut⁻ f g
```

Each invertibility fiber is inhabited by the other twist.

```agda
  cancel⁻ : (x : ob) → coact-π {x} {x} (unit x) ≡ snd
  cancel⁻ x = funext λ γ →
    ap (_⨾ (γ .snd)) (pivot-unitl (unit x)) ∙ unitl (γ .snd)

  cancel⁺ : (x : ob) → act-π {x} {x} (pivot x) ≡ snd
  cancel⁺ x = funext λ t →
    unitr (cross (t .snd) ⨾ pivot x) ∙ pivot-unitr (t .snd)
```

Readback makes the reflection injective, so each fiber's edge is
forced.

```agda
  reflect-injective : ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-injective {x} {y} {m} {n} p =
    sym (readback m) ∙ happly p (var x , covar y) ∙ readback n

  cut⁺-forced : ∀ {x y z} (f : hom x y) (g : hom y z)
                (w : is-representable (composite⁺ graph f g))
              → w .fst ≡ f ⨾ g
  cut⁺-forced f g w = reflect-injective (w .snd ∙ sym (cut⁺ f g))

  cut⁻-forced : ∀ {x y z} (f : hom x y) (g : hom y z)
                (w : is-representable (composite⁻ graph f g))
              → w .fst ≡ cross f ⨾ g
  cut⁻-forced f g w = reflect-injective (w .snd ∙ sym (cut⁻ f g))

  centre⁻-forced : (x : ob) (w : fiber (coact-π {x} {x}) snd)
                 → w .fst ≡ unit x
  centre⁻-forced x (e , p) =
      sym (pivot-unitl e)
    ∙ sym (unitr (cross (pivot x) ⨾ e))
    ∙ happly p (x , unit x)

  centre⁺-forced : (x : ob) (w : fiber (act-π {x} {x}) snd)
                 → w .fst ≡ pivot x
  centre⁺-forced x (e , p) =
      sym (pivot-unitl e)
    ∙ sym (unitr (cross (pivot x) ⨾ e))
    ∙ happly p (x , pivot x)
```

The pivot is a field, and the two pivot laws pin it. One law each is
enough: the right unit law of one family against the cross law of the
other.

```agda
  pivot-forced : (p q : (x : ob) → hom x x)
               → (∀ x → cross (q x) ≡ unit x)
               → (∀ {x y} (f : hom x y) → cross f ⨾ p y ≡ f)
               → ∀ x → p x ≡ q x
  pivot-forced p q cq up x =
    sym (ap (_⨾ p x) (cq x) ∙ unitl (p x)) ∙ up (q x)
```

## The residue

Each tier asks one fiber to be contractible, and the fiber's edge is
forced already. What remains at each tier is one propositionality
demand. Hom sets give all three, through the library's own
`stable-from-hom-sets` and one `Σ-prop-path` per invertibility tier.

```agda
  residue : Type (o ⊔ h)
  residue = is-stable graph
          × ((x : ob) → is-prop (fiber (coact-π {x} {x}) snd))
          × ((x : ob) → is-prop (fiber (act-π {x} {x}) snd))

  hom-sets→stable : (∀ {x y} → is-set (hom x y)) → is-stable graph
  hom-sets→stable hset = stable-from-hom-sets graph hset
    (λ {_} {_} {m} {n} q → sym (readback m) ∙ q ∙ readback n)

  fiber⁻-is-prop : (∀ {x y} → is-set (hom x y)) → (x : ob)
                 → is-prop (fiber (coact-π {x} {x}) snd)
  fiber⁻-is-prop hset x w w' =
    Σ-prop-path (λ e → Π-is-hlevel 2 (λ _ → hset) (coact-π e) snd)
      (centre⁻-forced x w ∙ sym (centre⁻-forced x w'))

  fiber⁺-is-prop : (∀ {x y} → is-set (hom x y)) → (x : ob)
                 → is-prop (fiber (act-π {x} {x}) snd)
  fiber⁺-is-prop hset x w w' =
    Σ-prop-path (λ e → Π-is-hlevel 2 (λ _ → hset) (act-π e) snd)
      (centre⁺-forced x w ∙ sym (centre⁺-forced x w'))

  hom-sets→residue : (∀ {x y} → is-set (hom x y)) → residue
  hom-sets→residue hset =
    hom-sets→stable hset , fiber⁻-is-prop hset , fiber⁺-is-prop hset

  axioms : residue → is-deductive-system graph
  axioms r .is-deductive-system.composable .is-composable.contr⁺ f g =
    prop-inhabited→is-contr (r .fst _) (composable⁺ f g)
  axioms r .is-deductive-system.composable .is-composable.contr⁻ f g =
    prop-inhabited→is-contr (r .fst _) (composable⁻ f g)
  axioms r .is-deductive-system.invertible .is-invertible.fiber⁻ x =
    prop-inhabited→is-contr (r .snd .fst x) (unit x , cancel⁻ x)
  axioms r .is-deductive-system.invertible .is-invertible.fiber⁺ x =
    prop-inhabited→is-contr (r .snd .snd x) (pivot x , cancel⁺ x)

system : ∀ {o h} (P : presentation o h) → carrier.residue P → deductive-system o h
system P r .deductive-system.graph  = carrier.graph P
system P r .deductive-system.axioms = carrier.axioms P r
```

## The presentation of a deductive system

```agda
module presented {o h} (D : deductive-system o h) where
  G : virtual-graph o h
  G = deductive-system.graph D

  A : is-deductive-system G
  A = deductive-system.axioms D

  S : is-stable G
  S = axioms→stable G A

  C⁺ : is-composable⁺ G
  C⁺ f g = is-composable.contr⁺ (is-deductive-system.composable A) f g .center

  C⁻ : is-composable⁻ G
  C⁻ f g = is-composable.contr⁻ (is-deductive-system.composable A) f g .center

  T⁻ : is-invertible⁻ G
  T⁻ = is-invertible.fiber⁻ (is-deductive-system.invertible A)

  T⁺ : is-invertible⁺ G
  T⁺ = is-invertible.fiber⁺ (is-deductive-system.invertible A)

  open virtual-graph G
  open tower G S C⁺ C⁻
  open balanced T⁻ T⁺
  open collapse G S C⁺ C⁻ T⁻ T⁺
  open polarity G S C⁺ C⁻ using (positive; negative; module full)
  open full T⁻ T⁺ using (positive-of-twist⁺)

  present : presentation o h
  present .presentation.ob = ob
  present .presentation.hom = hom
  present .presentation.unit = twist⁺
  present .presentation._⨾_ = _⨾⁺_
  present .presentation.assoc = assoc⁺
  present .presentation.unitl = unitl⁺
  present .presentation.unitr = unitr⁺
  present .presentation.cross = cross⁻
  present .presentation.pivot = twist⁻
  present .presentation.cross-pivot = pair⁻
  present .presentation.pivot-unitr f = cut⁻-cross f (twist⁻ _) ∙ unitr⁻ f
  present .presentation.cross-cut = cross⁻-cut⁺
```

The opposite exchanges the two operators.

```agda
  Aᵛ : is-deductive-system (opⱽ G)
  Aᵛ = op-axioms G A

  Sᵛ : is-stable (opⱽ G)
  Sᵛ = axioms→stable (opⱽ G) Aᵛ

  C⁺ᵛ : is-composable⁺ (opⱽ G)
  C⁺ᵛ f g = is-composable.contr⁺ (is-deductive-system.composable Aᵛ) f g .center

  C⁻ᵛ : is-composable⁻ (opⱽ G)
  C⁻ᵛ f g = is-composable.contr⁻ (is-deductive-system.composable Aᵛ) f g .center

  T⁻ᵛ : is-invertible⁻ (opⱽ G)
  T⁻ᵛ = is-invertible.fiber⁻ (is-deductive-system.invertible Aᵛ)

  T⁺ᵛ : is-invertible⁺ (opⱽ G)
  T⁺ᵛ = is-invertible.fiber⁺ (is-deductive-system.invertible Aᵛ)

  module op = collapse (opⱽ G) Sᵛ C⁺ᵛ C⁻ᵛ T⁻ᵛ T⁺ᵛ

  op-cross : ∀ {x y} (f : hom x y) → op.cross⁻ f ≡ cross⁺ f
  op-cross f = refl
```

Every reflection is a flanked word, so the presentation's reflection
agrees with the graph's one edge at a time.

```agda
  reflect-word : ∀ {x y} (m : hom x y) (γ : argument x y)
               → reflect m γ ≡ ((γ .fst .snd) ⨾⁻ m) ⨾⁺ (γ .snd .snd)
  reflect-word m ((w , s) , (v , k)) =
      (λ i → reflect m ((w , readback s (~ i)) , (v , k)))
    ∙ sym (happly (reflect-⨾⁻ s m) (var w , (v , k)))
    ∙ ⨾⁺-is-coact (s ⨾⁻ m) k

  back : virtual-graph o h
  back = carrier.graph present

  round-ob : virtual-graph.ob back ≡ ob
  round-ob = refl

  round-hom : virtual-graph.hom back ≡ hom
  round-hom = refl

  round-twist⁺ : virtual-graph.twist⁺ back ≡ twist⁺
  round-twist⁺ = refl

  round-twist⁻ : virtual-graph.twist⁻ back ≡ twist⁻
  round-twist⁻ = refl

  round-reflect : ∀ {x y} (m : hom x y) (γ : argument x y)
                → virtual-graph.reflect back m γ ≡ reflect m γ
  round-reflect m γ =
      ap (_⨾⁺ (γ .snd .snd)) (cut⁻-cross (γ .fst .snd) m)
    ∙ sym (reflect-word m γ)
```

The two readbacks share their endpoints and nothing identifies them.
The square is the whole of the remaining obligation, and it carries the
graph and the package with it.

```agda
  readback-square : Type (o ⊔ h)
  readback-square = ∀ {x y} (f : hom x y)
                  → PathP (λ i → round-reflect f (var x , covar y) i ≡ f)
                          (virtual-graph.readback back f) (readback f)

  round-graph : readback-square → back ≡ G
  round-graph sq i .virtual-graph.ob = ob
  round-graph sq i .virtual-graph.hom = hom
  round-graph sq i .virtual-graph.reflect m γ = round-reflect m γ i
  round-graph sq i .virtual-graph.twist⁺ = twist⁺
  round-graph sq i .virtual-graph.twist⁻ = twist⁻
  round-graph sq i .virtual-graph.readback f = sq f i

  round-system : (sq : readback-square) (r : carrier.residue present)
               → system present r ≡ D
  round-system sq r i .deductive-system.graph = round-graph sq i
  round-system sq r i .deductive-system.axioms =
    is-prop→PathP (λ j → is-deductive-system-is-prop (round-graph sq j))
      (carrier.axioms present r) A i
```

## The dictionary

```agda
  associates→cross : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
                   → associates f g h
                   → cross⁻ (f ⨾⁺ g) ⨾⁺ h ≡ (f ⨾⁺ cross⁻ g) ⨾⁺ h
  associates→cross f g h a =
      cut⁻-cross (f ⨾⁺ g) h
    ∙ a
    ∙ ap (f ⨾⁺_) (sym (cut⁻-cross g h))
    ∙ sym (assoc⁺ f (cross⁻ g) h)

  cross→associates : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
                   → cross⁻ (f ⨾⁺ g) ⨾⁺ h ≡ (f ⨾⁺ cross⁻ g) ⨾⁺ h
                   → associates f g h
  cross→associates f g h e =
      sym (cut⁻-cross (f ⨾⁺ g) h)
    ∙ e
    ∙ assoc⁺ f (cross⁻ g) h
    ∙ ap (f ⨾⁺_) (cut⁻-cross g h)

  thunkable→cross : ∀ {w x} (f : hom w x) → thunkable f
                  → ∀ {y} (g : hom x y) → cross⁻ (f ⨾⁺ g) ≡ f ⨾⁺ cross⁻ g
  thunkable→cross f T g =
      sym (unitr⁺ (cross⁻ (f ⨾⁺ g)))
    ∙ associates→cross f g (twist⁺ _) (T g (twist⁺ _))
    ∙ unitr⁺ (f ⨾⁺ cross⁻ g)

  cross→thunkable : ∀ {w x} (f : hom w x)
                  → (∀ {y} (g : hom x y) → cross⁻ (f ⨾⁺ g) ≡ f ⨾⁺ cross⁻ g)
                  → thunkable f
  cross→thunkable f e g h = cross→associates f g h (ap (_⨾⁺ h) (e g))

  linear→cross : ∀ {y z} (h : hom y z) → linear h
               → ∀ {w x} (f : hom w x) (g : hom x y)
               → cross⁻ (f ⨾⁺ g) ⨾⁺ h ≡ (f ⨾⁺ cross⁻ g) ⨾⁺ h
  linear→cross h L f g = associates→cross f g h (L f g)

  cross→linear : ∀ {y z} (h : hom y z)
               → (∀ {w x} (f : hom w x) (g : hom x y)
                  → cross⁻ (f ⨾⁺ g) ⨾⁺ h ≡ (f ⨾⁺ cross⁻ g) ⨾⁺ h)
               → linear h
  cross→linear h e f g = cross→associates f g h (e f g)
```

Polarity is representability of the operator on the edges into an
object.

```agda
  represents : ob → Type (o ⊔ h)
  represents x = ∀ {w} (f : hom w x) → cross⁻ f ≡ f ⨾⁺ cross⁻ (twist⁺ x)

  represents-forced : (x : ob) (e : hom x x)
                    → (∀ {w} (f : hom w x) → cross⁻ f ≡ f ⨾⁺ e)
                    → e ≡ cross⁻ (twist⁺ x)
  represents-forced x e R = sym (unitl⁺ e) ∙ sym (R (twist⁺ x))

  linear-twist→represents : (x : ob) → linear (twist⁺ x) → represents x
  linear-twist→represents x L f = from-linear.cross⁻-into L f

  represents→linear-twist : (x : ob) → represents x → linear (twist⁺ x)
  represents→linear-twist x R f g =
    cross→associates f g (twist⁺ x)
      (ap (_⨾⁺ twist⁺ x)
        ( R (f ⨾⁺ g)
        ∙ assoc⁺ f g (cross⁻ (twist⁺ x))
        ∙ ap (f ⨾⁺_) (sym (R g)) ))

  positive→represents : (x : ob) → positive x → represents x
  positive→represents x P = linear-twist→represents x (P x (twist⁺ x))

  represents→positive : (x : ob) → represents x → positive x
  represents→positive x R = positive-of-twist⁺ x (represents→linear-twist x R)

  negative→represents : (x : ob) → negative x → represents x
  negative→represents x N = positive→represents x (negative→positive x N)

  represents→negative : (x : ob) → represents x → negative x
  represents→negative x R = positive→negative x (represents→positive x R)
```

## The presentation round trip

```agda
module round {o h} (P : presentation o h) (r : carrier.residue P) where
  open presentation P using (ob; hom; unit; _⨾_; cross; pivot; unitr)

  P' : presentation o h
  P' = presented.present (system P r)

  round-ob : presentation.ob P' ≡ ob
  round-ob = refl

  round-hom : presentation.hom P' ≡ hom
  round-hom = refl

  round-unit : presentation.unit P' ≡ unit
  round-unit = refl

  round-pivot : presentation.pivot P' ≡ pivot
  round-pivot = refl

  round-cut : ∀ {x y z} (f : hom x y) (g : hom y z)
            → presentation._⨾_ P' f g ≡ (f ⨾ g)
  round-cut f g = refl

  round-cross : ∀ {x y} (f : hom x y) → presentation.cross P' f ≡ cross f
  round-cross f = unitr (cross f)
```

## What the spike settles

The carrier is `presentation`. Its category component is the positive
cut, its operator is the negative cut against `twist⁺`, and its pivot
is `twist⁻`. Each of the three operator laws is a theorem of a
deductive system: `cross-pivot` is `pair⁻`, `pivot-unitr` is
`cut⁻-cross` against `unitr⁻`, and `cross-cut` is `cross⁻-cut⁺`. The
backward direction consumes every field, so no law is idle. The one
free choice is the operator's direction, and `op-cross` shows the
opposite exchanges the two readings on the nose.

The forward direction is assembly, `present`.

The backward direction rebuilds the structure and stops at the tiers.
`carrier.graph` is a virtual graph with readback and no hypothesis.
`composable⁺`, `composable⁻`, `cancel⁻` and `cancel⁺` inhabit all four
fibers, again with no hypothesis. `reflect-injective` forces each
fiber's edge (`cut⁺-forced`, `cut⁻-forced`, `centre⁻-forced`,
`centre⁺-forced`). The gap is `residue`, three propositionality
demands, and `hom-sets→residue` discharges it over hom sets. No tier
asked for a new law. Each one asked for an h-level of a fiber, which
no equation between operator words states.

Both round trips are componentwise. Five components of the
presentation return on the nose, and the operator returns up to
`unitr`, since the rebuilt negative cut ends at the unit. Four
components of the graph return on the nose, and the reflection returns
up to `round-reflect`. The record-level identity of graphs is exactly
one square, `readback-square`, and `round-graph` with `round-system`
derive both records from it. The homs are wild, so nothing here
identifies the two readbacks, and nothing here refutes the square.

The dictionary reads each polarity notion as a commutation defect of
the operator. `associates f g h` says right multiplication by `h`
erases the defect between `cross (f ⨾⁺ g)` and `f ⨾⁺ cross g`.
`thunkable f` erases the defect outright, one trailing edge at a time.
`linear h` erases it by right multiplication, at every pair.
`positive x` and `negative x` are one condition, `represents x`: the
operator on the edges into `x` is right multiplication by a single
edge. That edge is forced to be `cross⁻ (twist⁺ x)`, the operator's
value at the identity (`represents-forced`).

The balanced laws enter at two places. `unitl⁺` is the presentation's
`unitl`, and the backward direction spends it on readback, on the
positive cut, on the negative invertibility centre, and on the forcing
lemmas. `unitr⁻` enters as `pivot-unitr`, and `cancel⁺` is its only
consumer. So a stratum below balance loses the positive invertibility
centre first.

verified: `just check Cat.Logic.Gist.OperatorCarrier`, 2026-07-29, zero
warnings, no holes, no postulates.
