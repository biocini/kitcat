The deductive-system predicate on a virtual graph, packaged.

Three tiers, three records, one bundle. Each hand's datum is a field
of its tier rather than a tier of its own, so a downstream instance
supplies one `is-composable`, one `is-unital` and one `is-stable`,
and never handles the two hands separately unless it wants to. Every
element the theory runs on — the two compositions, the two units, the
readback family — is projected from a contractible fiber rather than
declared, which is what makes each tier a proposition and hence the
bundle one.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeDeductiveSystem where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Path.Base
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.J using (J)
open import Core.Transport.Properties using (is-contr-is-prop)

open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base
open import Cat.Logic.Type

module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G
```

## The actions

Each hand's action holds one slot of the argument at its axiom half.
The edge-level form leaves the anonymous endpoint a parameter; the
term and coterm forms are the same data bundled.

```agda
  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (argue (var x) γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (argue t (covar y))

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact {x} f e = elim (reflect f (argue (var x) e))

  act : ∀ {x y} → hom x y → term x → term y
  act {y = y} f t = intro (reflect f (argue t (covar y)))
```

The two composite judgments: one factor stays reflected as the head,
the other acts on its slot.

```agda
  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (argue (γ .fst) (coact g (γ .snd)))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect g (argue (act f (γ .fst)) (γ .snd))
```

## Composability

Both hands in one record. Each composition is a fiber center and its
head-rewriting witness the center's path.

```agda
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
```

## Unitality

Both hands in one record: per hand, the fiber of that hand's action
map over the identity action. Neither field mentions `idn`, and the
unit each one projects absorbs everything.

```agda
  record is-unital : Type (o ⊔ h) where
    field
      unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
      unit-fiber⁺ : ∀ x → is-contr (fiber (act-π {x} {x}) snd)

    unit⁻ unit⁺ : ∀ x → hom x x
    unit⁻ x = unit-fiber⁻ x .center .fst
    unit⁺ x = unit-fiber⁺ x .center .fst

    unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
    unit⁻-absorb x γ i = unit-fiber⁻ x .center .snd i γ

    unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
    unit⁺-absorb x t i = unit-fiber⁺ x .center .snd i t
```

Uniqueness, from the tier alone. A candidate unit is an edge together
with a proof that its action is the identity action — that is, an
element of the very fiber the tier contracts. So a candidate is
identified with the projected unit, and the identification carries
the witness along with the element; readback is not consumed.

```agda
    unit⁻-unique-σ : ∀ x (e : hom x x) (p : coact-π e ≡ snd)
                   → (e , p) ≡ unit-fiber⁻ x .center
    unit⁻-unique-σ x e p = sym (unit-fiber⁻ x .paths (e , p))

    unit⁺-unique-σ : ∀ x (e : hom x x) (p : act-π e ≡ snd)
                   → (e , p) ≡ unit-fiber⁺ x .center
    unit⁺-unique-σ x e p = sym (unit-fiber⁺ x .paths (e , p))

    unit⁻-unique : ∀ x (e : hom x x) → coact-π e ≡ snd → e ≡ unit⁻ x
    unit⁻-unique x e p = ap fst (unit⁻-unique-σ x e p)

    unit⁺-unique : ∀ x (e : hom x x) → act-π e ≡ snd → e ≡ unit⁺ x
    unit⁺-unique x e p = ap fst (unit⁺-unique-σ x e p)
```

The same with the hypothesis in pointwise form, which is how an
instance will usually have it.

```agda
    unit⁻-unique-pt : ∀ x (e : hom x x)
                    → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ unit⁻ x
    unit⁻-unique-pt x e abs = unit⁻-unique x e (funext abs)

    unit⁺-unique-pt : ∀ x (e : hom x x)
                    → (∀ t → act-π e t ≡ t .snd) → e ≡ unit⁺ x
    unit⁺-unique-pt x e abs = unit⁺-unique x e (funext abs)
```

## Stability

Readback bare is a torsor, so the tier is the contractible fiber over
the coherence that pins it at the flanks. The flank canonicals are
stated at the units the unit tier projects, so the tier is a
predicate over `is-unital`.

```agda
  readback : Type (o ⊔ h)
  readback = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f

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
```

The readback family and the coherence are projections, and with them
the chosen edge of the graph is identified with each hand's unit — so
the two hands' units agree, and the chosen edge inherits both
absorptions.

```agda
  module stability (U : is-unital) (S : is-stable U) where
    open is-unital U

    unit : readback
    unit = S .center .fst

    coh : absorb-coh U unit
    coh = S .center .snd

    flanks-agree : ∀ x → flank⁻-of U x (unit (unit⁻ x))
                       ≡ flank⁺-of U x (unit (unit⁺ x))
    flanks-agree x = sym (coh x .fst) ∙ coh x .snd

    unit⁻-is-idn : ∀ x → unit⁻ x ≡ idn x
    unit⁻-is-idn x = sym (unit (unit⁻ x)) ∙ unit⁻-absorb x (covar x)

    unit⁺-is-idn : ∀ x → unit⁺ x ≡ idn x
    unit⁺-is-idn x = sym (unit (unit⁺ x)) ∙ unit⁺-absorb x (var x)

    units-agree : ∀ x → unit⁻ x ≡ unit⁺ x
    units-agree x = unit⁻-is-idn x ∙ sym (unit⁺-is-idn x)

    idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
    idn-absorb⁻ x γ =
      ap (λ e → coact-π e γ) (sym (unit⁻-is-idn x)) ∙ unit⁻-absorb x γ

    idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
    idn-absorb⁺ x t =
      ap (λ e → act-π e t) (sym (unit⁺-is-idn x)) ∙ unit⁺-absorb x t
```

Uniqueness against the graph's own edge: a candidate unit is the
chosen edge. Readback alone gives it, by evaluating the candidate's
absorption at the axiom, so the statement holds of any candidate
whether or not the unit tier is in scope.

```agda
    unit⁻-canonical : ∀ x (e : hom x x)
                    → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ idn x
    unit⁻-canonical x e abs = sym (unit e) ∙ abs (covar x)

    unit⁺-canonical : ∀ x (e : hom x x)
                    → (∀ t → act-π e t ≡ t .snd) → e ≡ idn x
    unit⁺-canonical x e abs = sym (unit e) ∙ abs (var x)
```

There are then two routes from a candidate to the chosen edge — via
the projected unit, or directly through readback — and they agree.
Both are instances of one dependent function on the fiber: send a
candidate to the composite of its readback point with its absorption
read at the axiom. Being a function of the fiber element, it is
natural in paths between them, which path induction supplies.

```agda
    route⁻ : ∀ x (c : fiber (coact-π {x} {x}) snd) → c .fst ≡ idn x
    route⁻ x c = sym (unit (c .fst)) ∙ (λ i → c .snd i (covar x))

    route⁺ : ∀ x (c : fiber (act-π {x} {x}) snd) → c .fst ≡ idn x
    route⁺ x c = sym (unit (c .fst)) ∙ (λ i → c .snd i (var x))

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
```

Both named identifications are that function: the projected unit's is
it at the center, the candidate's is it at the candidate. So the
detour through the projected unit cancels, and the two routes are one
path.

```agda
    unique-agrees⁻
      : ∀ x (e : hom x x) (abs : ∀ γ → coact-π e γ ≡ γ .snd)
      → unit⁻-unique-pt x e abs ∙ unit⁻-is-idn x ≡ unit⁻-canonical x e abs
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
      → unit⁺-unique-pt x e abs ∙ unit⁺-is-idn x ≡ unit⁺-canonical x e abs
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

## The bundle

```agda
  record is-deductive-system : Type (o ⊔ h) where
    field
      composable : is-composable
      unital     : is-unital
      stable     : is-stable unital

    open is-composable composable public
    open is-unital unital public
    open stability unital stable public
```

## Propositionality

Each tier is a proposition because every field is a contractibility
statement, and a product of propositions is one. The bundle follows
field by field, its stability component over the path the unit
component supplies.

```agda
  is-composable-is-prop : is-prop is-composable
  is-composable-is-prop C C' i .is-composable.contr⁻ f g =
    is-contr-is-prop _
      (is-composable.contr⁻ C f g) (is-composable.contr⁻ C' f g) i
  is-composable-is-prop C C' i .is-composable.contr⁺ f g =
    is-contr-is-prop _
      (is-composable.contr⁺ C f g) (is-composable.contr⁺ C' f g) i

  is-unital-is-prop : is-prop is-unital
  is-unital-is-prop U U' i .is-unital.unit-fiber⁻ x =
    is-contr-is-prop _ (is-unital.unit-fiber⁻ U x) (is-unital.unit-fiber⁻ U' x) i
  is-unital-is-prop U U' i .is-unital.unit-fiber⁺ x =
    is-contr-is-prop _ (is-unital.unit-fiber⁺ U x) (is-unital.unit-fiber⁺ U' x) i

  is-stable-is-prop : ∀ U → is-prop (is-stable U)
  is-stable-is-prop U = is-contr-is-prop _

  is-deductive-system-is-prop : is-prop is-deductive-system
  is-deductive-system-is-prop D D' i .is-deductive-system.composable =
    is-composable-is-prop
      (is-deductive-system.composable D) (is-deductive-system.composable D') i
  is-deductive-system-is-prop D D' i .is-deductive-system.unital =
    is-unital-is-prop
      (is-deductive-system.unital D) (is-deductive-system.unital D') i
  is-deductive-system-is-prop D D' i .is-deductive-system.stable =
    is-prop→PathP
      (λ i → is-stable-is-prop
        (is-unital-is-prop
          (is-deductive-system.unital D) (is-deductive-system.unital D') i))
      (is-deductive-system.stable D) (is-deductive-system.stable D') i
```

## Appendix — the tiers in `Cat.Graph.Refl` terms

The predicate above is stated entirely in the sequent vocabulary, but
each of its parts is an instance of a notion the reflexive-graph
suite already has a name for. The underlying reflexive graph is the
virtual graph's own data, and terms and coterms are its cofans and
fans, with `var` and `covar` their centers.

```agda
  graph : reflexive-graph o h
  graph .reflexive-graph.vtx  = ob
  graph .reflexive-graph.edge = hom
  graph .reflexive-graph.rx   = idn

  module appendix (D : is-deductive-system) where
    open is-deductive-system D
```

The unit tier's absorptions are what make the coslice and slice
families *displayed* reflexive graphs: displayed reflexivity over
`rx` is exactly a flank absorption, transported to the chosen edge.

```agda
    coact-idn : ∀ {y} (e : coterm y) → coact (idn y) e ≡ e
    coact-idn {y} e i = e .fst , idn-absorb⁻ y e i

    act-idn : ∀ {x} (t : term x) → act (idn x) t ≡ t
    act-idn {x} t i = t .fst , idn-absorb⁺ x t i

    coslice-rx : ∀ {a y} (u : hom a y) → reflect u ≡ composite⁻ u (idn y)
    coslice-rx u = funext λ γ →
      ap (λ e → reflect u (argue (γ .fst) e)) (sym (coact-idn (γ .snd)))

    slice-rx : ∀ {x c} (u : hom x c) → reflect u ≡ composite⁺ (idn x) u
    slice-rx u = funext λ γ →
      ap (λ t → reflect u (argue t (γ .snd))) (sym (act-idn (γ .fst)))
```

The coslice at an object carries the edges out of it, with a
displayed edge over `p` recording that its target is a composite.

```agda
    coslice : ob → rx.disp graph h (o ⊔ h)
    coslice a .reflexive-graphᴰ.vtx z          = hom a z
    coslice a .reflexive-graphᴰ.edge y z p u w = reflect w ≡ composite⁻ u p
    coslice a .reflexive-graphᴰ.rx u           = coslice-rx u

    slice : ob → rx.disp graph h (o ⊔ h)
    slice c .reflexive-graphᴰ.vtx x          = hom x c
    slice c .reflexive-graphᴰ.edge x y p u w = reflect u ≡ composite⁺ p w
    slice c .reflexive-graphᴰ.rx u           = slice-rx u
```

Against those displays the composability fields *are* the two
fibration conditions, handed over unchanged.

```agda
    coslice-is-fibration : ∀ a → rx.is-cov-fibration graph (coslice a)
    coslice-is-fibration _ _ _ p u = contr⁻ u p

    slice-is-fibration : ∀ c → rx.is-ctrv-fibration graph (slice c)
    slice-is-fibration _ _ _ p w = contr⁺ p w

    module cov (a : ob) = rx.cov-fibration graph (coslice a) (coslice-is-fibration a)
    module ctrv (c : ob) = rx.ctrv-fibration graph (slice c) (slice-is-fibration c)

    push-is-comp : ∀ a y z (p : hom y z) (u : hom a y) → cov.push a y z p u ≡ u ⨾⁻ p
    push-is-comp _ _ _ _ _ = refl

    pull-is-comp : ∀ c x y (p : hom x y) (w : hom y c) → ctrv.pull c x y p w ≡ p ⨾⁺ w
    pull-is-comp _ _ _ _ _ = refl
```

### The argument shapes

The correspondences above are definitional; the rest of the appendix
is a reading of the proof patterns, not further code.

*Fibration conditions.* `is-composable` is the pair of fibration
conditions on the two displays, so its projected compositions are the
pushforward and the pullback and its head-rewriting witnesses are the
lift and colift. The tier is stated on the bare virtual graph because
the condition needs only vertices and edges; the displays themselves
need the unit tier, which is why `coslice` sits inside `appendix`.

*The unit fiber.* `is-unital`'s fields are fibers of the two action
maps over the identity action, which is the shape `Lens`'s
uniqueness proofs collapse to: `cov-lens-structure-is-prop` reduces a
lens structure to the cofan of the identity in `B.vtx x ⋔ B x`, and
here the same datum appears one level down, with the fiber taken of
the assignment sending an edge to its action. The two differ only in
that ours is a single path where the cotensor's cofan is a pointwise
family — funext between them.

*Uniqueness by contraction.* `unit⁻-unique` is `ap fst` of a fiber
contraction, which is exactly the move `rx.univalence.to-id` makes:
recover an identification of vertices as the `fst`-shadow of a
contraction of the fan. Ours contracts the unit fiber rather than a
fan, and `unit⁻-unique-σ` keeps the witness the shadow discards.

*Naturality by path induction.* `route⁻-natural` is the elementary
form of the pattern `Fibration`'s straightening runs on: a family
determined on a contractible base is determined everywhere, so
transport along a contraction is forced. Straightening states it as a
based identity system; at this level path induction suffices.

*Duality.* The exchange of hands is `rx.op` on the base together with
the total opposite on the displays — the coslice over `graph` is the
slice over `rx.op graph` — so `tot-op-lens` and `fibration-duality`
are the suite's versions of the mirror we obtain by instantiating at
the opposite virtual graph.

*Propositionality.* Every tier is propositional for the reason
`is-univalent-is-prop` and `is-displayed-univalent-is-prop` are: the
fields are contractibility or propositionality statements, and
products of propositions are propositions. Where the suite hypothesises
`rx.is-univalent G` it is asking every fan to be a proposition — a
condition a deductive system does not satisfy, which is why the
uniqueness theorems of `Lens` do not transfer even though its
vocabulary does.

### The actions as displayed reflexive graphs

The term family displayed over the graph, with a displayed edge over
`p` recording that the target is the transport of the source. Its
displayed reflexivity is the term-side absorption.

```agda
    term-disp : rx.disp graph (o ⊔ h) (o ⊔ h)
    term-disp .reflexive-graphᴰ.vtx x            = term x
    term-disp .reflexive-graphᴰ.edge x y p t t'  = act p t ≡ t'
    term-disp .reflexive-graphᴰ.rx t             = act-idn t

    coterm-disp : rx.disp graph (o ⊔ h) (o ⊔ h)
    coterm-disp .reflexive-graphᴰ.vtx x           = coterm x
    coterm-disp .reflexive-graphᴰ.edge x y p u w  = u ≡ coact p w
    coterm-disp .reflexive-graphᴰ.rx u            = sym (coact-idn u)
```

Each is a fibration, and the lift space is a singleton, so the
condition carries no content: all the content sits in the
reflexivity above.

```agda
    term-disp-fibration : rx.is-cov-fibration graph term-disp
    term-disp-fibration x y p t .center = act p t , refl
    term-disp-fibration x y p t .paths (t' , q) i = q i , λ j → q (i ∧ j)

    coterm-disp-fibration : rx.is-ctrv-fibration graph coterm-disp
    coterm-disp-fibration x y p w .center = coact p w , refl
    coterm-disp-fibration x y p w .paths (u , q) i = q (~ i) , λ j → q (~ i ∨ j)
```

The pushforward and the pullback are the two actions themselves.

```agda
    module term-cov   = rx.cov-fibration  graph term-disp   term-disp-fibration
    module coterm-ctrv = rx.ctrv-fibration graph coterm-disp coterm-disp-fibration

    act-is-push : ∀ x y (p : hom x y) (t : term x) → term-cov.push x y p t ≡ act p t
    act-is-push _ _ _ _ = refl

    coact-is-pull : ∀ x y (p : hom x y) (w : coterm y) → coterm-ctrv.pull x y p w ≡ coact p w
    coact-is-pull _ _ _ _ = refl
```
