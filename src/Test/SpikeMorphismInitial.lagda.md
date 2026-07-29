Spike: initiality of a virtual graph, stated as contractibility of
the mapping type, probed for content.

Three probes. The statement is itself a proposition, so demanding it
adds property and no structure. The empty graph satisfies it, so it
is satisfiable. The codiscrete graph on two points refutes it, and
that graph carries the full deductive-system axioms, so the axioms
of the theory do not force it.

The carrier and the morphism record, inlined: a spike in an
in-development layer carries its own copy of the data it probes, so
a change to the layer cannot silently retune it. The carrier is a
field-for-field copy of `virtual-graph` in `Cat.Logic.Type`, with
the derived actions the cut composites need.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeMorphismInitial where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Bool using (Bool; true; false; module Bool)
open import Core.Data.Empty
open import Core.Kan using (_∙_)
open import Core.Path.Base using (_≢_)
open import Core.Transport.Base using (contr-ind)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.HLevel.Base using (Π-is-prop)

record virtual-graph o h : Type₊ (o ⊔ h) where
  field
    ob : Type o
    hom : ob → ob → Type h

  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v

  argument : ob → ob → Type (o ⊔ h)
  argument x y = term x × coterm y

  conclusion : ∀ {x y} → argument x y → Type h
  conclusion γ = hom (γ .fst .fst) (γ .snd .fst)

  judgment : ob → ob → Type (o ⊔ h)
  judgment x y = (γ : argument x y) → conclusion γ

  field
    reflect : ∀ {x y} → hom x y → judgment x y
    twist⁺  : (x : ob) → hom x x
    twist⁻  : (x : ob) → hom x x

  var : (x : ob) → term x
  var x = x , twist⁻ x

  covar : (y : ob) → coterm y
  covar y = y , twist⁺ y

  field
    readback : ∀ {x y} (f : hom x y)
             → reflect f (var x , covar y) ≡ f

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (var x , γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (t , covar y)

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact f γ = γ .fst , coact-π f γ

  act : ∀ {x y} → hom x y → term x → term y
  act f t = t .fst , act-π f t
```

A map of virtual graphs is a graph map that preserves each twist as
a pointwise path and preserves `reflect` at every argument. The
argument transport is the vertex and edge maps applied to both
halves, so both sides of the `reflect` equation inhabit one edge
type on the nose.

```agda
record _⇒_ {o h o' h'} (G : virtual-graph o h) (G' : virtual-graph o' h')
  : Type (o ⊔ o' ⊔ h ⊔ h') where
  private
    module G = virtual-graph G
    module G' = virtual-graph G'
  field
    map  : G.ob → G'.ob
    hmap : ∀ {x y} → G.hom x y → G'.hom (map x) (map y)

  term-map : ∀ {x} → G.term x → G'.term (map x)
  term-map t = map (t .fst) , hmap (t .snd)

  coterm-map : ∀ {y} → G.coterm y → G'.coterm (map y)
  coterm-map k = map (k .fst) , hmap (k .snd)

  argument-map : ∀ {x y} → G.argument x y → G'.argument (map x) (map y)
  argument-map γ = term-map (γ .fst) , coterm-map (γ .snd)

  field
    pres-twist⁺  : ∀ x → hmap (G.twist⁺ x) ≡ G'.twist⁺ (map x)
    pres-twist⁻  : ∀ x → hmap (G.twist⁻ x) ≡ G'.twist⁻ (map x)
    pres-reflect : ∀ {x y} (f : G.hom x y) (γ : G.argument x y)
                 → hmap (G.reflect f γ) ≡ G'.reflect (hmap f) (argument-map γ)

open _⇒_
```

An object is initial when the type of maps out of it is contractible
at every target. Contractibility is a proposition, so initiality is
one too: a system is initial or it is not, and the demand carries no
coherence data of its own.

```agda
is-initial : ∀ {o h} → virtual-graph o h → Type₊ (o ⊔ h)
is-initial {o} {h} G = (G' : virtual-graph o h) → is-contr (G ⇒ G')

is-initial-is-prop : ∀ {o h} (G : virtual-graph o h) → is-prop (is-initial G)
is-initial-is-prop G = Π-is-prop λ _ → is-contr-is-prop _

module Initial {o h} {G : virtual-graph o h} (init : is-initial G) where
  ¡ : ∀ {G'} → G ⇒ G'
  ¡ = init _ .center

  ¡-ind : ∀ {u} {G' : virtual-graph o h} (P : G ⇒ G' → Type u) → P ¡ → ∀ m → P m
  ¡-ind = contr-ind (init _)

  ¡-unique : ∀ {G'} (m : G ⇒ G') → ¡ ≡ m
  ¡-unique = ¡-ind (¡ ≡_) refl
```

The empty graph is initial: every component of a map out of it is a
function from the empty type, and so is every component of a path
between two such maps.

```agda
empty : virtual-graph 0ℓ 0ℓ
empty .virtual-graph.ob = ⊥
empty .virtual-graph.hom _ _ = ⊥
empty .virtual-graph.reflect ()
empty .virtual-graph.twist⁺ ()
empty .virtual-graph.twist⁻ ()
empty .virtual-graph.readback ()

empty-is-initial : is-initial empty
empty-is-initial G' .center .map ()
empty-is-initial G' .center .hmap ()
empty-is-initial G' .center .pres-twist⁺ ()
empty-is-initial G' .center .pres-twist⁻ ()
empty-is-initial G' .center .pres-reflect ()
empty-is-initial G' .paths m i .map ()
empty-is-initial G' .paths m i .hmap ()
empty-is-initial G' .paths m i .pres-twist⁺ ()
empty-is-initial G' .paths m i .pres-twist⁻ ()
empty-is-initial G' .paths m i .pres-reflect ()
```

The codiscrete graph on two points: every hom type is the unit type,
so the twists and `reflect` are forced, and readback holds by eta.
The identity and the point swap both preserve everything, and they
differ at the vertex `true`. So the type of self-maps of this graph
is not contractible, and the graph is not initial.

```agda
codisc : virtual-graph 0ℓ 0ℓ
codisc .virtual-graph.ob = Bool
codisc .virtual-graph.hom _ _ = ⊤
codisc .virtual-graph.reflect _ _ = tt
codisc .virtual-graph.twist⁺ _ = tt
codisc .virtual-graph.twist⁻ _ = tt
codisc .virtual-graph.readback _ = refl

id-hom : codisc ⇒ codisc
id-hom .map b = b
id-hom .hmap f = f
id-hom .pres-twist⁺ _ = refl
id-hom .pres-twist⁻ _ = refl
id-hom .pres-reflect _ _ = refl

not-hom : codisc ⇒ codisc
not-hom .map = Bool.not
not-hom .hmap f = f
not-hom .pres-twist⁺ _ = refl
not-hom .pres-twist⁻ _ = refl
not-hom .pres-reflect _ _ = refl

discrim : Bool → Type
discrim true  = ⊤
discrim false = ⊥

true≢false : true ≢ false
true≢false p = subst discrim p tt

id-hom≢not-hom : id-hom ≢ not-hom
id-hom≢not-hom p = true≢false (ap (λ m → m .map true) p)

codisc-hom-not-contr : ¬ is-contr (codisc ⇒ codisc)
codisc-hom-not-contr c =
  id-hom≢not-hom (sym (c .paths id-hom) ∙ c .paths not-hom)

codisc-not-initial : ¬ is-initial codisc
codisc-not-initial init = codisc-hom-not-contr (init codisc)
```

The two cut composites and representability, over any inlined
virtual graph, in the shapes of `Cat.Logic.Base`.

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G

  is-representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  is-representable = fiber reflect

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect f (γ .fst , coact g (γ .snd))

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect g (act f (γ .fst) , γ .snd)
```

The countermodel is not short of axioms: every fiber in sight is a
singleton. The four lemmas below are, field for field, the
components of `is-composable` and `is-invertible` in
`Cat.Logic.Base`. So the codiscrete graph carries the full
deductive-system axioms, and the type of its self-maps is still not
contractible.

```agda
module codisc-axioms where
  open virtual-graph codisc

  contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable codisc {x} {z} (composite⁺ codisc {x} {y} {z} f g))
  contr⁺ _ _ .center = tt , refl
  contr⁺ _ _ .paths _ = refl

  contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable codisc {x} {z} (composite⁻ codisc {x} {y} {z} f g))
  contr⁻ _ _ .center = tt , refl
  contr⁻ _ _ .paths _ = refl

  fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
  fiber⁻ _ .center = tt , refl
  fiber⁻ _ .paths _ = refl

  fiber⁺ : ∀ x → is-contr (fiber (act-π {x} {x}) snd)
  fiber⁺ _ .center = tt , refl
  fiber⁺ _ .paths _ = refl
```

## What the spike settles

Initiality as contractibility of the mapping type truncates no hom.
The predicate is a proposition (`is-initial-is-prop`), so it adds
property and no structure, and it constrains one object through its
maps out. The mechanism is the one `is-composable` already uses one
level down: contractibility asked of a specific fiber, not an
h-level hypothesis imposed on the homs of the theory.

The mapping type between two systems is wild in general. The type
of self-maps of `codisc` has two distinct points, and `codisc`
carries the deductive-system axioms, so no axiom of the theory
forces system maps to form a proposition. Contractibility can hold
only as a fact about a particular source, which is what initiality
asserts.

Open: whether a mapping type can be non-trivially higher, with two
maps equal in more than one way. That needs a target hom with a
non-trivial loop, and no such target is built here. Open: whether
the free system attains contractibility against every wild target.
Nothing here decides the free case. The countermodel only shows
that the axioms alone never will.
