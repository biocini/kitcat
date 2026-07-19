Lane Biocini
July 2026

A formulation of category presented through a representable embedding
`emb` into two-sided *composite* operators.

The records take the name `category`; speaking properly they are
wild categories, types of morphisms never truncated to a set, but
enjoying many nice properties compared to the ordinary definition.

In particular we show that higher coherences arise automatically without
forcing truncation assumptions, and prove that no hidden truncation
assumption obtains.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Type where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.J using (J)
```

First we start with the data of a reflexive graph.

```agda
record reflexive-graph u v : Type₊ (u ⊔ v) where
  field
    ob : Type u
    edge : ob → ob → Type v
    rx : (x : ob) → edge x x

module virtual {o h} (structure : reflexive-graph o h) where
  private module structure = reflexive-graph structure

  ob = structure.ob
  hom = structure.edge
  idn = structure.rx
```

`over x = Σ w , hom w x` is a *cofamily-arrow* (cofHom) into `x` (here
an object over `x`).

`ov-idn y = (y , idn y)` is the identity cofamily-arrow — the *center*
in the path instance `over x` is the singleton `Σ w , w ≡ x` and
`ov-idn` is its center of contraction; wild categories posit the
center without the contractibility. It is the universal element the
representable actions read at.

```agda
  over : ob → Type (o ⊔ h)
  over x = Σ w ∶ ob , hom w x

  ov-ctr : ∀ {x y} → hom x y → over y
  ov-ctr {x} f = x , f

  ov-idn : (a : ob) → over a
  ov-idn a = a , idn a
```

`under y = Σ v , hom y v` is a family-arrow (fHom) out of `y`, an
object under `y`. We likewise define a center.

```agda
  under : ob → Type (o ⊔ h)
  under y = Σ v ∶ ob , hom y v

  un-ctr : ∀ {x y} → hom x y → under x
  un-ctr {y} f = y , f

  un-idn : (y : ob) → under y
  un-idn y = y , idn y
```

A context `ctx x y = over x × under y` pairs the two. This bears some
unpacking: the overarrow pins an arrow to x, the underarrow pins an object
out of y, so we're considering two arrows that might factor through an `x -> y`
if the latter exists.

```
  ctx : ob → ob → Type (o ⊔ h)
  ctx x y = over x × under y

  emp : ∀ {w x y z} → hom w x → hom y z → ctx x y
  emp h k = ov-ctr h , un-ctr k
```

`res γ` is the *result family* over a context. One can think of it in terms
of virtual double categories in a way that ought to be clear in a moment.

Here we fix the type of morphisms that range over the anonymous
witnesses of the over and under parts of the context - allowing us to
more concretely pose the question about what arrows factor in between
the over and under arrows to compose the full arc.

This allows us to formalize the notion of what it means to be a composite: a
composite between two objects is inhabited when any context based at the objects
yields an arc between the anonymous endpoints of the context. This condition must
be total: any context must be suitable as to induce it.

```
  res : ∀ {x y} → ctx x y → Type h
  res γ = hom (γ .fst .fst) (γ .snd .fst)

  composite : ob → ob → Type (o ⊔ h)
  composite x y = (γ : ctx x y) → res γ

  ev : ∀ {x y} → composite x y → hom x y
  ev {x} {y} α = α (ov-idn x , un-idn y)
```

We now require a function which allows us to demonstrate a composite exists
for any hom, i.e. fixing a morphism that given pre and post composable morphisms
always yields an arc between the anonymous endpoints -- at least ostensibly (it ought
to be this one, otherwise, we would have to account for some other morphism qualifying
as a middle factor of the arc).

We then say that a composite is representable when at least one morphism exists
such that it embeds into the composite fixed at its objects. The connection to
VDCs will be direct when we demonstrate that is-representable is a proposition,
and how the type of morphisms fixed at a composite x y admits only one inhabitant
under the total space.

`emb` is the two-sided Yoneda/CPS embedding f ↦ λ(a,b). b∘f∘a.

```agda
module representable {o h}
  (S : reflexive-graph o h)
  (let private module S = reflexive-graph S
       private module T = virtual S)
  (emb : ∀ {x y} → S.edge x y → T.composite x y)
  where

  open virtual S

  is-representable : ∀ {x y} → composite x y → Type (o ⊔ h)
  is-representable = fiber emb

  _⊨_ : ∀ {x y} → composite x y → hom x y → Type (o ⊔ h)
  α ⊨ s = emb s ≡ α

  ⊨ctr : ∀ {x y} (s : hom x y) → emb s ⊨ s
  ⊨ctr s = refl

  pre : ∀ {y z} (g : hom y z) {v} → hom z v → hom y v
  pre {y} g {v} b = emb g (ov-idn y , un-ctr b)

  post : ∀ {x y} (f : hom x y) {w} → hom w x → hom w y
  post {y = y} f {w} a = emb f (ov-ctr a , un-idn y)

  sub : ∀ {x y z} → hom y z → ctx x z → ctx x y
  sub g (c , (v , b)) = c , (v , pre g b)

  cosub : ∀ {x y z} → hom x y → ctx x z → ctx y z
  cosub g ((w , b) , β) = (w , post g b) , β

  nrm : ∀ {x y} (f : hom x y) → is-representable (emb f)
  nrm f = f , refl

  _▾_ : ∀ {x y z} → composite x y → hom y z → composite x z
  (α ▾ g) γ = α (sub g γ)
  infixl 30 _▾_

  _▴_ : ∀ {x y z} → hom x y → composite y z → composite x z
  (f ▴ β) γ = β (cosub f γ)
  infixl 30 _▴_

  _▿_ : ∀ {x y z} → composite x y → composite y z → composite x z
  _▿_ {y = y} β α γ = β (γ .fst , (γ .snd .fst , α (ov-idn y , γ .snd)))
  infixl 30 _▿_

  _▵_ : ∀ {x y z} → composite x y → composite y z → composite x z
  _▵_ {y = y} β α γ = α ((γ .fst .fst , β (γ .fst , un-idn y)) , γ .snd)
  infixl 30 _▵_

  -- closure of the ternary interchange over the fibers of emb;
  -- at nrm endpoints it agrees with the input up to J-refl
  interchange♭-from
    : (∀ {x y z} (f : hom x y) (g : hom y z) → emb f ▾ g ≡ f ▴ emb g)
    → ∀ {x y z} {A : composite x y} {B : composite y z}
    → is-representable A → is-representable B → A ▿ B ≡ A ▵ B
  interchange♭-from ι {B = B} (m , p) (n , q) =
    J (λ F' _ → F' ▿ B ≡ F' ▵ B)
      (J (λ G' _ → emb m ▿ G' ≡ emb m ▵ G') (ι m n) q)
      p

record category-axioms {o h} (S : reflexive-graph o h) : Type (o ⊔ h) where
  open virtual S

  field
    emb : ∀ {x y} → hom x y → composite x y

  open representable S emb public

  field
    interchange♭
      : ∀ {x y z} {A : composite x y} {B : composite y z}
      → is-representable A
      → is-representable B
      → A ▿ B ≡ A ▵ B

  interchange : ∀ {x y z} (f : hom x y) (g : hom y z) → emb f ▾ g ≡ f ▴ emb g
  interchange f g = interchange♭ (nrm f) (nrm g)

  spine : ∀ {x y z} (f : hom x y) (g : hom y z) → Type (o ⊔ h)
  spine f g =
    Σ k ∶ hom _ _ ,
    Σ p ∶ (emb k ≡ emb f ▾ g) ,
    Σ q ∶ (emb k ≡ f ▴ emb g) ,
      PathP (λ i → emb k ≡ interchange f g i) p q

  field
    spine-contr : ∀ {x y z} (f : hom x y) (g : hom y z) → is-contr (spine f g)
    unit        : ∀ {x y} (f : hom x y) → ev (emb f) ≡ f

record category (o h : Level) : Type₊ (o ⊔ h) where
  field
    structure : reflexive-graph o h
    axioms    : category-axioms structure

  open virtual structure public
  open category-axioms axioms public

```
