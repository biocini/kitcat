A small gloss to give attribution for the ideas here and elsewhere in
this devleopment, and because I believe a summary for the origination
of these ideas will be instructive.

The following presentation of the identity type is originally based on
Petrakis's Univalent typoids, augmented with some ideas from Kraus
et. al's work on univalent higher categories formalizable in HoTT.

My original intention following the latter's work on coherent notions
of unit, isomorphism, and so forth was to build upon and extend their
framework to encompass a complete description of higher categorical
data, for various reasons having to do with my specific research
interest. Inspired by the synthetic higher category theory espoused by
Riehl, Verity, and others, I was eventually led to a very simple
formalism, almost didactic, a condition trivially satisfied by the
ordinary identity type, but just slightly stronger — the notion that
in order to define the data of a 1-category, one must specify
2-categorical data witnessing that the composites in the 1-category
have a unique composite up to the ambient notion of isomorphism. This
definition asks us to give a notion homotopies between paths by
providing a hom type for 2-cells whose total space of composites are
contractible, whose center is given by the reflexivity at the
composition of compatible `f`, `g`, namely:
  is-contr (Σ s ∶ x ⟶ y , f ⨾ g => s) (where `_=>_` is a type of 2-cells)

This specific idea formed when I was studying Sterling's notes on
virtual bicategories, which he was kind enough to send when I asked him
about his formalization of Duploids. I began to realize that the
framework I was developing from Kraus not only could fruitfully
interpret Sterling's constructions, but that my additional work was
approaching them from a different perspective and I could directly
adapt from his definitions. During this time I also became interested
in his Reflexive Graph Lenses paper, but I did not appreciate them
fully until I got to a certain point in the development of this budding
virtual graph theory. This module is in part an attempt to flesh out those
connections.

Important to the concept of virtual graph underpinning this library's
depiction of formal categories is the observation that unitality has
subtle implications on 2-cell structure.  As Kraus and Capirotti
shows, unital data in a category can be propositionally specified and
the correct definition of units for higher category is presented and
justified by their semi-simplicial model and semi-segal types. Upon
formalizing this notion in more general bicategorical type structure
(with 1-cells and 2-cell types ranging over their shapes), I observed
the contractibility of composite data (which is trivial when these 2-cells
are in fact the ambient identity type) alongside the existence of canonical
units allows us to conclude that coherent composition necessitates that 2-cells
collapse to a groupoid structure. This happens for an unavoidable reason:
as soon as unital 1-cells exist for each object in a higher category with
the requisite unit laws, `f ⨾ g => s` enjoys an equivalence of types with
the more general `h => s` because every `h` can be described as `h ∙ eqv` or
`eqv ∙ h`, and these are homotopical to `h` up to the higher morphism
structure given by the identity laws.

Given our contractibility condition for the unary identity system of
composites, this circumstance can in retrospect be trivially
anticipated by considering an equivalence of types:
  Γ, x, y, z ⊢ Π f ∶ x ⟶ y , Π g ∶ y ⟶ z, Σ s ∶ x ⟶ z , f ⨾ g => s
             ≃ Π h ∶ x ⟶ z , Σ s ∶ x ⟶ z , h => s

for such 2-cells. This is only inhabitable once we have units, as then
we can trivially construct the right hand of the equivalence from the left,
and the conjectured equivalence follows because we know:
  Γ, x, y, z ⊢ Π f ∶ x ⟶ y , Π g ∶ y ⟶ z, is-contr (Σ s ∶ x ⟶ z , f ⨾ g => s)
             ≃ Π h ∶ x ⟶ z , is-contr (Σ s ∶ x ⟶ z , h => s)

the latter of which is, of course, contractiblity of singletons (so that we
can add that it is equivalent to the native identity type, and is in particular
an encoding of the infinity groupoid structure of the hom-type). Upon studying Sterling's reflexive graph lenses in more detail, I found that his
framework was quite clarifying perspective on the constructions I was engaging in,
and was well disposed to characterize this arrangement of circumstances, so I will
explore that structure in this module

To sum up: after units exist in 1-cell data, in one fell swoop we witness the collapse of
2-cell structure such that the data specifying the coherence of categorical
composition fully saturates the space of 2-cells, and directed morphisms
become no longer possible to express. The core decision underpinning the
perspective of virtual graph theory takes this characterization seriously,
and entails a radical departure where we take the notion of isomorphism in
general as primitive, formalizing all the constructions of our formal system
in reference to the preservation of an ambient notion of isomorphism derived
directly from our categorical data. Because we
specify our definition of unit as a particular kind of isomorphism,
this treatment is sufficient to ensure the classic description of Functors,
Natural transformations, and so on, as we can systematically derive that the
appropriate definitions preserve unitality if and only if they preserve isomorphisms.
I will leave it to those modules to demonstrate such.

For now, we will demonstrate elementary proofs of the synthetic category theory
utilizing the infrastructure of virtual graphs whose development is elsewhere.

```
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Core.Groupoid where

open import Core.Base
open import Core.Data
open import Core.HLevel
open import Core.Kan
open import Core.Equiv
open import Core.Type

open import Lib.Graph.Base
open import Lib.Graph.Reflexive.Base

singl-unique : ∀ {u} {A : Type u} {x : A} → is-prop (Σ y ∶ A , x ≡ y)
singl-unique {A} {x} = is-contr→is-prop contr where
  contr : is-contr (Σ y ∶ A , x ≡ y)
  contr .center = x , refl
  contr .paths (y , q) = λ i → (q i) , λ j → q (i ∧ j)

record is-category {u} v (Ob : Type u) : Type (u ⊔ v ₊) where
  infix 6 _~>_
  field
    _~>_ : Ob → Ob → Type v
    eqv : ∀ {x} → x ~> x
    concat : ∀ {x y z} → x ~> y → y ~> z → x ~> z

  private
    _⨾_ = concat; infixr 9 _⨾_

  is-left-divisible : ∀ {x y} → x ~> y → Type (u ⊔ v)
  is-left-divisible {x} {y} f = ∀ {w} → is-equiv λ (k : w ~> x) → k ⨾ f

  is-right-divisible : ∀ {x y} → x ~> y → Type (u ⊔ v)
  is-right-divisible {x} {y} f = ∀ {z} → is-equiv λ (h : y ~> z) → f ⨾ h

  is-iso : ∀ {x y} → x ~> y → Type (u ⊔ v)
  is-iso f = is-left-divisible f × is-right-divisible f

  field
    eqv-iso : ∀ {x} → is-iso (eqv {x = x})
    eqv-linear : ∀ {x y} (f : x ~> y) → eqv ⨾ (eqv ⨾ f) ≡ eqv ⨾ f
    eqv-thunkable : ∀ {x y : Ob} (f : x ~> y) → (f ⨾ eqv) ⨾ eqv ≡ f ⨾ eqv
    assoc : ∀ {w x y z : Ob} (f : w ~> x) (g : x ~> y) (h : y ~> z)
          → (f ⨾ g) ⨾ h ≡ f ⨾ g ⨾ h

  hconcat : ∀ {x y z} {e1 d1 : x ~> y} {e2 d2 : y ~> z}
          → e1 ≡ d1 → e2 ≡ d2 → concat e1 e2 ≡ concat d1 d2
  hconcat α β i = concat (α i) (β i)

    -- Contractible fibers from is-equiv
  divr-contr : ∀ {x y} (s : x ~> y) → is-contr (Σ h ∶ x ~> y , eqv ⨾ h ≡ s)
  divr-contr s = eqv-iso .snd .eqv-fibers s

  divl-contr : ∀ {x y} (s : x ~> y) → is-contr (Σ k ∶ x ~> y , k ⨾ eqv ≡ s)
  divl-contr s = eqv-iso .fst .eqv-fibers s

  unitl : ∀ {x y : Ob} (f : x ~> y) → eqv ⨾ f ≡ f
  unitl {x = x} f = transport (λ i → path (~ i) ≡ f) (sym path ∙ path)
    module unitl where
      lin : eqv ⨾ (eqv ⨾ f) ≡ eqv ⨾ f
      lin = eqv-linear f

      total = is-contr→is-prop (divr-contr (eqv ⨾ f)) (eqv ⨾ f , lin) (f , refl)

      path : eqv ⨾ f ≡ f
      path = ap fst total

      htpy : PathP (λ i → eqv ⨾ path i ≡ eqv ⨾ f) lin refl
      htpy = ap snd total

  unitr : ∀ {x y : Ob} (f : x ~> y) → f ⨾ eqv ≡ f
  unitr {y = y} f = transport (λ i → path (~ i) ≡ f) (sym path ∙ path)
    module unitr where
      thk : (f ⨾ eqv) ⨾ eqv ≡ f ⨾ eqv
      thk = eqv-thunkable f

      total = is-contr→is-prop (divl-contr (f ⨾ eqv)) (f ⨾ eqv , thk) (f , refl)

      path : f ⨾ eqv ≡ f
      path = ap fst total

      htpy : PathP (λ i → path i ⨾ eqv ≡ f ⨾ eqv) thk refl
      htpy = ap snd total

  idem : ∀ {x} → eqv ⨾ eqv ≡ eqv {x = x}
  idem = unitl eqv

record 𝓘𝒹 {u} (Ob : Type u) : Typeω where
  infix 6 _＝_ _≈_
  field
    _＝_ : Ob → Ob → Type u
    _≈_ : ∀ {x y} → x ＝ y → x ＝ y → Type u
    eqv : ∀ {x} → x ＝ x
    inv : ∀ {x y} → x ＝ y → y ＝ x
    hinv : ∀ {x y} {f g : x ＝ y} → f ≈ g → g ≈ f
    concat : ∀ {x y z} → x ＝ y → y ＝ z → x ＝ z
    hconcat : ∀ {x y z} {e1 d1 : x ＝ y} {e2 d2 : y ＝ z}
            → e1 ≈ d1 → e2 ≈ d2 → concat e1 e2 ≈ concat d1 d2
    heqv : ∀ {x y} {f : x ＝ y} → f ≈ f
    vconcat : ∀ {x y : Ob} {f g h k : x ＝ y} → f ≈ g → g ≈ h → h ≈ k → f ≈ k

  private
    _⨾_ = concat; infixr 9 _⨾_
    _⨾⨾_⨾⨾_ = vconcat; infix 6 _⨾⨾_⨾⨾_
    _●_ = hconcat; infixr 8 _●_
    _⊚_ : ∀ {x y} {f g h : x ＝ y} → f ≈ g → g ≈ h → f ≈ h
    _⊚_ = vconcat heqv; infixr 9 _⊚_

  field
    eqv-linear : ∀ {x y : Ob} (f : x ＝ y) → eqv ⨾ (eqv ⨾ f) ≈ eqv ⨾ f
    eqv-thunkable : ∀ {x y : Ob} (f : x ＝ y) → (f ⨾ eqv) ⨾ eqv ≈ f ⨾ eqv
    assoc : ∀ {w x y z : Ob} (f : w ＝ x) (g : x ＝ y) (h : y ＝ z)
          → (f ⨾ g) ⨾ h ≈ f ⨾ g ⨾ h

    invl : ∀ {x y : Ob} (f : x ＝ y) → inv f ⨾ f ≈ eqv
    invr : ∀ {x y : Ob} (f : x ＝ y) → f ⨾ inv f ≈ eqv

    comp-unique : ∀ {x y z : Ob} {f : x ＝ y} {g : y ＝ z}
                → is-prop (Σ s ∶ x ＝ z , f ⨾ g ≈ s)
    divl-unique : ∀ {w x y : Ob} {f : x ＝ y} {s : w ＝ y}
                → is-prop (Σ h ∶ w ＝ x , h ⨾ f ≈ s)
    divr-unique : ∀ {x y z : Ob} {f : x ＝ y} {s : x ＝ z}
                → is-prop (Σ k ∶ y ＝ z , f ⨾ k ≈ s)

  comp-contr : ∀ {x y z : Ob} {f : x ＝ y} {g : y ＝ z}
             → is-contr (Σ s ∶ x ＝ z , f ⨾ g ≈ s)
  comp-contr {f} {g} .center = f ⨾ g , heqv
  comp-contr {f} {g} .paths = comp-unique (f ⨾ g , heqv)

  idtocomp : ∀ {x y z} {f : x ＝ y} {g : y ＝ z} {s : x ＝ z} → f ⨾ g ≡ s → f ⨾ g ≈ s
  idtocomp {f} {g} p = transport (λ i → f ⨾ g ≈ p i) heqv

  unitl : ∀ {x y : Ob} (f : x ＝ y) → eqv ⨾ f ≈ f
  unitl {x = x} f = transport (λ i → path (~ i) ≈ f) (hinv (idtocomp path) ⊚ idtocomp path)
    module unitl where
      is-lin : ∀ {y} (g : x ＝ y) → eqv ⨾ (eqv ⨾ g) ≈ eqv ⨾ g
      is-lin = eqv-linear

      total = divr-unique (eqv ⨾ f , is-lin f) (f , heqv)

      path : eqv ⨾ f ≡ f
      path = ap fst total

      htpy : PathP (λ i → eqv ⨾ path i ≈ eqv ⨾ f) (is-lin f) heqv
      htpy = ap snd total

  unitr : ∀ {x y : Ob} (f : x ＝ y) → f ⨾ eqv ≈ f
  unitr {y = y} f = transport (λ i → path (~ i) ≈ f) (hinv (idtocomp path) ⊚ idtocomp path)
    module unitr where
      is-thk : ∀ {w} (g : w ＝ y) → (g ⨾ eqv) ⨾ eqv ≈ g ⨾ eqv
      is-thk = eqv-thunkable

      total :  (f ⨾ eqv , is-thk f) ≡ (f , heqv)
      total = divl-unique (f ⨾ eqv , is-thk f) (f , heqv)

      path : f ⨾ eqv ≡ f
      path = ap fst total

      htpy : PathP (λ i → path i ⨾ eqv ≈ f ⨾ eqv) (is-thk f) heqv
      htpy = ap snd total

  idem : ∀ {x} → eqv ⨾ eqv ≈ eqv {x = x}
  idem {x = x} = transport (λ i → eqv ⨾ eqv ≈ path i) (heqv {x = x})
    module idem where
      is-lin : ∀ {y} (f : x ＝ y) → eqv ⨾ (eqv ⨾ f) ≈ eqv ⨾ f
      is-lin = eqv-linear

      total = divr-unique (eqv ⨾ eqv , is-lin eqv) (eqv , heqv)

      path : eqv ⨾ eqv ≡ eqv
      path = ap fst total

      htpy : PathP (λ i → eqv ⨾ path i ≈ eqv ⨾ eqv) (is-lin eqv) heqv
      htpy = ap snd total

  contr-hfibers : ∀ {x y} (f : x ＝ y) → is-contr (Σ g ∶ x ＝ y , f ≈ g)
  contr-hfibers f .center = f , heqv
  contr-hfibers f .paths = ! (f , heqv) where
    ! : is-prop (Σ (f ≈_))
    ! = transport (λ i → is-prop (Σ (unitl.path f i ≈_))) comp-unique

  to-2path : {x y : Ob} {f g : x ＝ y} → f ≈ g → f ≡ g
  to-2path {f} {g} H = ap fst (contr-hfibers f .paths (g , H))

  from-2path : {x y : Ob} {f g : x ＝ y} → f ≡ g → f ≈ g
  from-2path {f} α = transport (λ i → f ≈ α i) heqv

  2path-refl : ∀ {x y} {f : x ＝ y} → from-2path refl ≡ heqv {f = f}
  2path-refl = transport-refl heqv

  to-2path-heqv : ∀ {x y} {f : x ＝ y} → to-2path (heqv {f = f}) ≡ refl
  to-2path-heqv {f = f} = ap (ap fst) center-loop-is-refl
    where
      center-loop-is-refl : contr-hfibers f .paths (f , heqv) ≡ refl
      center-loop-is-refl = is-contr→loop-is-refl (contr-hfibers f)

  divl-contr : ∀ {w x y} (f : x ＝ y) (s : w ＝ y)
              → is-contr (Σ h ∶ w ＝ x , h ⨾ f ≈ s)
  divl-contr f s .center = s ⨾ inv f , assoc s (inv f) f ⨾⨾ (heqv ● invl f) ⨾⨾ unitr s
  divl-contr f s .paths = divl-unique (s ⨾ inv f , assoc s (inv f) f ⨾⨾ (heqv ● invl f) ⨾⨾ unitr s)

  divr-contr : ∀ {x y z} (f : x ＝ y) (s : x ＝ z)
             → is-contr (Σ k ∶ y ＝ z , f ⨾ k ≈ s)
  divr-contr f s .center = inv f ⨾ s , hinv (assoc f (inv f) s) ⨾⨾ (invr f ● heqv) ⨾⨾ unitl s
  divr-contr f s .paths = divr-unique (inv f ⨾ s , hinv (assoc f (inv f) s) ⨾⨾ (invr f ● heqv) ⨾⨾ unitl s)

  inv-eqv : ∀ {x} → inv eqv ≡ eqv {x = x}
  inv-eqv = ap fst (divl-unique (inv eqv , invl eqv) (eqv , idem))

  inv-inv : ∀ {x y} (f : x ＝ y) → inv (inv f) ≡ f
  inv-inv f = ap fst (divl-unique (inv (inv f) , invl (inv f)) (f , invr f))

  inv-concat : ∀ {x y z} (f : x ＝ y) (g : y ＝ z) → inv (f ⨾ g) ≡ inv g ⨾ inv f
  inv-concat f g = ap fst (divl-unique (inv (f ⨾ g) , invl (f ⨾ g)) (inv g ⨾ inv f , α))
    where
      α : (inv g ⨾ inv f) ⨾ (f ⨾ g) ≈ eqv
      α = assoc (inv g) (inv f) (f ⨾ g)
        ⨾⨾ heqv ● hinv (assoc (inv f) f g)
        ⨾⨾ heqv ● invl f ● heqv
        ⨾⨾ heqv ● unitl g
        ⨾⨾ invl g

  -- idem : ∀ {x} → eqv ⨾ eqv ≈ eqv {x = x}
  -- idem {x = x} = transport (λ i → eqv ⨾ eqv ≈ path i) (heqv {x = x})
  --   module idem where
  --     is-lin : ∀ {y} (f : x ＝ y) → eqv ⨾ (eqv ⨾ f) ≈ eqv ⨾ f
  --     is-lin = eqv-linear

  --     total = divr-unique (eqv ⨾ eqv , is-lin eqv) (eqv , heqv)

  --     path : eqv ⨾ eqv ≡ eqv
  --     path = ap fst total

  --     htpy : PathP (λ i → eqv ⨾ path i ≈ eqv ⨾ eqv) (is-lin eqv) heqv
  --     htpy = ap snd total



  heqv-unitl : ∀ {x y} {f g : x ＝ y} (α : f ≈ g) → heqv ⊚ α ≡ α
  heqv-unitl {f} {g} α = ap fst (singl-unique (heqv ⊚ α , {!!}) (α , refl)) where
    is-lin : heqv ⊚ heqv ⊚ α ≡ heqv ⊚ α
    is-lin = {!!}

    total = {!!}

    -- path : eqv ⨾ f ≡ f
    -- path = ap fst total

    -- htpy : PathP (λ i → eqv ⨾ path i ≈ eqv ⨾ f) (is-lin f) heqv
    -- htpy = ap snd total



  -- heqv-unitr : ∀ {x y} {f g : x ＝ y} (α : f ≈ g) → α ⊚ heqv ≡ α
  -- heqv-unitr α = {!!}
  --  module heqv-unitr where
  --     is-thk : ∀ {w} (g : w ＝ y) → (g ⨾ eqv) ⨾ eqv ≈ g ⨾ eqv
  --     is-thk = eqv-thunkable

  --     total :  (f ⨾ eqv , is-thk f) ≡ (f , heqv)
  --     total = divl-unique (f ⨾ eqv , is-thk f) (f , heqv)

  --     path : f ⨾ eqv ≡ f
  --     path = ap fst total

  --     htpy : PathP (λ i → path i ⨾ eqv ≈ f ⨾ eqv) (is-thk f) heqv
  --     htpy = ap snd total


  𝓘𝒹-hom : ∀ {x y : Ob} → 𝓘𝒹 (x ＝ y)
  𝓘𝒹-hom ._＝_ = _≈_
  𝓘𝒹-hom ._≈_ = _≡_
  𝓘𝒹-hom .eqv = heqv
  𝓘𝒹-hom .inv = hinv
  𝓘𝒹-hom .hinv = sym
  𝓘𝒹-hom .concat = _⊚_
  𝓘𝒹-hom .hconcat α β i = vconcat heqv (α i) (β i)
  𝓘𝒹-hom .heqv = refl
  𝓘𝒹-hom .vconcat p q r i = hcomp (∂ i) λ where
    k (i = i0) → p (~ k)
    k (k = i0) → q i
    k (i = i1) → r k
  𝓘𝒹-hom .eqv-linear f i = vconcat heqv heqv {!!}
  𝓘𝒹-hom .eqv-thunkable = {!!}
  𝓘𝒹-hom .assoc = {!!}
  𝓘𝒹-hom .invl = {!!}
  𝓘𝒹-hom .invr = {!!}
  𝓘𝒹-hom .comp-unique = {!!}
  𝓘𝒹-hom .divl-unique = {!!}
  𝓘𝒹-hom .divr-unique = {!!}

```
  H : ∀ {v} {Ob : Type u} {x y : Ob} (P : x ＝ y → Type v)
         → {f g : x ＝ y} → f ≈ g → P f → P g
  H P {g} h = transport (λ i → P (to-2path h (~ i)) → P g) id

  unital : ∀ {Ob} (x : Ob) → defn.has-identity (Gph Ob _＝_ , λ x → eqv {x = x}) _≈_ concat x
  unital = {!!}

  total-unit-contr  : ∀ {Ob : Type u} {x y : Ob} (s : x ＝ y) → is-contr (Σ f ∶ x ＝ y , eqv ⨾ f ≈ s)
  total-unit-contr {x = x} = defn.has-identity.unit (unital x)

  total-counit-contr  : ∀ {Ob : Type u} {w x : Ob} (s : w ＝ x) → is-contr (Σ f ∶ w ＝ x , f ⨾ eqv ≈ s)
  total-counit-contr {x = x} = defn.has-identity.counit (unital x)




    Disp : ∀ {v} (B : Ob → Type v) {x y} → x ≈ y → B x → B y → Type v
    deqv : ∀ {v} {B : Ob → Type v} {x} (a : B x) → Disp B (rx x) a a
    tr : ∀ {v} {C D : Type v} {x} → Disp (λ _ → Type v) (rx x) C D → C → D

  private module D {v} (B : Ob → Type v) = Displayed B Disp deqv
  field
    inv : ∀ {x y} → x ≈ y → y ≈ x
    concat : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
    cov-fib : ∀ {v} (B : Ob → Type v) → D.is-cov-fib B
    ctrv-fib : ∀ {v} (B : Ob → Type v) → D.is-ctrv-fib B

  subst : ∀ {v} (B : Ob → Type v) → ∀ {x y} → x ≈ y → B x → B y
  subst B = D.is-cov-fib.push B (cov-fib B)

  subst-lift : ∀ {v} (B : Ob → Type v) → ∀ {x y} (p : x ≈ y) (u : B x) → Disp B p u (subst B p u)
  subst-lift B = D.is-cov-fib.lift B (cov-fib B)

  lift-unique : ∀ {v} (B : Ob → Type v) → ∀ {x y} (p : x ≈ y) (u : B x) (v : B y) (e : Disp B p u v)
              → subst B p u , subst-lift B p u ≡ v , e
  lift-unique B = D.is-cov-fib.lift-unique B (cov-fib B)

  concat-contr : ∀ {x y z} (p : x ≈ y) (q : y ≈ z)
               → is-contr (Σ s ∶ x ≈ z , Disp (_≈ z) (rx x) (concat p q) s)
  concat-contr {x} {z} p q = cov-fib (_≈ z) (rx x) (concat p q)

  concat-unique : ∀ {x y z} (p : x ≈ y) (q : y ≈ z)
                → is-prop (Σ s ∶ x ≈ z , Disp (_≈ z) (rx x) (concat p q) s)
  concat-unique p q = is-contr→is-prop (concat-contr p q)

  subst-contr' : ∀ {x y z} (p : x ≈ y) (q : y ≈ z)
               → is-contr (Σ s ∶ x ≈ z , Disp (_≈ z) (rx x) s (subst (x ≈_) q p))
  subst-contr' {x} {z} p q = ctrv-fib (_≈ z) (rx x) (subst (x ≈_) q p)

  subst-prop' : ∀ {x y z} (p : x ≈ y) (q : y ≈ z)
             → is-prop (Σ s ∶ x ≈ z , Disp (_≈ z) (rx x) s (subst (x ≈_) q p))
  subst-prop' p q = is-contr→is-prop (subst-contr' p q)

  concat-fiber : ∀ {x y z} (p : x ≈ y) (q : y ≈ z) (r : x ≈ z)
               → (α : Disp (x ≈_) q p r)
               → subst (x ≈_) q p , subst-lift (x ≈_) q p ≡ r , α
  concat-fiber {x} {z} p q = lift-unique (x ≈_) q p

  concat-test : ∀ {x y z} (p : x ≈ y) (q : y ≈ z)
                → is-contr (Σ s ∶ x ≈ z , Disp (_≈ z) (rx x) (concat p q) s)
  concat-test p q = {!!} -- is-contr→is-prop (concat-contr p q)

  subst-concat : ∀ {x y z} (p : x ≈ y) (q : y ≈ z)
               → {!!} ≡ {!!}
  subst-concat {x} {z} p q  = concat-unique _ _ (concat p q , deqv (concat p q)) ({!!} , {!!}) where
    r0 : Disp (_≈ z) (rx x) (subst-contr' p q .center .fst) (subst (x ≈_) q p)
    r0 = ctrv-fib (_≈ z) (rx x) (subst (x ≈_) q p) .center .snd

    f0 : {!!}
    f0 = subst-prop' p q ((concat p q) , {!!}) ({!!} , {!!})

    cong : ∀ {v} {B : I.₀ → Type v} (f : ∀ x → B x)
         → ∀ {x y} (p : x ≈ y) → Disp B p (f x) (f y)
    cov-fib : ∀ {v} (B : I.₀ → Type v) → Disp.is-cov-fib B

    -- dcong : ∀ {u v} {A : Type u} {B : A → Type v}
    --       → ∀ {x y} (f : ∀ x → B x) (p : x ≈ y)
    --       → Disp B p (f x) (f y)

  --_∙_ = concat; infixr 9 _∙_

  -- Composite : ∀ {u} {A : Type u} {x y z : A} → x ≈ y → y ≈ z → Type u
  -- Composite {x = x} {y = y} {z = z} p q = DepFan (x ≈_) (p ∙ q)



  -- sigma-path : ∀ {u v} {A : Type u} {B : A → Type v}
  --            → ∀ {x y} (p : x ≈ y) {a : B x} {b : B y}
  --            → Disp B p a b → (x , a) ≈ (y , b)
  -- sigma-path {y} p α = {!!} where
  --   contr refl (y , p , p , displayed-path p)
  --   p1 = fan-contr  _ ({!!} , ({!!} , {!!}))

    display-prop : ∀ {u v} {A : Type u} (B : A → Type v)
                  → {x y : A} (a : B x) (p : x ≈ y)
                  → is-prop (Fan B a p)
    idemp : ∀ {u} {A : Type u} {x : A} → Disp (_≈ x) refl (concat refl refl) refl

  component-paths : ∀ {u v} {A : Type u} (B : A → Type v)
             → {x : A} (a : B x) (t : Fan B a refl)
             → (a , drefl) ≈ t
  component-paths B a = display-prop B a refl (a , drefl)

  singl-fibers : ∀ {u} {A : Type u} (x : A)
               → ((y , q) : Σ y ∶ A , Disp (λ _ → A) refl x y)
               → (x , drefl) ≈ (y , q)
  singl-fibers {A = A} x = display-prop (λ _ → A) x (refl {x = x}) (x , drefl)

  -- path composites are unique
  composite-paths : ∀ {u} {A : Type u} {x y z : A}
                  → (p : x ≈ y) (q : y ≈ z) (c : Composite p q)
                  → (p ∙ q , drefl) ≈ (c .fst , c .snd)
  composite-paths {x = x} p q = component-paths (x ≈_) (p ∙ q)



  -- display-fibers : ∀ {u v} {A : Type u} {B : A → Type v} {x y}
  --                → (f : ∀ x → B x) (p : x ≈ y)
  --              → ((q , α) : Σ q ∶ x ≈ y , Disp B q (f x) (f y))
  --              → Disp (λ z → Σ λ (q : x ≈ z) → Disp B q (f x) (f z)) p (refl , dcong f refl) (q , α)
  -- display-fibers {A = A} f p (q , α) = {!!}

  -- J : ∀ {u v} {A : Type u} {x : A}
  --   → (P : ∀ y → x ≈ y → Type v)
  --   → P x refl → ∀ {y} (q : x ≈ y)
  --   → P y q
  -- J  {v = v} {x = x} P c {y} q = transport (cong (λ (f , s) → P f s) (singl-prop (y , q))) c

  field
    -- singl-snd : ∀ {u} {A : Type u} {a : A} ((x , q) : Singl a)
    --           → Disp (a ≈_) (cong fst (singl-contr (x , q))) (refl {x = a}) q

    -- 𝓙-refl : ∀ {u v} {A : Type u} (C : (x y : A) → x ≈ y → Type v)
    --        → (c : (a : A) → C a a refl)
    --        → (x : A) → Disp id refl (𝓙 C c refl) (c x)
    -- 𝓙-sym : ∀ {u} {A : Type u} {x y : A} (p : x ≈ y)
    --       → Disp id refl (sym p) (𝓙 (λ x y p → y ≈ x) erefl p)
    -- 𝓙-cong : ∀ {u v} {A : Type u} {B : Type v} (f : A → B)
    --        → ∀ {x y} (p : x ≈ y) → Disp ? id ? ?

  -- ap : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → ∀ {x y} → x ≈ y → f x ≈ f y
  -- ap f = 𝓙 (λ x y q → f x ≈ f y) (λ x → erefl (f x))

  singl-contr : ∀ {u} {A : Type u} {x : A} ((y , q) : Singl x) → (x , erefl x) ≈ (y , q)
  singl-contr {x = x} (y , q) = {!!} where
    β : {!!}
    β = singl-fibers (x , erefl x) ((y , q) , {!!})



private variable
  u : Level
  A : Type u

--   ap-refl : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) (x : A) → ap f (erefl x) ≡ erefl (f x)
--   ap-refl f = 𝓙-refl (λ x y q → f x ≈ f y) (λ x → erefl (f x))

--   sym : ∀ {u} {A : Type u} {x y : A} → x ≈ y → y ≈ x
--   sym = 𝓙 (λ x y p → y ≈ x) erefl

--   sym-refl : ∀ {u} {A : Type u} (x : A)
--            → sym refl ≡ (erefl x)
--   sym-refl = 𝓙-refl (λ x y p → y ≈ x) erefl

--   midpoint : ∀ {u} {A : Type u} {x y : A} → x ≈ y → A
--   midpoint {A = A} = 𝓙 (λ _ _ _ → A) id

--   midpoint-refl : ∀ {u} {A : Type u} (u : A) → midpoint (erefl u) ≡ u
--   midpoint-refl {A = A} = 𝓙-refl (λ _ _ _ → A) id

--   𝓙-idf : ∀ {u v} {A : Type u} (B : (x y : A) → x ≈ y → Type v)
--         → (let C = λ (x y : A) (p : x ≈ y) → B x y p → B x y p)
--         → (u : A) → 𝓙 C (λ x → idf (B x x refl)) refl ≡ idf (B u u refl)
--   𝓙-idf B = 𝓙-refl (λ x y p → B x y p → B x y p) (λ x → idf (B x x refl))

--   𝓙-id-refl : ∀ {u v} {A : Type u} (B : (x y : A) → x ≈ y → Type v)
--             → (let
--                 C = λ x y p → B x y p → B x y p
--                 φ = λ x → idf (B x x refl)
--                 D = λ x y p → (𝓙 C φ refl) ≡ id)
--             → (x : A) → 𝓙 D (𝓙-refl C φ) refl ≡ 𝓙-refl C φ x
--   𝓙-id-refl {A = A} B =
--     𝓙-refl (λ x y p → 𝓙 C (λ _ → id) refl ≡ idf (B x x refl)) (𝓙-refl C (λ _ → id)) where
--       C = λ (x y : A) (p : x ≈ y) → B x y p → B x y p

--   𝓙-2refl : ∀ {u v} {A : Type u} (B : (x y : A) → x ≈ y → Type v)
--           → (c : ∀ a → B a a refl) (a : A)
--           → 𝓙 (λ x _ _ → 𝓙 B c (erefl x) ≡ c x) (𝓙-refl B c) refl ≡ 𝓙-refl B c a
--   𝓙-2refl B c = 𝓙-refl (λ x y p → 𝓙 B c (erefl x) ≡ c x) (𝓙-refl B c)
--   -- one can actually keep going to 3, 4...

-- module _ {ids : Ids} where
--   open Ids ids
--   -- Principle 1: Identification induction
--   ind₌ : ∀ {u v} {A : Type u} (C : ∀ x y → x ≈ y → Type v)
--        → {x y : A} (p : x ≈ y) (c : (x : A) → C x x refl) → C x y p
--   ind₌ C p c = 𝓙 C c p

--   ind-refl : ∀ {u v} {A : Type u} (C : ∀ x y → x ≈ y → Type v)
--            → (c : (x : A) → C x x refl) {x : A}
--            → ind₌ C refl c ≡ c x
--   ind-refl C c {x} = 𝓙-refl C c x

--   -- Corollary 1: Transport
--   tr : ∀ {u v} {A : Type u} (B : A → Type v) {x y : A} → x ≈ y → B x → B y
--   tr {u} {v} {A} B {x = x} {y} p = ind₌ (λ x y _ → B x → B y) p (λ x → idf (B x))

--   idtofun : ∀ {u} {A B : Type u} → A ≈ B → A → B
--   idtofun = tr id

--   happly : ∀ {u v} {A : Type u} {B : A → Type v}
--          → {f g : ∀ a → B a} → f ≈ g → (x : A) → f x ≈ g x
--   happly {v = v} {A = A} {B} {f} {g} p x = ind₌ C p (λ f → erefl (f x)) where
--     C : (h k : ∀ a → B a) → h ≈ k → Type v
--     C h k _ = h x ≈ k x

--   happly-refl : ∀ {u v} {A : Type u} {B : A → Type v} (f : ∀ a → B a) {x : A}
--               → happly (erefl f) x ≡ erefl (f x)
--   happly-refl {v} {B} f {x} = ind-refl (λ h k _ → h x ≈ k x) (λ f → erefl (f x))

--   -- We can prove that transport on refl has equivalent action to id
--   -- directly from the id induction comp rule
--   tr-htpy : ∀ {u v} {A : Type u} (B : A → Type v) (x : A) → tr B (erefl x) ≡ id
--   tr-htpy B _ = ind-refl (λ x y _ → B x → B y) (λ _ b → b)

--   -- This is harder to do (without additional assumptions about the metatheory's equality)
--   tr-refl : ∀ {u v} {A : Type u} (B : A → Type v)
--           → {x : A} (b : B x) → tr B refl b ≡ b
--   tr-refl B {x} b = {!!} where
--     -- motive is `tr B refl b ≡ b`, we need to get this in a form like:
--     -- `𝓙 C (erefl x) c ≡ c x` where `∀ x → c x ≡ b` for some c, C.
--     -- Note: this means that `c` is weakly constant
--     --
--     -- But we could have it easily if we have the below assumptions re: our metatheory
--     --  1. transport in its Id
--     --  2. at least one self-homotopy over function application on f
--     module _
--       (t : {f g : B x → B x} → f ≡ g → ((h : B x → B x) → h b ≡ h b) → f b ≡ g b)
--       (d : (f : B x → B x) → f b ≡ f b)
--       where
--       meta-happly : {f g : B x → B x} → f ≡ g → f b ≡ g b
--       meta-happly q = t q d

--       goal : tr B refl b ≡ b
--       goal = meta-happly (tr-htpy B x)

--   -- Definition 2: Singleton type
--   ⟨_⟩₁ : ∀ {u} {A : Type u} (x : A) → Type u
--   ⟨_⟩₁ {A = A} x = Σ λ (y : A) → x ≈ y

--   -- Corollary 3: Contractibility of Singletons
--   singl-contr : ∀ {u} {A : Type u} {a : A} → ((x , q) : ⟨ a ⟩₁) → a , refl ≈ x , q
--   singl-contr {u} {A} (x , q) =
--     let
--       B : (x y : A) → x ≈ y → Type u
--       B = λ x y p → (x , refl {x = x}) ≈ (y , p)
--     in ind₌ B q (λ a → erefl (a , refl))

--   -- Based path induction. We'll follow Hofmann's proof cited by Sterling
--   -- (1lab uses this as well IIRC, but with subst2 instead)
--   J : ∀ {u v} {A : Type u} {x : A} (B : ∀ y → x ≈ y → Type v)
--     → B x refl → ∀ {y} (p : x ≈ y) → B y p
--   J {v} {x} B c {y} p = tr B♯ (singl-contr (y , p)) c where
--     B♯ : ⟨ x ⟩₁ → Type v
--     B♯ (y , p) = B y p
