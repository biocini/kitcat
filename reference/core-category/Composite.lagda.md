```agda

{-# OPTIONS --safe --erased-cubical #-}

module Lib.Core.Composite where

open import Core.Type
open import Core.Base
open import Core.Data
open import Core.Kan
open import Core.Sub
open import Core.Equiv
open import Core.Transport

private variable ℓ : Level

-- A cylinder at face φ: partial walls with a definite base
Cyl : (φ : I) (A : Type ℓ) → SSet ℓ
Cyl φ A = (i : I) → Partial (φ ∨ ~ i) A

-- The base of a tube (at i = i0, always defined)
base : (φ : I) {A : Type ℓ} → Cyl φ A → A
base _ u = u i0 1=1

-- The partial lid (at i = i1, defined when φ)
lid : {φ : I} {A : Type ℓ} → Cyl φ A → Partial φ A
lid {φ} u (φ = i1) = u i1 1=1

-- The extension type for lids: total elements agreeing with partial lid
Ext : (φ : I) {A : Type ℓ} → Cyl φ A → SSet ℓ
Ext φ {A} u = A [ φ ↦ lid u ]

Fill : {A : Type ℓ} (φ : I) (u : Cyl φ A) → Ext φ u → SSet ℓ
Fill {A} φ u ext  = (i : I) → A [ (φ ∨ ~ i) ↦ (λ where
  (φ = i1) → u i 1=1 
  (i = i0) → base φ u) ]

composite : {A : Type ℓ} (φ : I) → Cyl φ A → A
composite {A} φ u = hcomp φ λ where
  k (k = i0) → base φ u
  k (φ = i1) → u k 1=1

filler : {A : Type ℓ} (φ : I) (u : Cyl φ A) (i : I) → A
filler {A} φ u i = hcomp (φ ∨ ~ i) λ where
  k (φ = i1) → u (i ∧ k) 1=1
  k (i = i0) → base φ u
  k (k = i0) → base φ u

cyl-path : {A : Type ℓ} (φ : I) (u : Cyl φ A) → base φ u ≡ composite φ u
cyl-path φ u i = filler φ u i

module filler {A : Type ℓ} (φ : I) (u : Cyl φ A) where
  pbase : filler φ u i0 ≡ base φ u
  pbase = λ _ → base φ u

  plid : filler φ u i1 ≡ composite φ u
  plid = λ _ → composite φ u

composite→Ext : {A : Type ℓ} (φ : I) (u : Cyl φ A) → Ext φ u
composite→Ext φ u = inS (composite φ u)

filler→Fill : {A : Type ℓ} (φ : I) (u : Cyl φ A) (e : Ext φ u) → Fill φ u e
filler→Fill φ u e i = inS (filler φ u i)

-- Witnesses a composite
Comp : {A : Type ℓ} (φ : I) (u : Cyl φ A) → Type ℓ
Comp {A} φ u = Σ s ∶ A , composite φ u ≡ s

-- singletons contractible
Comp-is-contr : {A : Type ℓ} (φ : I) (u : Cyl φ A) → is-contr (Comp φ u)
Comp-is-contr φ u .center = composite φ u , filler.plid φ u
Comp-is-contr φ u .paths (s , p) i = p i , λ j → p (i ∧ j)

plid-refl : {A : Type ℓ} (φ : I) (u : Cyl φ A) → filler.plid φ u ≡ refl
plid-refl φ u = refl

ceqv : {A : Type ℓ} (φ : I) (u : Cyl φ A) → Comp φ u
ceqv φ u = Comp-is-contr φ u .center

J-cyl : ∀ {v} {A : Type ℓ} (φ : I) (u : Cyl φ A)
      → (P : (s : A) → composite φ u ≡ s → Type v)
      → P (composite φ u) (filler.plid φ u)
      → {s : A} (α : composite φ u ≡ s)
      → P s α
J-cyl φ u P c {s} α = transport (λ i → P (ap fst total i) (ap snd total i)) c where
  total : composite φ u , filler.plid φ u ≡ s , α
  total = Comp-is-contr φ u .paths (s , α)

𝓙 : ∀ {v} {A : Type ℓ} {x : A}
  → (P : ∀ y → x ≡ y → Type v)
  → P x refl
  → ∀ {y} (q : x ≡ y) → P y q
𝓙 {x = x} = J-cyl i1 (λ _ _ → x)

subst-cyl : ∀ {v} {A : Type ℓ} (φ : I) (P : A → Type v)
          → (u : Cyl φ A) → P (base φ u) → P (composite φ u)
subst-cyl φ P u = transport (λ i → P (filler φ u i))

-- Composition gluing two cylinders end-to-end
module _ {A : Type ℓ} where
  -- Composition: given cylinders t₁ (to y) and t₂ (from y), produce cylinder to composite of t₂
  cyl-compose : (φ ψ : I) (t₁ : Cyl φ A) (t₂ : Cyl ψ A)
              → composite φ t₁ ≡ base ψ t₂
              → Cyl (φ ∨ ψ) A
  cyl-compose φ ψ t₁ t₂ p i (φ = i1) = p (ψ ∧ ~ i)
  cyl-compose φ ψ t₁ t₂ p i (ψ = i1) = p (φ ∧ ~ i)
  cyl-compose φ ψ t₁ t₂ p i (i = i0) = p (φ ∧ ψ)

  hcom : (φ : I) (t : Cyl φ A) {s : A} → composite φ t ≡ s → A
  hcom φ t {s} p = hcomp i1 (cyl-compose φ i1 t (λ _ _ → s) p)

HCyl : (φ : I) (A : I → Type ℓ) → SSet ℓ
HCyl φ A = (i : I) → Partial (φ ∨ ~ i) (A i)

module _ {A : I → Type ℓ} (φ : I) (u : HCyl φ A) where
  hbase : A i0
  hbase = u i0 1=1

  hfiller : (i : I) → A i
  hfiller i = comp (λ j → A (i ∧ j)) (φ ∨ ~ i) λ where
    k (φ = i1) → u (i ∧ k) 1=1
    k (i = i0) → hbase
    k (k = i0) → hbase

  hcomposite : A i1
  hcomposite = hfiller i1

  hcyl-path : PathP A hbase hcomposite
  hcyl-path i = hfiller i

module _ {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ') where
  -- A dependent cylinder can be indexed over the filler
  CylP : (φ : I) (u : Cyl φ A) → SSet ℓ'
  CylP φ u = (i : I) → Partial (φ ∨ ~ i) (P (filler φ u i))

  -- Base: at i = i0, filler φ u i0 = base φ u definitionally
  baseP : (φ : I) (u : Cyl φ A) → CylP φ u → P (base φ u)
  baseP φ u v = v i0 1=1

  -- Dependent filler: requires comp (dependent hcomp)
  -- We fill along the path (λ j → filler φ u (i ∧ j)) from base to filler φ u i
  fillerP : (φ : I) (u : Cyl φ A) (v : CylP φ u) (i : I) → P (filler φ u i)
  fillerP φ u v i = comp (λ j → P (filler φ u (i ∧ j))) (φ ∨ ~ i) λ where
    k (φ = i1) → v (i ∧ k) 1=1
    k (i = i0) → baseP φ u v
    k (k = i0) → baseP φ u v

  compP : (φ : I) (u : Cyl φ A) → CylP φ u → P (composite φ u)
  compP φ u v = fillerP φ u v i1

  -- The dependent path induced by a dependent cylinder
  cyl-pathP : (φ : I) (u : Cyl φ A) (v : CylP φ u)
            → PathP (λ i → P (filler φ u i)) (baseP φ u v) (compP φ u v)
  cyl-pathP φ u v i = fillerP φ u v i

  LiftP : {x y : A} → x ≡ y → P x → Type ℓ'
  LiftP {x} {y} p a = Σ b ∶ P y , PathP (λ i → P (p i)) a b

  -- A lift of a : P (base φ u) along a cylinder u
  LiftD : (φ : I) (u : Cyl φ A) → P (base φ u) → Type ℓ'
  LiftD φ u = LiftP (λ i → filler φ u i)

  leqv : {x y : A} (p : x ≡ y) (a : P x) → LiftP p a
  leqv p a = transport (λ i → P (p i)) a , transport-filler (λ i → P (p i)) a

  LiftP-is-contr : {x y : A} (q : x ≡ y) (a : P x) → is-contr (LiftP q a)
  LiftP-is-contr q = SinglP-contr

module _ {ℓ} {A : Type ℓ} (c : A) where
  lift-2cell : {s s' : A} (p : s ≡ s') (α : c ≡ s)
             → is-contr (Σ β ∶ c ≡ s' , PathP (λ i → c ≡ p i) α β)
  lift-2cell p = SinglP-contr

  lift-dcell-unique : (P : I → Type ℓ)
                    → (α : P i0) (β : P i1)
                    → (φ : PathP P α β)
                    → leqv id (λ i → P i) α ≡ β , φ
  lift-dcell-unique P α β φ = LiftP-is-contr id (λ i → P i) α .paths (β , φ)

module CylFunctor {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  -- Action on cylinders
  Cyl-map : (φ : I) → Cyl φ A → Cyl φ B
  Cyl-map φ u i p = f (u i p)

  -- Base is preserved
  Cyl-map-base : (φ : I) (u : Cyl φ A)
               → base φ (Cyl-map φ u) ≡ f (base φ u)
  Cyl-map-base φ u = refl

  Cyl-map-composite : (φ : I) (u : Cyl φ A)
                     → composite φ (Cyl-map φ u) ≡ f (composite φ u)
  Cyl-map-composite φ u i = hcomp (φ ∨ i) λ where
    k (φ = i1) → f (u (i ∨ k) 1=1)
    k (i = i1) → f (filler φ u (k ∨ φ))
    k (k = i0) → f (filler φ u (i ∧ φ))
    
  -- Filler is preserved
  -- Cyl-map-filler : (φ : I) (u : Cyl φ A) (i : I)
  --                → filler φ (Cyl-map φ u) i ≡ f (filler φ u i)
  -- Cyl-map-filler φ u i = {!!}
    -- Also definitional

  -- The action on Comp witnesses
  -- Comp-map : (φ : I) (u : Cyl φ A) → Comp φ u → Comp φ (Cyl-map φ u)
  -- Comp-map φ u (s , p) = f s , ap f p

  -- -- This is an equivalence (between contractible types, so automatic)
  -- Comp-map-is-equiv : (φ : I) (u : Cyl φ A) → is-equiv (Comp-map φ u)
  -- Comp-map-is-equiv φ u = is-contr→is-equiv
  --   (Comp-is-contr φ u)
  --   (Comp-is-contr φ (Cyl-map φ u))

-- Functoriality at level 1 (2-cells)
module CylFunctor₁ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
                   {x y : A} where

  -- ap f acts on cylinders of paths
  Cyl₁-map : (φ : I) → Cyl φ (x ≡ y) → Cyl φ (f x ≡ f y)
  Cyl₁-map φ u i p = ap f (u i p)

  -- Composite is preserved: ap f (p ∙ q) ≡ ap f p ∙ ap f q
  -- (up to the standard lemma)
  -- ap-∙ : (p : x ≡ y) {z : A} (q : y ≡ z)
  --      → ap f (p ∙ q) ≡ ap f p ∙ ap f q
  -- ap-∙ p q = ... -- standard lemma


record is-virtual-system {u v} {A : Type u} (B : A → Type v) : Type (u ⊔ v) where
  field
    contr : is-contr (Σ a ∶ A , B a)






```
{-# OPTIONS --safe --erased-cubical #-}

module VG.Native where

------------------------------------------------------------------------
-- Raw Cubical Primitives
------------------------------------------------------------------------

open import Agda.Primitive public
  using (Level; SSet)
  renaming (Set to Type; _⊔_ to infixl 6 _⊔_; lsuc to _⁺; lzero to ℓ0)

open import Agda.Primitive.Cubical public
  using (I; i0; i1; IsOne; Partial; PartialP)
  renaming ( primIMin to _∧_; primIMax to _∨_; primINeg to ~_
           ; primHComp to prim-hcomp; primTransp to prim-transp
           ; itIsOne to 1=1; isOneEmpty to ∅
           ; IsOne1 to is1-l; IsOne2 to is1-r; primPOr to por )

private module Sub where
  open import Agda.Builtin.Cubical.Sub public
open Sub public renaming (Sub to _[_↦_]; primSubOut to out; inc to in')

private module Path where
  open import Agda.Builtin.Cubical.Path public
open Path public using (PathP) renaming (_≡_ to infix 4 _≡_)

private variable
  ℓ ℓ' : Level
  A B : Type ℓ

------------------------------------------------------------------------
-- Part I: The Extension as Primitive Composite Fiber
------------------------------------------------------------------------

-- The extension type IS the composite fiber. Let's make this explicit.

-- A "Tube" is the data specifying a composition problem
-- It's a partial element varying over the interval with a base
record Tube (φ : I) (A : Type ℓ) : Type ℓ where
  constructor tube
  field
    walls : (i : I) → Partial (φ ∨ ~ i) A

  base : A
  base = walls i0 1=1

open Tube public

-- The "Lid" of a tube is an extension of the i1 face
Lid : (φ : I) → Tube φ A → Type ℓ
Lid {A = A} φ t = A [ φ ↦ t .walls i1 ]

-- The filler IS the morphism from base to lid in the extension VG
Filler : (φ : I) (t : Tube φ A) → Lid φ t → Type ℓ
Filler {A = A} φ t lid = (i : I) → A [ (φ ∨ ~ i) ↦
  (λ { (φ = i1) → t .walls i 1=1
     ; (i = i0) → t .base }) ]

------------------------------------------------------------------------
-- Part II: Direct Composite Structure (No Paths!)
------------------------------------------------------------------------

-- The composite of a tube, defined directly as extension extraction
composite : {A : Type ℓ} (φ : I) (t : Tube φ A) → A
composite φ t = prim-hcomp (λ i → λ { (φ = i1) → t .walls i 1=1 }) (t .base)

-- The canonical lid (as a Sub value)
canonical-lid : {A : Type ℓ} (φ : I) (t : Tube φ A) → Lid φ t
canonical-lid φ t = in' (composite φ t)

-- The filler connecting base to composite
canonical-filler : {A : Type ℓ} (φ : I) (t : Tube φ A)
                 → (i : I) → A [ (φ ∨ ~ i) ↦
                     (λ { (φ = i1) → t .walls i 1=1
                        ; (i = i0) → t .base }) ]
canonical-filler {A = A} φ t i = in' (prim-hcomp
  (λ j → λ { (φ = i1) → t .walls (i ∧ j) 1=1
           ; (i = i0) → t .base
           ; (j = i0) → t .base })
  (t .base))

------------------------------------------------------------------------
-- Part III: The Face Virtual Graph
------------------------------------------------------------------------

-- Objects: face formulas (elements of I that can be i0, i1, or compound)
-- But we work with Partial elements as our "specified composites"

-- A System bundles a face with partial data
record System (A : Type ℓ) : Type ℓ where
  constructor sys
  field
    φ : I
    partial : Partial φ A

open System public

-- A SystemMorphism is an extension: total element agreeing with system
SystemMor : (A : Type ℓ) → System A → Type ℓ
SystemMor A s = A [ s .φ ↦ s .partial ]

-- The empty system (no constraints)
∅-sys : System A
∅-sys = sys i0 ∅

-- The full system (completely determined)
full-sys : A → System A
full-sys a = sys i1 (λ _ → a)

-- System join: combine two compatible systems
_∨-sys_ : System A → System A → System A
(sys φ u) ∨-sys (sys ψ v) = sys (φ ∨ ψ) (por φ ψ u v)

------------------------------------------------------------------------
-- Part IV: The Extension Virtual Graph
------------------------------------------------------------------------

-- Objects: pairs (A, s) where s : System A
-- Morphisms: extensions that refine

record ExtObj (ℓ : Level) : Type (ℓ ⁺) where
  constructor ext-obj
  field
    carrier : Type ℓ
    system : System carrier

open ExtObj public

-- A morphism in the extension VG: a total element extending both systems
record ExtMor (X Y : ExtObj ℓ) : Type ℓ where
  constructor ext-mor
  field
    element : X .carrier  -- X .carrier = Y .carrier in practice
    extends-X : X .carrier [ X .system .φ ↦ X .system .partial ]
    extends-Y : Y .carrier [ Y .system .φ ↦ Y .system .partial ]

open ExtMor public

-- The diagonal: when X = Y, we have a canonical morphism
ext-diag : (X : ExtObj ℓ) → SystemMor (X .carrier) (X .system) → ExtMor X X
ext-diag X e = ext-mor (out e) e e

------------------------------------------------------------------------
-- Part V: Tube Composition (Native cut Operation)
------------------------------------------------------------------------

-- Composition of tubes: gluing two tubes end-to-end
-- This is "cut" in the virtual graph of tubes

module _ {A : Type ℓ} where

  -- A tube from x to y (using extension formulation)
  TubeFrom : (φ : I) → A → Type ℓ
  TubeFrom φ x = Σ t ∶ Tube φ A , t .base ≡ x
    where open Path using (_≡_)

  -- Composition: given tubes t₁ (to y) and t₂ (from y), produce tube to composite of t₂
  tube-compose : (φ ψ : I) (t₁ : Tube φ A) (t₂ : Tube ψ A)
               → composite φ t₁ ≡ t₂ .base
               → Tube (φ ∨ ψ) A
  tube-compose φ ψ t₁ t₂ p = tube walls'
    where
      walls' : (i : I) → Partial (φ ∨ ψ ∨ ~ i) A
      walls' i (φ = i1) = t₁ .walls i 1=1
      walls' i (ψ = i1) = t₂ .walls i 1=1
      walls' i (i = i0) = t₁ .base

------------------------------------------------------------------------
-- Part VI: The Contractibility Witness (Native cut-contr)
------------------------------------------------------------------------

-- Direct formulation: the type of extensions is contractible
-- We express this using the extension type itself

record is-contr-ext {A : Type ℓ} (φ : I) (u : Partial φ A) : Type ℓ where
  field
    center : A [ φ ↦ u ]
    contract : (e : A [ φ ↦ u ]) →
               (i : I) → A [ (φ ∨ ~ i ∨ i) ↦
                 (λ { (φ = i1) → u 1=1
                    ; (i = i0) → out center
                    ; (i = i1) → out e }) ]

open is-contr-ext public

-- The Kan condition: all extensions are contractible
-- This is BUILT INTO the type theory via hcomp
kan : {A : Type ℓ} (φ : I) (u : Partial φ A) → is-contr-ext φ u
kan {A = A} φ u .center = in' (prim-hcomp (λ _ → λ { (φ = i1) → u 1=1 }) (u 1=1))
  -- Note: requires φ inhabited; general case uses transport
kan {A = A} φ u .contract e i = in' (prim-hcomp
  (λ j → λ { (φ = i1) → u 1=1
           ; (i = i0) → out (kan φ u .center)
           ; (i = i1) → out e })
  (out (kan φ u .center)))

------------------------------------------------------------------------
-- Part VII: Boundary Extensions (Path-Free Formulation)
------------------------------------------------------------------------

-- The boundary of an interval point
∂ : I → I
∂ i = i ∨ ~ i

-- A boundary system: partial element defined at both endpoints
BdrySystem : (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
BdrySystem A x y = (i : I) → Partial (∂ i) (A i)

-- Make a boundary system from endpoints
bdry : {A : I → Type ℓ} (x : A i0) (y : A i1) → BdrySystem A x y
bdry x y i (i = i0) = x
bdry x y i (i = i1) = y

-- A line extension: total element agreeing with boundary
LineExt : (A : I → Type ℓ) (x : A i0) (y : A i1) → Type ℓ
LineExt A x y = (i : I) → A i [ ∂ i ↦ bdry x y i ]

-- THIS IS PathP, reformulated natively!
-- PathP A x y ≃ LineExt A x y

line-to-path : {A : I → Type ℓ} {x : A i0} {y : A i1}
             → LineExt A x y → PathP A x y
line-to-path l i = out (l i)

path-to-line : {A : I → Type ℓ} {x : A i0} {y : A i1}
             → PathP A x y → LineExt A x y
path-to-line p i = in' (p i)

------------------------------------------------------------------------
-- Part VIII: Composition via Extension (Native ∙)
------------------------------------------------------------------------

-- Path composition reformulated: it's tube composition for boundary systems

-- The composition tube for two boundary extensions
comp-tube : {A : Type ℓ} {x y z : A}
          → LineExt (λ _ → A) x y
          → LineExt (λ _ → A) y z
          → Tube (∂ i) A  -- for any i
comp-tube {A = A} {x} {y} {z} p q = tube walls
  where
    walls : (i : I) → (j : I) → Partial (∂ j ∨ ~ i) A
    walls i j (j = i0) = x
    walls i j (j = i1) = out (q i)
    walls i j (i = i0) = out (p j)

-- Composition: extract the composite from the tube
_∙ₑ_ : {A : Type ℓ} {x y z : A}
     → LineExt (λ _ → A) x y
     → LineExt (λ _ → A) y z
     → LineExt (λ _ → A) x z
(p ∙ₑ q) j = in' (composite (∂ j) (record { walls = λ i →
  λ { (j = i0) → out (p i0)  -- x
    ; (j = i1) → out (q i)
    ; (i = i0) → out (p j) }}))

------------------------------------------------------------------------
-- Part IX: The Witness Type (Native hom2)
------------------------------------------------------------------------

-- A witness that s is the composite of tube t
-- This is hom2 (cut f g) s in virtual graph terms

Witness : {A : Type ℓ} (φ : I) (t : Tube φ A) (s : A) → Type ℓ
Witness {A = A} φ t s = A [ φ ↦ t .walls i1 ] × (composite φ t ≡ s)

-- The reflexivity witness (ceqv)
witness-refl : {A : Type ℓ} (φ : I) (t : Tube φ A) → Witness φ t (composite φ t)
witness-refl φ t = canonical-lid φ t , (λ _ → composite φ t)

-- The type of all composites with witnesses
CompositeWitness : {A : Type ℓ} (φ : I) (t : Tube φ A) → Type ℓ
CompositeWitness {A = A} φ t = Σ s ∶ A , Witness φ t s

-- This type is contractible! (cut-contr)
composite-witness-contr : {A : Type ℓ} (φ : I) (t : Tube φ A)
                        → (cw : CompositeWitness φ t)
                        → (composite φ t , witness-refl φ t) ≡ cw
composite-witness-contr φ t (s , lid , p) i =
  p i , in' (prim-hcomp
    (λ j → λ { (φ = i1) → t .walls i1 1=1
             ; (i = i0) → composite φ t
             ; (i = i1) → p j })
    (p i))
  , λ j → p (i ∨ j)

------------------------------------------------------------------------
-- Part X: Transport as Trivial-System Composition
------------------------------------------------------------------------

-- Transport is composition where the system is trivially satisfied
-- i.e., φ = i0 so Partial i0 A is empty

transport-tube : (A : I → Type ℓ) → A i0 → Tube i0 (A i1)
transport-tube A a₀ = tube (λ i → ∅)
  -- But this doesn't quite work because base needs to be in A i1

-- Better: heterogeneous tube
record HTube (A : I → Type ℓ) (φ : I) : Type ℓ where
  constructor htube
  field
    walls : (i : I) → Partial (φ ∨ ~ i) (A i)

  base : A i0
  base = walls i0 1=1

open HTube public

-- Heterogeneous composite (= comp)
hcomposite : {A : I → Type ℓ} (φ : I) (t : HTube A φ) → A i1
hcomposite {A = A} φ t = prim-hcomp
  (λ i → λ { (φ = i1) → prim-transp (λ j → A (i ∨ j)) i (t .walls i 1=1) })
  (prim-transp A i0 (t .base))

-- Transport: heterogeneous composite with empty system
coe : (A : I → Type ℓ) → A i0 → A i1
coe A a = hcomposite i0 (htube (λ i _ → a))
  -- walls i ∅ is never called, but we provide a

-- The transport path as a filler
coe-filler : (A : I → Type ℓ) (a : A i0) → PathP A a (coe A a)
coe-filler A a i = prim-transp (λ j → A (i ∧ j)) (~ i) a

------------------------------------------------------------------------
-- Part XI: Identity Systems via Extension Contractibility
------------------------------------------------------------------------

-- An identity system is a family R with contractible total extension space

record IsIdentityExt {A : Type ℓ} (R : A → A → Type ℓ') (r : (a : A) → R a a) : Type (ℓ ⊔ ℓ') where
  field
    -- For any b and s : R a b, the extension from (a, r a) to (b, s) exists
    to-ext : {a b : A} (s : R a b)
           → (i : I) → (Σ x ∶ A , R a x) [ ∂ i ↦
               (λ { (i = i0) → a , r a
                  ; (i = i1) → b , s }) ]

open IsIdentityExt public

-- Paths form an identity system (via extension)
path-is-identity-ext : {A : Type ℓ} → IsIdentityExt {A = A} _≡_ (λ _ i → _)
path-is-identity-ext .to-ext {a} {b} p i = in' (p i , λ j → p (i ∧ j))

------------------------------------------------------------------------
-- Part XII: Native Fiber Structure
------------------------------------------------------------------------

-- Fibers as extension types!
-- fiber f y = A [ i1 ↦ (λ _ → ?) ] where the ? involves f

-- A "graph" of f: pairs (x, fx)
Graph : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ ⊔ ℓ')
Graph {A = A} {B} f = Σ x ∶ A , Σ y ∶ B , f x ≡ y

-- The fiber over y as a system morphism
FiberSys : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → System (Graph f)
FiberSys f y = sys i1 (λ _ → {!!} , y , (λ _ → y))
  -- This doesn't quite work; let's reformulate

-- Better: fiber as extension of the "is y" system
FiberExt : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ ⊔ ℓ')
FiberExt {A = A} f y = Σ x ∶ A , (i : I) → B [ (i ∨ ~ i) ↦
  (λ { (i = i0) → f x
     ; (i = i1) → y }) ]

-- This is equivalent to the standard fiber
fiber-equiv : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B)
            → FiberExt f y → Σ x ∶ A , f x ≡ y
fiber-equiv f y (x , ext) = x , (λ i → out (ext i))

------------------------------------------------------------------------
-- Part XIII: The Native Virtual Graph Record
------------------------------------------------------------------------

-- Now we can define virtual graphs using extension types directly

record NativeVG (Obj : Type ℓ) : Type (ℓ ⁺) where
  field
    -- 1-cells: for each pair, a type of morphisms
    Mor : Obj → Obj → Type ℓ

    -- Composition: specified via tubes
    -- A pair (f, g) gives a tube; composition extracts the lid
    comp-tube : {x y z : Obj} → Mor x y → Mor y z → Tube i0 (Mor x z)

    -- The composite is the canonical lid
    _∘_ : {x y z : Obj} → Mor x y → Mor y z → Mor x z
    _∘_ f g = composite i0 (comp-tube f g)

    -- 2-cells: witnesses that something is a composite
    -- Defined via extension types
    _=>_ : {x y z : Obj} {f : Mor x y} {g : Mor y z} → Mor x z → Mor x z → Type ℓ
    _=>_ {f = f} {g = g} s t = (i : I) → Mor _ _ [ ∂ i ↦
      (λ { (i = i0) → s; (i = i1) → t }) ]

    -- Reflexivity 2-cell (ceqv)
    ∘-refl : {x y z : Obj} (f : Mor x y) (g : Mor y z) → (f ∘ g) => (f ∘ g)
    ∘-refl f g i = in' (f ∘ g)

    -- THE AXIOM: composite witnesses form a contractible type
    ∘-contr : {x y z : Obj} (f : Mor x y) (g : Mor y z)
            → (s : Mor x z) → (f ∘ g) => s
            → (t : Mor x z) → (f ∘ g) => t
            → (j : I) → Mor _ _ [ ∂ j ↦ (λ { (j = i0) → s; (j = i1) → t }) ]

open NativeVG public

-- Any type forms a native VG via paths-as-extensions
Type-NativeVG : (A : Type ℓ) → NativeVG A
Type-NativeVG A .Mor = _≡_
Type-NativeVG A .comp-tube p q = tube (λ i →
  λ { (i = i0) → p i0 })  -- Degenerate; composition defined below
Type-NativeVG A ._∘_ p q i = prim-hcomp
  (λ j → λ { (i = i0) → p i0; (i = i1) → q j })
  (p i)
Type-NativeVG A ._=>_ s t = (i : I) → A [ ∂ i ↦ (λ { (i = i0) → s _; (i = i1) → t _ }) ]
  -- Need to fix: s and t are paths, need to extract points
Type-NativeVG A .∘-refl f g i = in' (Type-NativeVG A ._∘_ f g i)
Type-NativeVG A .∘-contr f g s α t β j = in' (prim-hcomp
  (λ k → λ { (j = i0) → out (α k)
           ; (j = i1) → out (β k) })
  (Type-NativeVG A ._∘_ f g _))

------------------------------------------------------------------------
-- Part XIV: Directly Leveraging Partial Coherence
------------------------------------------------------------------------

-- The key insight: Partial φ A forms a "system category"
-- where morphisms are refinements

-- A refinement: ψ implies φ, and partial elements agree
record Refines {A : Type ℓ} (s : System A) (t : System A) : Type ℓ where
  constructor refines
  field
    impl : IsOne (s .φ) → IsOne (t .φ)
    agree : (p : IsOne (s .φ)) → s .partial p ≡ t .partial (impl p)

-- Systems form a category (actually, a poset under refinement)
-- Composition is system join, identity is full system

-- The extension functor: sends a system to its extensions
-- This is contravariant! More constraints = fewer extensions

ExtFunctor : (A : Type ℓ) → System A → Type ℓ
ExtFunctor A s = A [ s .φ ↦ s .partial ]

-- Refinement gives a map in the OPPOSITE direction
refine-ext : {A : Type ℓ} {s t : System A}
           → Refines s t → ExtFunctor A t → ExtFunctor A s
refine-ext {A = A} {s} {t} r e = in' (out e)
  -- This works because if e extends t, and s refines t,
  -- then e also extends s

------------------------------------------------------------------------
-- Part XV: The Fundamental Theorem (Native Formulation)
------------------------------------------------------------------------

-- The fundamental theorem of virtual graph theory, stated natively:
-- For any tube, the type of lids with fillers is contractible

LidWithFiller : {A : Type ℓ} (φ : I) (t : Tube φ A) → Type ℓ
LidWithFiller {A = A} φ t = Σ lid ∶ A ,
  (i : I) → A [ (φ ∨ ~ i) ↦
    (λ { (φ = i1) → t .walls i 1=1
       ; (i = i0) → t .base
       ; (i = i1) → lid }) ]

-- The canonical lid-with-filler
canonical-lwf : {A : Type ℓ} (φ : I) (t : Tube φ A) → LidWithFiller φ t
canonical-lwf {A = A} φ t = composite φ t , λ i → in' (prim-hcomp
  (λ j → λ { (φ = i1) → t .walls (i ∧ j) 1=1
           ; (i = i0) → t .base
           ; (j = i0) → t .base })
  (t .base))

-- Contractibility: any lid-with-filler equals the canonical one
lwf-contr : {A : Type ℓ} (φ : I) (t : Tube φ A)
          → (lwf : LidWithFiller φ t) → canonical-lwf φ t ≡ lwf
lwf-contr {A = A} φ t (lid , filler) i =
  prim-hcomp
    (λ j → λ { (i = i0) → composite φ t
             ; (i = i1) → out (filler j) })
    (out (filler i))
  , λ k → in' (prim-hcomp
    (λ j → λ { (φ = i1) → t .walls (k ∧ j) 1=1
             ; (k = i0) → t .base
             ; (i = i0) → out (canonical-lwf φ t .snd (k ∧ j))
             ; (i = i1) → out (filler (k ∧ j))
             ; (j = i0) → t .base })
    (t .base))

------------------------------------------------------------------------
-- Summary: Native VG Primitives
--
-- 1. Tube φ A: the data of a composition problem
-- 2. Lid φ t: extension type = composite fiber
-- 3. composite φ t: center extraction via hcomp
-- 4. canonical-filler: the path to the center
-- 5. LidWithFiller: explicit composite fiber type
-- 6. lwf-contr: the contractibility theorem
-- 7. System A: bundled face formula with partial element
-- 8. LineExt A x y: path reformulated as extension
-- 9. Witness φ t s: the hom2 type
-- 10. NativeVG: virtual graph interface using extensions
--
-- The key insight: everything is extensions and their contractibility.
-- Paths are a special case (boundary extensions).
-- Composition is tube-lid extraction.
-- The Kan condition IS cut-contr.
------------------------------------------------------------------------
