I wanted to see what I could derive about the identity type with a very minimal
set of assumptions, implementing Sterling's reflexive graphs paper

```
{-# OPTIONS --safe --erased-cubical #-}

open import Lib.Graph.Reflexive.Base

module Lib.Core.Equality {u} (R : Rx u u) where

open import Core.Base
open import Core.Data
open import Core.HLevel
open import Core.Equiv
open import Core.Type

open Rx R renaming (₀ to Ob; ₁ to infix 6 _≈_)

import Lib.Graph.Reflexive.Displayed

private
  module Displayed {v} (B : Ob → Type v)
    (Disp : ∀ {v} (B : Ob → Type v) {x y} → x ≈ y → B x → B y → Type v)
    (drx : ∀ {v} {B : Ob → Type v} {x} (a : B x) → Disp B (rx x) a a)
    where
    open Lib.Graph.Reflexive.Displayed R public

    disp : Disp-rx v v
    disp .Disp-rx.Ob = B
    disp .Disp-rx.₂ = Disp B
    disp .Disp-rx.drx x = drx

    open Lib.Graph.Reflexive.Displayed.display R disp public

record Groupoid : Typeω where
  field
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

```
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
