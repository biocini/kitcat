```
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Core.Virtual where

open import Core.Base
open import Core.Data
open import Core.HLevel
open import Core.Kan
open import Core.Equiv
open import Core.Type
open import Core.Transport

open import Lib.Graph.Base hiding (ob)
open import Lib.Graph.Reflexive.Base

singl-contr : ∀ {u} {A : Type u} {x : A} → is-contr (Σ y ∶ A , x ≡ y)
singl-contr {x} .center = x , refl
singl-contr {x} .paths (y , q) = λ i → (q i) , λ j → q (i ∧ j)

singl-unique : ∀ {u} {A : Type u} {x : A} → is-prop (Σ y ∶ A , x ≡ y)
singl-unique {A} {x} = is-contr→is-prop singl-contr

-- record Cat u v : Type₊ (u ⊔ v) where
--   field
--     ob : Type u
--     hom :

-- Virtual double categories
record Virtual {u} (Γ : Type u) : Typeω where
  field
    l₀ l₁ l₂ : Level
    obj : Γ → Type l₀
    homt : ∀ {x y} → obj x → obj y → Type l₁ -- tight arrows
    tcut : ∀ {x y z} {a : obj x} {b : obj y} {c : obj z}
         → homt a b → homt b c → homt a c
    homl : ∀ {x} → obj x → obj x → Type l₁ -- loose arrows
    lcut : ∀ {x} {a b c : obj x} → homl a b → homl b c → homl a c
    vcell : ∀ {x y} {a b : obj x} {c d : obj y}
         → homt a c
         → homl a b
         → homt b d
         → homl c d
         → Type l₁
    -- loose morphisms are composite systems with centre at `f ; g => f ; g`
    glob-comp-unique : ∀ {x} {a b c : obj x} {f : homl a b} {g : homl b c}
                     → is-prop (Σ s ∶ homl a c , vcell {!!} (lcut f g) {!!} s)
    --ceqv : ∀ {x} {a b : obj x} {f : hom a b} → cell f f
    -- vcut : ∀ {x} {a b c : obj x} {f : hom a b} {g : hom b c}
    --      →
    -- cell-coh : ∀ {x y} {a b : obj x} {f : hom a b} {s0 s1 : obj x → obj y}
    --          → cell f s0 s1 ≡ hom (s0 a) (s1 b)
    -- cell-unique : ∀ {x y} {a b : obj x} {s0 s1 : obj x → obj y}
    --             → is-prop (Σ s ∶ hom a b , cell s s0 s1)
    -- hom-unique : ∀ {x y} {a : obj x} {s0 : obj x → obj y}
    --            → is-prop (Σ b ∶ obj y , hom (s0 a) b)
    -- cmap : ∀ {x y} {a b : obj x} {f : hom a b} {s0 s1 : obj x → obj y}
    --      → cell f s0 s1 → hom (s0 a) (s1 b)

    -- heqv : ∀ {x} {a b : obj x} {f : hom a b} → cell f id id
    -- ceqv-divl : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c} {k : hom x a c}
    --           → (α : cell ? ? ?)
    --           → is-contr (Σ β ∶ cell ? ? ? , ?)
    -- ceqv-divr : ∀ {x} {a b c : obj x} {h : hom x a c} {f : hom x a b} {g : hom x b c}
    --           → (α : hom2 x h (cut f g))
    --           → is-contr (Σ β ∶ hom2 x h (cut f g) , vcut β (ceqv {f = f} {g}) ≡ α)
    -- c-wlinear : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c} {s : hom x a c}
    --             → (α : hom2 x (cut f g) s) → vcut ceqv (vcut ceqv α) ≡ vcut ceqv α
    -- c-wthunkable : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c} {s : hom x a c}
    --             → (α : hom2 x s (cut f g)) → vcut (vcut α ceqv) ceqv ≡ vcut α ceqv



  -- target : ∀ {x y} {a b : obj x} {f : hom a b} {s0 s1 : obj x → obj y} → cell f s0 s1
  --        → hom (s0 a) (s1 b)
  -- target {f} {s0} {s1} = transport λ i → cell-coh {f = f} {s0 = s0} {s1 = s1} i

  -- wconcat : ∀ {x y} {a b c : obj x} {f : hom a b} {g : hom b c}
  --         → {s0 s1 s2 : obj x → obj y}
  --         → cell (cut f g) s0 s1 → cell s t0 t1 → cell s s0 s2
  -- wconcat {f} {g} {s0} {s1} {s2} α = transport λ i → cell {!!} {!!} s2 where
  --   l0 : {!!}
  --   l0 = cell-unique (cut f g , {!!}) (cut f g , α)

  -- cast-aut-path : ∀ {x} {a b c : obj x}
  --           → {f : hom x a b} {g : hom x b c} {s : hom x a c}
  --           → (α : hom2 (cut f g) s)
  --           → cut f g ≡ s
  -- cast-aut-path {f} {g} {s} α = ap fst (cut-unique (cut f g , ceqv) (s , α))

  -- cast-path : ∀ {x y} {a b c : obj x} {d e : obj y}
  --           → {f : hom x a b} {g : hom x b c} {s : hom y d e}
  --           → (p : x ≡ y) (q : PathP (λ i → obj (p i)) a d) (r : PathP (λ i → obj (p i)) c e)
  --           → (α : hom2 (cut f g) s)
  --           → {!!}
  -- cast-path {f = f} {g = g} {s = s} p q r α = ap fst (cut-unique ({!cut f g!} , {!!}) (s , α))
  --   where
  --     Σ-fam : I → Type _
  --     Σ-fam i = Σ t ∶ hom (p i) (q i) (r i) , hom2 (cut f g) t

  --     transported : Σ-fam i1
  --     transported = transport (λ i → Σ-fam i) (cut f g , ceqv)

  -- cast-pathp : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
  --            → (α : f ⨾ g => s)
  --            → PathP (λ i → (f ⨾ g) => cast-path α i) ceqv α
  -- cast-pathp {f} {g} {s} α = ap snd (cut-unique Γ ((f ⨾ g) , ceqv ) (s , α))

  -- based-ids : ∀ {x y z} {f : x ~> y} {g : y ~> z}
  --           → is-based-identity-system (f ⨾ g) (f ⨾ g =>_) ceqv
  -- based-ids .to-path = cast-path
  -- based-ids .to-path-over = cast-pathp

  -- hcut : ∀ {x y z} {a b c : obj x} {d e : obj y} {f g : obj z}
  --      → {x0 : hom x a b} {x1 : hom x b c} {y0 y1 : hom y d e} {σ : hom z f g}
  --      → hom2 (cut x0 x1) y0
  --      → hom2 y0 y1
  --      → hom2 (cut x0 x1) y1
  -- hcut α = transport λ i → hom2 {!!} {!y1!}

    -- we require that ceqv is unital with respect to 2-cell composites. this
    -- also entails that if 2-cells are a groupoid, and that ceqv will coincide
    -- with the canonical unit with free source and target symbols
  --   ceqv-divl : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c} {k : hom x a c}
  --             → (α : hom2 x (cut f g) k)
  --             → is-contr (Σ β ∶ hom2 x (cut f g) k , vcut (ceqv {f = f} {g}) β ≡ α)
  --   ceqv-divr : ∀ {x} {a b c : obj x} {h : hom x a c} {f : hom x a b} {g : hom x b c}
  --             → (α : hom2 x h (cut f g))
  --             → is-contr (Σ β ∶ hom2 x h (cut f g) , vcut β (ceqv {f = f} {g}) ≡ α)
  --   c-wlinear : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c} {s : hom x a c}
  --               → (α : hom2 x (cut f g) s) → vcut ceqv (vcut ceqv α) ≡ vcut ceqv α
  --   c-wthunkable : ∀ {x} {a b c : obj x} {f : hom x a b} {g : hom x b c} {s : hom x a c}
  --               → (α : hom2 x s (cut f g)) → vcut (vcut α ceqv) ceqv ≡ vcut α ceqv

  -- vcut-unique : ∀ {x} {a b : obj x} {f g h : hom x a b}
  --             → {α : hom2 x f g}
  --             → {β : hom2 x g h}
  --             → is-prop (Σ s ∶ hom2 x f h , vcut α β ≡ s)
  -- vcut-unique = singl-unique

```
module _ {u} {Γ : Type u} ⦃ V : Virtual Γ ⦄ where
  open Virtual V
  infixr -1 1cell-syntax 2cell-syntax iso-syntax term-syntax

  ob : Γ → Type l₀
  ob = obj

  term-syntax : ∀ Γ → Π ob → ob Γ
  term-syntax C b = b C
  syntax term-syntax 𝓒 (λ x → a) = x ∶ 𝓒 ⊢ a

  1cell-syntax : ∀ C → obj C → obj C → Type l₁
  1cell-syntax = hom
  syntax 1cell-syntax 𝓒 a b = a ↦ b ∶ 𝓒

  2cell-syntax : ∀ C {x y} → x ↦ y ∶ C → x ↦ y ∶ C → Type l₂
  2cell-syntax = hom2
  syntax 2cell-syntax 𝓒 f g = f ⇒ g ∶ 𝓒

  module _ Γ where
    private
      infix 6 _~>_ _=>_
      _~>_ = hom Γ
      _=>_ = hom2 Γ
      _⨾_ = cut
      _⊚_ = vcut; infixr 9 _⨾_ _⊚_
      _●_ = hcut; infixr 8 _●_

    cidem : ∀ {a b c} {f : a ~> b} {g : b ~> c} → ceqv ⊚ ceqv ≡ ceqv {f = f} {g}
    cidem {f = f} {g} = ap fst total
      where
        -- c-wlinear with α = ceqv gives: ceqv ⊚ (ceqv ⊚ ceqv) ≡ ceqv ⊚ ceqv
        is-lin : ceqv ⊚ (ceqv ⊚ ceqv) ≡ ceqv ⊚ ceqv
        is-lin = c-wlinear ceqv

        -- ceqv-divl says (Σ β , ceqv ⊚ β ≡ ceqv ⊚ ceqv) is contractible
        -- Both (ceqv ⊚ ceqv , is-lin) and (ceqv , refl) are in this type
        total : (ceqv ⊚ ceqv , is-lin) ≡ (ceqv , refl)
        total = is-contr→is-prop (ceqv-divl (ceqv ⊚ ceqv)) (ceqv ⊚ ceqv , is-lin) (ceqv , refl)

    vcut-unitl : ∀ {a b c} {f : a ~> b} {g : b ~> c} {k : a ~> c}
               → (α : f ⨾ g => k) → ceqv ⊚ α ≡ α
    vcut-unitl {f = f} {g} α = ap fst total
      where
        total : (ceqv ⊚ α , c-wlinear α) ≡ (α , refl)
        total = is-contr→is-prop (ceqv-divl (ceqv ⊚ α)) (ceqv ⊚ α , c-wlinear α) (α , refl)

    vcut-unitr : ∀ {a b c} {h : a ~> c} {f : a ~> b} {g : b ~> c}
               → (α : h => f ⨾ g) → α ⊚ ceqv ≡ α
    vcut-unitr {f = f} {g} α = ap fst total
      where
        is-thk : (α ⊚ ceqv) ⊚ ceqv ≡ α ⊚ ceqv
        is-thk = c-wthunkable α

        total : (α ⊚ ceqv , c-wthunkable α) ≡ (α , refl)
        total = is-contr→is-prop (ceqv-divr (α ⊚ ceqv)) (α ⊚ ceqv , c-wthunkable α) (α , refl)

    cast-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
              → f ⨾ g => s
              → f ⨾ g ≡ s
    cast-path {f} {g} {s} α = ap fst (cut-unique Γ ((f ⨾ g) , ceqv ) (s , α))

    cast-pathp : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
               → (α : f ⨾ g => s)
               → PathP (λ i → (f ⨾ g) => cast-path α i) ceqv α
    cast-pathp {f} {g} {s} α = ap snd (cut-unique Γ ((f ⨾ g) , ceqv ) (s , α))

    based-ids : ∀ {x y z} {f : x ~> y} {g : y ~> z}
              → is-based-identity-system (f ⨾ g) (f ⨾ g =>_) ceqv
    based-ids .to-path = cast-path
    based-ids .to-path-over = cast-pathp

    --inhab-based-ids

    cocut-unique : ∀ x {a b c : obj x} {f : hom x a b} {g : hom x b c}
                 → is-prop (Σ t ∶ hom x a c , hom2 x t (cut f g))

    cocut-unique = {!!}
    -- Based identity system for the other direction (cofan)
    cobased-ids : ∀ {x y z} {f : x ~> y} {g : y ~> z}
                → is-based-identity-system (f ⨾ g) (_=> (f ⨾ g)) ceqv
    cobased-ids .to-path α = ap fst (cocut-unique Γ (_ , ceqv) (_ , α))
    cobased-ids .to-path-over α = ap snd (cocut-unique Γ (_ , ceqv) (_ , α))

    loop : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z} → f ⨾ g => s → s => s
    loop {s} p = transport (λ i → cast-path p i => s) p

    lift-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {r s : x ~> z}
              → f ⨾ g => r → r ≡ s → r => s
    lift-path {r} {s} α q = transport (λ i → r => q i) (loop α)

    comp-unique : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
                → f ⨾ g => s → f ⨾ g => s' → s ≡ s'
    comp-unique α β = sym (cast-path α) ∙ cast-path β

    loop-contr : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z} (α : f ⨾ g => s)
               → is-contr (Σ s' ∶ (x ~> z) , Σ β ∶ f ⨾ g => s' , PathP (λ i → f ⨾ g => comp-unique α β i) α β)
    loop-contr {f = f} {(g)} {(s)} α .center = s , α , loop-over (f ⨾ g =>_) (cast-path α) α
    loop-contr {f = f} {(g)} {(s)} α .paths (s' , β , H) i = a0 i , a1 i , a2
      where
      a0 : s ≡ s'
      a0 = comp-unique α β

      a1 : PathP (λ i → f ⨾ g => a0 i) α β
      a1 = H

      a2 : PathP (λ j → f ⨾ g => comp-unique α (a1 i) j) α (a1 i)
      a2 j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → loop-over (f ⨾ g =>_) (cast-path α) α j
        k (i = i1) → H j
        k (j = i0) → α
        k (j = i1) → H i
        k (k = i0) → transport (λ k → (f ⨾ g) => {!? ∙ ?!}) {!!} -- (loop-over (f ⨾ g =>_) (cast-path α) α j)
          where
          c = sym (cast-path α) ∙ cast-path α
          -- path :
          -- path = {!!}
          k : {!!} ≡ {!!}
          k = {!!}

      -- t0 : cut f g , ceqv ≡ s , α
      -- t0 = cut-unique Γ (f ⨾ g , ceqv) (s , α)

      -- t1 : cut f g , ceqv ≡ s' , β
      -- t1 = cut-unique Γ (f ⨾ g , ceqv) (s' , β)

      -- p0 : s ≡ s
      -- p0 = sym (ap fst t0) ∙ ap fst t0

      -- p1 : s' ≡ s'
      -- p1 = sym (ap fst t1) ∙ ap fst t1

      -- c : (i : I) → PathP (λ j → f ⨾ g => comp-unique α (σ i) j) α (transport (λ j → f ⨾ g => cat.invl (ap fst t0) (~ j) {!~ i!}) α)
      -- c i = transport-filler (λ j → f ⨾ g => comp-unique α (σ i) j) α

      -- h0 : transport (λ i → (f ⨾ g) => p0 i) α , transport-filler (λ i → f ⨾ g => p0 i) α
      --    ≡ α , loop-over (f ⨾ g =>_) (cast-path α) α
      -- h0 = SinglP-contr α .paths (α , loop-over (f ⨾ g =>_) (cast-path α) α)

      -- h1 : transport (λ i → (f ⨾ g) => p1 i) β , transport-filler (λ i → f ⨾ g => p1 i) β
      --    ≡ β , loop-over (f ⨾ g =>_) (cast-path β) β
      -- h1 = SinglP-contr β .paths (β , loop-over (f ⨾ g =>_) (cast-path β) β)

    -- over the composite space we have the embedding of a core groupoid which
    -- can be displayed from the ambient identity type
    csym : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z} → f ⨾ g => s → s => f ⨾ g
    csym {s} α = transport (λ i → hom2 Γ s (cast-path α (~ i))) (loop α)

    cconcat : ∀ {w x y z} {f : w ~> x} {f' : x ~> z} {g : w ~> y} {g' : y ~> z} {s : w ~> z}
                 → f ⨾ f' => g ⨾ g' → g ⨾ g' => s → f ⨾ f' => s
    cconcat {f} {f'} α β = transport (λ i → hom2 Γ (cut f f') (cast-path β i)) α

    wconcat : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
            → f ⨾ g => s → s => s' → f ⨾ g => s'
    wconcat {s'} α = transport (λ i → cast-path α (~ i) => s')

    module cconcat {w x y z} {f : w ~> x} {g : x ~> y} {h : y ~> z} where
      lwhisk :  {s : w ~> y} → f ⨾ g => s → (f ⨾ g) ⨾ h => s ⨾ h
      lwhisk H = transport (λ i → (f ⨾ g) ⨾ h => cast-path H i ⨾ h) ceqv

      lwhisk-op : {s : w ~> y} → f ⨾ g => s → s ⨾ h => (f ⨾ g) ⨾ h
      lwhisk-op H = transport (λ i → cast-path H i ⨾ h => (f ⨾ g) ⨾ h) ceqv

      -- Abstract right overlap on target bracket
      rwhisk :  {r : x ~> z} → g ⨾ h => r → f ⨾ (g ⨾ h) => f ⨾ r
      rwhisk K = transport (λ i → f ⨾ (g ⨾ h) => f ⨾ cast-path K i) ceqv

      rwhisk-op : {r : x ~> z} → g ⨾ h => r → f ⨾ r => f ⨾ (g ⨾ h)
      rwhisk-op K = transport (λ i → f ⨾ cast-path K i => f ⨾ (g ⨾ h)) ceqv

      conj : {s : w ~> y} {r : x ~> z} → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h) → f ⨾ g => s → g ⨾ h => r → s ⨾ h => f ⨾ r
      conj A H K = transport (λ i → cast-path H i ⨾ h => f ⨾ cast-path K i) A -- (cast-path H) (cast-path K)

      lcross : {s : w ~> y} → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h) → f ⨾ g => s → s ⨾ h => f ⨾ (g ⨾ h)
      lcross A H = transport (λ i → cast-path H i ⨾ h => f ⨾ (g ⨾ h)) A
      --subst (λ u → u ⨾ h => f ⨾ (g ⨾ h)) (cast-path H) A

      -- Keep left concrete, abstract right
      rcross : {r : x ~> z} → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h) → g ⨾ h => r → (f ⨾ g) ⨾ h => f ⨾ r
      rcross A K = transport (λ i → (f ⨾ g) ⨾ h => (f ⨾ cast-path K i)) A

    -- right factor with respect to canonical composite structure
    fibroid : ∀ {x y z} → x ~> y → x ~> z → Type (l₁ ⊔ l₂)
    fibroid {y} {z} f s = Σ k ∶ y ~> z , f ⨾ k => s

    2-fibroid : ∀ {x y} {f g s : x ~> y} → f => g → f => s → Type _
    2-fibroid {g} {s} α β = Σ φ ∶ g => s , α ⊚ φ ≡ β

    -- left factor with respect to canonical composite structure
    cofibroid : ∀ {w x y} → x ~> y → w ~> y → Type (l₁ ⊔ l₂)
    cofibroid {w} {x} f s = Σ h ∶ w ~> x , h ⨾ f => s

    2-cofibroid : ∀ {x y} {f g s : x ~> y} → g => s → f => s → Type _
    2-cofibroid {f} {g} α β = Σ φ ∶ f => g , φ ⊚ α ≡ β

    right-divisible : ∀ {x y z} → x ~> y → x ~> z → Type (l₁ ⊔ l₂)
    right-divisible {x} {y} {z} f s = is-contr (fibroid f s)

    left-divisible : ∀ {w x y} → x ~> y → w ~> y → Type (l₁ ⊔ l₂)
    left-divisible {w} {x} {y} f s = is-contr (cofibroid f s)

    record is-isomorphism {x y} (f : x ~> y) : Type (l₀ ⊔ l₁ ⊔ l₂) where
      no-eta-equality
      field
        divl : ∀ {w} (s : w ~> y) → left-divisible f s
        divr : ∀ {z} (s : x ~> z) → right-divisible f s

    record is-homotopy {x y} {s r : x ~> y} (H : s => r) : Type (l₂ ⊔ l₁) where
      field
        divl : ∀ {k} (S : s => k) → is-contr (Σ G ∶ r => k , H ⊚ G ≡ S)
        divr : ∀ {h} (S : h => r) → is-contr (Σ F ∶ h => s , F ⊚ H ≡ S)

    is-0-coherent : ∀ {x y} → {c d : x ~> y} → c => d → Type (l₁ ⊔ l₂)
    is-0-coherent {x} {y} {c} {d} α =
      is-prop (Σ β ∶ c => d , Path (Σ s ∶ (x ~> y) , c => s) (d , α) (d , β))


-- is-prop (Σ G ∶ c => d , (d , F) ≡ (d , G))
    is-isomorphism-is-prop : ∀ {x y} (q : x ~> y) → is-prop (is-isomorphism q)
    is-isomorphism-is-prop q x y i .is-isomorphism.divl s = is-contr-is-prop (cofibroid q s) (x .is-isomorphism.divl s) (y .is-isomorphism.divl s) i
    is-isomorphism-is-prop q x y i .is-isomorphism.divr s = is-contr-is-prop (fibroid q s) (x .is-isomorphism.divr s) (y .is-isomorphism.divr s) i

    is-homotopy-is-prop : ∀ {x y} {s r : x ~> y} (H : s => r) → is-prop (is-homotopy H)
    is-homotopy-is-prop H x y i .is-homotopy.divl s = is-contr-is-prop _ (x .is-homotopy.divl s) (y .is-homotopy.divl s) i
    is-homotopy-is-prop H x y i .is-homotopy.divr s = is-contr-is-prop _ (x .is-homotopy.divr s) (y .is-homotopy.divr s) i

    cut-contr : ∀ {a b c} {f : a ~> b} {g : b ~> c}
              → is-contr (Σ s ∶ a ~> c , (f ⨾ g) => s)
    cut-contr {f = f} {g} = prop-inhabited→is-contr
                             (cut-unique Γ)
                             (f ⨾ g , ceqv)

    cocut-contr : ∀ {a b c} {f : a ~> b} {g : b ~> c}
                → is-contr (Σ t ∶ a ~> c , t => (f ⨾ g))
    cocut-contr {f = f} {g} = prop-inhabited→is-contr
                               (cocut-unique Γ)
                               (f ⨾ g , ceqv)

    divr→lcancel : ∀ {x y z} {f : x ~> y} {k₁ k₂ : y ~> z}
                 → (∀ s → is-contr (fibroid f s))  -- f is right-divisible
                 → f ⨾ k₁ => f ⨾ k₂
                 → k₁ ≡ k₂
    divr→lcancel {f = f} {k₁} {k₂} f-div σ =
      let
        c = f-div (cut f k₂)

        path : (k₁ , σ) ≡ (k₂ , ceqv)
        path = is-contr→is-prop c _ _
      in
         ap fst path

    homotopy→lcancel : ∀ {x y} {s r k : x ~> y}
                    → {H : s => r} {G₁ G₂ : r => k}
                    → is-homotopy H
                    → H ⊚ G₁ ≡ H ⊚ G₂
                    → G₁ ≡ G₂
    homotopy→lcancel {H} {G₁} {G₂} H-htpy p =
      let
        c = H-htpy .is-homotopy.divl (H ⊚ G₂)
        path : (G₁ , p) ≡ (G₂ , refl)
        path = is-contr→is-prop c _ _
      in
        ap fst path

    divl→rcancel : ∀ {w x y} {g : x ~> y} {h₁ h₂ : w ~> x}
                 → (∀ s → left-divisible g s)  -- g is left-divisible
                 → h₁ ⨾ g => h₂ ⨾ g
                 → h₁ ≡ h₂
    divl→rcancel {g = g} {h₁} {h₂} g-div σ =
      let
        c = g-div (cut h₂ g)
        path : (h₁ , σ) ≡ (h₂ , ceqv)
        path = is-contr→is-prop c _ _
      in
       ap fst path

    homotopy→rcancel : ∀ {x y} {h s r : x ~> y}
                   → {H : s => r} {F₁ F₂ : h => s}
                   → is-homotopy H
                   → F₁ ⊚ H ≡ F₂ ⊚ H
                   → F₁ ≡ F₂
    homotopy→rcancel {H = H} {F₁} {F₂} H-htpy p =
      let
        c = H-htpy .is-homotopy.divr (F₂ ⊚ H)
        path : (F₁ , p) ≡ (F₂ , refl)
        path = is-contr→is-prop c _ _
      in
        ap fst path

    iso→lcancel : ∀ {x y z} {f : x ~> y} {k₁ k₂ : y ~> z}
                → is-isomorphism f
                → f ⨾ k₁ => f ⨾ k₂
                → k₁ ≡ k₂
    iso→lcancel f-iso = divr→lcancel (λ s → f-iso .is-isomorphism.divr s)

    cancel-iso-left : ∀ {w x y} {g : x ~> y} {h₁ h₂ : w ~> x}
                    → is-isomorphism g
                    → h₁ ⨾ g => h₂ ⨾ g
                    → h₁ ≡ h₂
    cancel-iso-left g-iso = divl→rcancel (λ s → g-iso .is-isomorphism.divl s)

    idem-assoc-unique : ∀ {x} (q q' : x ~> x)
                      → (cq : is-isomorphism q) (cq' : is-isomorphism q')
                      → (idem-q : q ⨾ q => q)
                      → (let c = cq' .is-isomorphism.divl q .center .fst)
                      → ((c ⨾ q') ⨾ q') => (c ⨾ q')
                      → q ≡ q'
    idem-assoc-unique {x} q q' cq cq' idem-q thk = ap fst (prop (q , idem-q) (q' , qq'=>q))
      where
        module cq' = is-isomorphism cq'
        prop = is-contr→is-prop (cq .is-isomorphism.divr q)

        c : x ~> x
        c = cq'.divl q .center .fst

        cq'=>q : c ⨾ q' => q
        cq'=>q = cq'.divl q .center .snd

        qq'=>q : q ⨾ q' => q
        qq'=>q = cconcat (cconcat.lwhisk-op cq'=>q) (cconcat thk cq'=>q)

    ceqv-homotopy : ∀ {x y z} {f : x ~> y} {g : y ~> z} → is-homotopy (ceqv {f = f} {g})
    ceqv-homotopy .is-homotopy.divl = ceqv-divl
    ceqv-homotopy .is-homotopy.divr = ceqv-divr

    private module _ {a b c} {f : a ~> b} {g : b ~> c} {s : a ~> c} (α : f ⨾ g => s) where
      rx : s => s
      rx = loop α

      composite-ids : is-based-identity-system s (s =>_) rx
      composite-ids .to-path {b = c} H = ap fst total-cut
        where
        total-cut : s , α ≡ c , wconcat α H
        total-cut = cut-unique Γ (s , α) (c , wconcat α H)
      composite-ids .to-path-over {b = c} H = β where
        path : s ≡ c
        path = transport (λ i → cast-path α i ≡ c) (cast-path (wconcat α H))

        total-cut : s , α ≡ c , wconcat α H
        total-cut = cut-unique Γ (s , α) (c , wconcat α H)

        β : PathP (λ i → s => ap fst total-cut i) rx H
        β i = hcomp (∂ i) λ where
          k (i = i0) → rx
          k (i = i1) → transport⁻-transport (λ j → hom2 Γ (cast-path α j) c) H k
          k (k = i0) → transport (λ j → hom2 Γ (cast-path α j) (ap fst total-cut i)) (ap snd total-cut i)

      module Ids = is-based-identity-system composite-ids


    record _~''_ {x y} (c d : x ~> y) : Type (l₁ ⊔ l₂) where
      field
        F : c => d
        F-htpy : is-homotopy F
        fan-contr : is-contr (Σ s ∶ x ~> y , c => s)
      open is-homotopy
      -- Derived reflexivity at d (from F-htpy)
      eqv : d => d
      eqv = F-htpy .divl F .center .fst

      -- Derived reflexivity at c (from F-htpy)
      c-refl : c => c
      c-refl = F-htpy .divr F .center .fst

    record _~_ {x y} (c d : x ~> y) : Type (l₁ ⊔ l₂) where
      field
        F : c => d
        F-htpy : is-homotopy F
        F-total : is-prop (Σ s ∶ x ~> y , c => s)
        L-fiber : is-0-coherent F

      unique : (G : c => d) → F ≡ G
      unique G = ap fst (L-fiber (F , refl) (G , F-total _ _))

      eqv : d => d
      eqv = F-htpy .is-homotopy.divl F .center .fst

    ~-is-prop : ∀ {x y} {c d : x ~> y} → is-prop (c ~ d)
    ~-is-prop {c} {d} r₁ r₂ = goal where
      module r₁ = _~_ r₁
      module r₂ = _~_ r₂

      F-path : r₁.F ≡ r₂.F
      F-path = r₁.unique r₂.F

      F-total-path : PathP (λ i → is-prop (Σ s ∶ _ ~> _ , c => s)) r₁.F-total r₂.F-total
      F-total-path = is-prop→PathP (λ i → is-prop-is-prop (Σ (hom2 Γ c))) r₁.F-total r₂.F-total

      F-htpy-path : PathP (λ i → is-homotopy (F-path i)) r₁.F-htpy r₂.F-htpy
      F-htpy-path = is-prop→PathP (λ i → is-homotopy-is-prop (F-path i)) r₁.F-htpy r₂.F-htpy

      L-fiber-path : PathP (λ i → is-prop (Σ G ∶ c => d , (d , F-path i) ≡ (d , G)))
                              r₁.L-fiber r₂.L-fiber
      L-fiber-path = is-prop→PathP (λ i → is-prop-is-prop _) r₁.L-fiber r₂.L-fiber

      goal : r₁ ≡ r₂
      goal i ._~_.F = F-path i
      goal i ._~_.F-total = F-total-path i
      goal i ._~_.F-htpy = F-htpy-path i
      goal i ._~_.L-fiber = L-fiber-path i

    ~-refl : ∀ {x y z} {f : x ~> y} {g : y ~> z} → (f ⨾ g) ~ (f ⨾ g)
    ~-refl ._~_.F = ceqv
    ~-refl ._~_.F-total = cut-unique Γ
    ~-refl ._~_.F-htpy = ceqv-homotopy
    ~-refl {f} {g} ._~_.L-fiber (s0 , α) (s1 , β) i =
      φ i , set (f ⨾ g , ceqv) (f ⨾ g , (φ i)) (λ j → f ⨾ g , w0 i .snd) (ψ i) i where
        set : is-set (Σ λ s → (f ⨾ g) => s)
        set = is-prop→is-set (cut-unique Γ)

        c0 = ceqv-divl s0 .center
        c1 = ceqv-divl s1 .center
        d0 = ceqv-divr s0 .center
        d1 = ceqv-divr s1 .center
        a0 = c0 .fst
        a1 = c1 .fst
        b0 = d0 .fst
        b1 = d1 .fst

        σ0 : vcut ceqv a0 ≡ s0
        σ0 = ceqv-divl s0 .center .snd

        σ1 : vcut (ceqv-divr s1 .center .fst) ceqv ≡ s1
        σ1 = ceqv-divr s1 .center .snd

        f0 : (σ : {!!}) → ceqv-divl s1 .center ≡ σ
        f0 = ceqv-divl s1 .paths

        φ : s0 ≡ s1
        φ i = Singl-unique (s0 , σ0) (s1 , {!!}) i .fst

        w0 : f ⨾ g , ceqv ≡ f ⨾ g , s0
        w0 = {!!}

        w1 : f ⨾ g , ceqv ≡ f ⨾ g , s1
        w1 = {!!}

        ψ : PathP (λ i → (f ⨾ g , ceqv ≡ f ⨾ g , φ i)) w0 w1
        ψ = {!!}

    ~-identity-system : ∀ {x y z} {f : x ~> y} {g : y ~> z} {c : x ~> z}
                      → (α : f ⨾ g => c) → is-contr (Σ d ∶ x ~> z , d ~ c)
    ~-identity-system {f = f} {g} {c} α .center = f ⨾ g , {!!}
    ~-identity-system {c = c} α .paths (d , r) = {!!} where
      -- r : c ~ d gives us r.F : c => d
      -- composite-ids α gives us the identity system
      module r = _~_ r
      base-path : c ≡ d
      base-path = composite-ids α .to-path {!!}

      -- -- ~-is-prop handles the fiber
      -- fiber-path : PathP (λ i → c ~ base-path i) ? ?
      -- fiber-path = ?

      -- goal : (c , ?) ≡ (d , ?)
      -- goal i = base-path i , fiber-path i

    -- ~-sym : ∀ {x y} {c d : x ~> y} → c ~ d → d ~ c
    -- ~-sym {c = c} {d} r ._~_.F = F⁻¹
    --   where
    --     -- r.F-htpy gives us division, hence an inverse
    --     F⁻¹ : d => c
    --     F⁻¹ = ? --r ._~_.F-htpy .is-homotopy.divr ? ._~_.F .center .fst

    -- ~-sym {d = d} r ._~_.F-total = R→total r ._~_.R
    --   where
    --     -- r.R : is-contr (Σ s, d => s)
    --     -- Convert to is-prop
    --     R→total : is-contr (Σ s ∶ ? , d => s) → is-prop (Σ s ∶ ? , d => s)
    --     R→total = is-contr→is-prop

    -- ~-sym r {c = c} {d} ._~_.F-htpy = F⁻¹-is-homotopy
    --   where
    --     F⁻¹ : d => c
    --     F⁻¹ = r ._~_.F-htpy .is-homotopy.divr r ._~_.F .center .fst
    --     -- The inverse of a homotopy is a homotopy
    --     F⁻¹-is-homotopy : is-homotopy F⁻¹
    --     F⁻¹-is-homotopy .is-homotopy.divl = ?
    --     F⁻¹-is-homotopy .is-homotopy.divr = ?

    -- ~-sym r ._~_.L-fiber = ?

    record is-idem-equiv {x} (i : x ~> x) : Type (l₀ ⊔ l₁ ⊔ l₂) where
      field
        divl : ∀ {w} (s : w ~> x) → left-divisible i s
        divr : ∀ {y} (s : x ~> y) → right-divisible i s
        idem : i ⨾ i => i

    is-idem-equiv-is-prop : ∀ {x} {i : x ~> x} → is-prop (is-idem-equiv i)
    is-idem-equiv-is-prop = {!!}

    record _~'_ {x y} (c d : x ~> y) : Type (l₀ ⊔ l₁ ⊔ l₂) where
      field
        arc : y ~> y
        idem-eqv : is-idem-equiv arc
        arc-wthunk : ∀ {w} (f : w ~> y) → (f ⨾ arc) ⨾ arc => f ⨾ arc -- weakly thunkable

        composite : c ⨾ arc => d
        is-htpy : is-homotopy composite
        unique-fiber : is-prop (Σ G ∶ c ⨾ arc => d , (d , composite) ≡ (d , G))


      unique-fiber-derived : is-prop (Σ G ∶ c ⨾ arc => d , (d , composite) ≡ (d , G))
      unique-fiber-derived (G₁ , p₁) (G₂ , p₂) i = {!ap snd (p-path i) i!} , {!!}
        where
          G-path : G₁ ≡ G₂
          G-path = {!!}

          p-path : PathP (λ i → (d , composite) ≡ (d , G-path i)) p₁ p₂
          p-path = is-prop→PathP (λ i → is-prop→is-set (cut-unique Γ) _ _) p₁ p₂

          prop : (α : hom2 Γ (cut c arc) d) → is-prop (d , composite ≡ d , α)
          prop α f0 f1 = {!!}

      arc-idem : arc ⨾ arc => arc
      arc-idem = {!!}

      arc-is-prop : is-prop (c ⨾ arc => d)
      arc-is-prop α β = ap fst (unique-fiber
        (α , cut-unique Γ (d , composite) (d , α))
        (β , cut-unique Γ (d , composite) (d , β)))

      arc-neutral : c ⨾ arc ≡ c
      arc-neutral = ap fst (is-contr→is-prop (idem-eqv .is-idem-equiv.divl (c ⨾ arc))
          (c ⨾ arc , arc-wthunk c)
          (c , ceqv))

      F-total : is-prop (Σ s ∶ x ~> y , c ⨾ arc => s)
      F-total = cut-unique Γ

      composite-unique : is-prop (c => d)
      composite-unique = transport (λ i → is-prop (arc-neutral i => d)) arc-is-prop

      canonical-fiber : is-prop (Σ s ∶ x ~> y , c => s)
      canonical-fiber = transport (λ i → is-prop (Σ s ∶ x ~> y , (arc-neutral i => s))) F-total

      F-contr : is-contr (Σ s ∶ x ~> y , c ⨾ arc => s)
      F-contr = prop-inhabited→is-contr F-total (c ⨾ arc , ceqv)

      unique : (G : c ⨾ arc => d) → composite ≡ G
      unique G = ap fst (unique-fiber (composite , refl) (G , F-total _ _))

      composite-contr : is-contr (c ⨾ arc => d)
      composite-contr .center = composite
      composite-contr .paths = unique



    -- associator data in a category
    -- field
    --   assoc : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z) → (f ⨾ g) ⨾ h ~ f ⨾ (g ⨾ h)

    -- Uniqueness of inverses (follows from cancellation) [this will go into the groupoid 2-cell case, although I believe
    -- a sym operation derived for local composite structure will also work]
    -- inverse-unique-right : ∀ {x y} {f : x ~> y} {g₁ g₂ : y ~> x}
    --                      → is-isomorphism f
    --                      → (f ⨾ g₁ => f)  -- g₁ is a right inverse
    --                      → (f ⨾ g₂ => f)  -- g₂ is a right inverse
    --                      → g₁ ≡ g₂
    -- inverse-unique-right f-iso σ₁ σ₂ =
    --   iso→lcancel f-iso (σ₁ ⊚ inv-2cell σ₂)
    --   -- where inv-2cell needs to be constructed from your 2-cell structure

    -- inverse-unique-left : ∀ {x y} {f : x ~> y} {h₁ h₂ : y ~> x}
    --                     → is-isomorphism f
    --                     → (h₁ ⨾ f => f)  -- h₁ is a left inverse
    --                     → (h₂ ⨾ f => f)  -- h₂ is a left inverse
    --                     → h₁ ≡ h₂
    -- inverse-unique-left f-iso σ₁ σ₂ =
    --   cancel-iso-left f-iso (σ₁ ⊚ inv-2cell σ₂)

  Iso : ∀ C → obj C → obj C → Type (l₀ ⊔ l₁ ⊔ l₂)
  Iso C x y = Σ f ∶ (x ↦ y ∶ C) , is-isomorphism C f

  iso-syntax : ∀ C → obj C → obj C → Type (l₀ ⊔ l₁ ⊔ l₂)
  iso-syntax = Iso
  syntax iso-syntax C x y = x ≅ y ∶ C

module _ {u v} {Γ : Type u} {Δ : Type v} ⦃ U : Virtual Γ ⦄ ⦃ V : Virtual Δ ⦄ {C : Γ} {D : Δ} where
  private
    module Γ = Virtual U
    module Δ = Virtual V

    l₀ = Γ.l₀ ⊔ Δ.l₀
    l₁ = Γ.l₁ ⊔ Δ.l₁
    l₂ = Γ.l₂ ⊔ Δ.l₂

    o : Γ × Δ → Type l₀
    o = λ (C , D) → Γ.obj C × Δ.obj D

    hom : ((C , D) : Γ × Δ) → o (C , D) → o (C , D) → Type l₁
    hom = λ (C , D) (x , a) (y , b) → Γ.hom C x y × Δ.hom D a b

    hom2 : ∀ z {a b : o z} → hom z a b → hom z a b → Type l₂
    hom2 = λ (C , D) (f , h) (g , k) → Γ.hom2 C f g × Δ.hom2 D h k

    cut : ∀ {z} {a b c : o z} → hom z a b → hom z b c → hom z a c
    cut z z₁ = Γ.cut (z .fst) (z₁ .fst) , Δ.cut (z .snd) (z₁ .snd)

    vcut : ∀ {z} {a b : o z} {f g h : hom z a b}
         → hom2 z f g → hom2 z g h → hom2 z f h
    vcut = λ z z₁ → Γ.vcut (z .fst) (z₁ .fst) , Δ.vcut (z .snd) (z₁ .snd)

    ceqv : {z : Γ × Δ} {a b c : o z} {f : hom z a b} {g : hom z b c}
         → hom2 z (cut f g) (cut f g)
    ceqv {z = C , D} = Γ.ceqv , Δ.ceqv

    hcut : ∀ {z} {a b c : o z} {e1 d1 : hom z a b} {e2 d2 : hom z b c}
         → hom2 z e1 d1 → hom2 z e2 d2 → hom2 z (cut e1 e2) (cut d1 d2)
    hcut (α , α') (β , β') = Γ.hcut α β , Δ.hcut α' β'

    cut-unique : ∀ z {a b c : o z} {f : hom z a b} {g : hom z b c}
                 → is-prop (Σ (hom2 z (cut f g)))
    cut-unique z = is-prop-equiv Σ-×-swap (is-prop-× (Γ.cut-unique (z .fst)) (Δ.cut-unique (z .snd)))

    ceqv-divl : {z : Γ × Δ} {a b c : o z} {f : hom z a b} {g : hom z b c} {s : hom z a c}
              → (α : hom2 z (cut f g) s) → is-contr (Σ β ∶ hom2 z (cut f g) s , vcut ceqv β ≡ α)
    ceqv-divl {z = C , D} {s = s , s'} (α , β) =
      is-contr-equiv Σ-fiber-swap (is-contr-× (Γ.ceqv-divl α) (Δ.ceqv-divl β))

    ceqv-divr : {z : Γ × Δ} {a b c : o z} {f : hom z a b} {g : hom z b c} {s : hom z a c}
              → (α : hom2 z s (cut f g)) → is-contr (Σ β ∶ hom2 z s (cut f g) , vcut β ceqv ≡ α)
    ceqv-divr {z = C , D} {s = s , s'} (α , β) =
      is-contr-equiv Σ-fiber-swap (is-contr-× (Γ.ceqv-divr α) (Δ.ceqv-divr β))

    c-wlinear : {z : Γ × Δ} {a b c : o z} {f : hom z a b} {g : hom z b c} {s : hom z a c}
                → (α : hom2 z (cut f g) s) → vcut ceqv (vcut ceqv α) ≡ vcut ceqv α
    c-wlinear {z = C , D} {f = f} {g} {s} (α , β) = λ i → Γ.c-wlinear α i , Δ.c-wlinear β i

    c-wthunkable : {z : Γ × Δ} {a b c : o z} {f : hom z a b} {g : hom z b c} {s : hom z a c}
                   → (α : hom2 z s (cut f g)) → vcut (vcut α ceqv) ceqv ≡ vcut α ceqv
    c-wthunkable {z = C , D} (α , β) = λ i → Γ.c-wthunkable α i , Δ.c-wthunkable β i

  instance
    Virtual-Product : Virtual (Γ × Δ)
    Virtual-Product .Virtual.l₀ = l₀
    Virtual-Product .Virtual.l₁ = l₁
    Virtual-Product .Virtual.l₂ = l₂
    Virtual-Product .Virtual.obj = o
    Virtual-Product .Virtual.hom = hom
    Virtual-Product .Virtual.hom2 = hom2
    Virtual-Product .Virtual.cut = cut
    Virtual-Product .Virtual.cut-unique = cut-unique
    Virtual-Product .Virtual.ceqv = ceqv
    Virtual-Product .Virtual.vcut = vcut
    Virtual-Product .Virtual.ceqv-divl = ceqv-divl
    Virtual-Product .Virtual.ceqv-divr = ceqv-divr
    Virtual-Product .Virtual.hcut = hcut
    Virtual-Product .Virtual.c-wlinear = c-wlinear
    Virtual-Product .Virtual.c-wthunkable  = c-wthunkable

module _ {u v} {Γ : Type u} {Δ : Type v} ⦃ U : Virtual Γ ⦄ ⦃ V : Virtual Δ ⦄ where
  private
    module Γ = Virtual U
    module Δ = Virtual V
  record Functor (C : Γ) (D : Δ) : Type (Γ.l₀ ⊔ Γ.l₁ ⊔ Γ.l₂ ⊔ Δ.l₀ ⊔ Δ.l₁ ⊔ Δ.l₂) where
    field
      F₀ : Γ.obj C → Δ.obj D
      F₁ : ∀ {x y} → Γ.hom C x y → Δ.hom D (F₀ x) (F₀ y)

      F-comp : ∀ {x y z} (f : Γ.hom C x y) (g : Γ.hom C y z)
            → Δ.hom2 D (F₁ (Γ.cut f g)) (Δ.cut (F₁ f) (F₁ g))

      F-iso : ∀ {x y} (f : Γ.hom C x y) → is-isomorphism C f → is-isomorphism D (F₁ f)

-- we have to wait for our defs when we're in a category
-- module Slice {u} {Γ : Type u} ⦃ U : Virtual Γ ⦄ (C : Γ) (X : Virtual.obj U C) where
--   private
--     module V = Virtual U
--     _~>_ = V.hom C
--     _=>_ = V.hom2 C; infix 6 _~>_ _=>_
--     _⨾_ = V.cut; infixr 9 _⨾_

--   instance
--     Virtual-Slice : Virtual ⊤
--     Virtual-Slice .Virtual.l₀ = V.l₀ ⊔ V.l₁
--     Virtual-Slice .Virtual.l₁ = V.l₁ ⊔ V.l₂
--     Virtual-Slice .Virtual.l₂ = V.l₂
--     Virtual-Slice .Virtual.obj _ = Σ A ∶ V.obj C , A ~> X
--     Virtual-Slice .Virtual.hom _ (A , f) (B , g) = Σ h ∶ A ~> B , h ⨾ g => f
--     Virtual-Slice .Virtual.hom2 _ (h , _) (k , _) = h => k
--     Virtual-Slice .Virtual.cut (h , α) (k , β) =
--       h ⨾ k , V.vcut (V.assoc h k _) (V.hcut (V.ceqv h k) β) α
--     Virtual-Slice .Virtual.ceqv (h , _) (k , _) = V.ceqv h k
--     Virtual-Slice .Virtual.cut-unique _ = V.cut-unique C
--     Virtual-Slice .Virtual.vcut α β = V.vcut α β
--     Virtual-Slice .Virtual.hcut α β = V.hcut α β

module _ {u v} {Γ : Type u} {Δ : Type v} ⦃ U : Virtual Γ ⦄ ⦃ V : Virtual Δ ⦄ where
  private
    module Γ = Virtual U
    module Δ = Virtual V

  record NatTrans {C : Γ} {D : Δ} (F G : Functor C D) : Type (Γ.l₀ ⊔ Γ.l₁ ⊔ Δ.l₁ ⊔ Δ.l₂) where
    private
      module F = Functor F
      module G = Functor G
      _~>_ = Δ.hom D
      _=>_ = Δ.hom2 D; infix 6 _~>_ _=>_
      _⨾_ = Δ.cut; infixr 9 _⨾_

    field
      η : ∀ A → F.F₀ A ~> G.F₀ A
      natural : ∀ {A B} (f : Γ.hom C A B)
              → F.F₁ f ⨾ η B => η A ⨾ G.F₁ f

  -- 2-cells between natural transformations
  NatTrans2 : ∀ {C D} {F G : Functor C D} → NatTrans F G → NatTrans F G → Type (Γ.l₀ ⊔ Δ.l₂)
  NatTrans2 {D = D} α β = ∀ A → Δ.hom2 D (NatTrans.η α A) (NatTrans.η β A)

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

record deductive-system {u} v (Γ : Type u) : Type (u ⊔ v ₊) where
  infix 6 _~>_
  field
    _~>_ : Γ → Γ → Type v
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
    eqv-thunkable : ∀ {x y : Γ} (f : x ~> y) → (f ⨾ eqv) ⨾ eqv ≡ f ⨾ eqv

  hconcat : ∀ {x y z} {e1 d1 : x ~> y} {e2 d2 : y ~> z}
          → e1 ≡ d1 → e2 ≡ d2 → concat e1 e2 ≡ concat d1 d2
  hconcat α β i = concat (α i) (β i)

    -- Contractible fibers from is-equiv
  divr-contr : ∀ {x y} (s : x ~> y) → is-contr (Σ h ∶ x ~> y , eqv ⨾ h ≡ s)
  divr-contr s = eqv-iso .snd .eqv-fibers s

  divl-contr : ∀ {x y} (s : x ~> y) → is-contr (Σ k ∶ x ~> y , k ⨾ eqv ≡ s)
  divl-contr s = eqv-iso .fst .eqv-fibers s

  unitl : ∀ {x y : Γ} (f : x ~> y) → eqv ⨾ f ≡ f
  unitl {x = x} f = ap fst total
    module unitl where
      lin : eqv ⨾ (eqv ⨾ f) ≡ eqv ⨾ f
      lin = eqv-linear f

      total = is-contr→is-prop (divr-contr (eqv ⨾ f)) (eqv ⨾ f , lin) (f , refl)

      htpy : PathP (λ i → eqv ⨾ ap fst total i ≡ eqv ⨾ f) lin refl
      htpy = ap snd total

  unitr : ∀ {x y : Γ} (f : x ~> y) → f ⨾ eqv ≡ f
  unitr {y = y} f = transport (λ i → ap fst total (~ i) ≡ f) (sym (ap fst total) ∙ ap fst total)
    module unitr where
      thk : (f ⨾ eqv) ⨾ eqv ≡ f ⨾ eqv
      thk = eqv-thunkable f

      total = is-contr→is-prop (divl-contr (f ⨾ eqv)) (f ⨾ eqv , thk) (f , refl)

      htpy : PathP (λ i → ap fst total i ⨾ eqv ≡ f ⨾ eqv) thk refl
      htpy = ap snd total

  idem : ∀ {x} → eqv ⨾ eqv ≡ eqv {x = x}
  idem = unitl eqv

```
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

