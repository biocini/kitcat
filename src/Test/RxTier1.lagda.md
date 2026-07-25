Placement certificate: the reflexive-graph structure layer sits
strictly below `Core.Kan`.

Imports are limited to `Core.Type`, `Core.Base`, `Core.Data.Sigma` —
the three modules `Core.Kan` itself sits on — so anything that
typechecks here can be imported by `Core.Kan` without a cycle. The
declarations are transcribed rather than imported, since the live
suite currently sits above `Core.Kan` and importing it would defeat
the measurement.

What fits: the two records, the fan and cofan with their centres, the
univalence conditions, the displayed operations, both fibration
conditions, `to-id`, and the product/cotensor/comprehension/discrete/
codiscrete constructions. What does not, and is therefore absent:
`to-edge` and `coproduct` (need `transport`), `tensor` (needs
`coproduct`), `concat`/`inv` (need `_∙_`), `image` (needs `_≃_`), and
every path-object proof, since `is-contr→is-prop` needs a composition.

The final two declarations record why the split falls there: the fan
of the discrete graph is the singleton on the nose, and its
contractibility needs no Kan operation.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.RxTier1 where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma

-- Tier 0 --------------------------------------------------------------

record reflexive-graph v e : Type₊ (v ⊔ e) where
  field
    vtx  : Type v
    edge : vtx → vtx → Type e
    rx   : (x : vtx) → edge x x

record reflexive-graphᴰ {v e} v' e' (G : reflexive-graph v e)
  : Type (v ⊔ e ⊔ v' ₊ ⊔ e' ₊) where
  private module G = reflexive-graph G
  field
    vtx  : G.vtx → Type v'
    edge : (x y : G.vtx) → G.edge x y → vtx x → vtx y → Type e'
    rx   : {x : G.vtx} (u : vtx x) → edge x x (G.rx x) u u

-- pure combinators, no Kan ---------------------------------------------

Singl-contr : ∀ {u} {A : Type u} (x : A) → is-contr (Σ y ∶ A , x ≡ y)
Singl-contr x .center = x , refl
Singl-contr x .paths (y , q) i = q i , λ j → q (i ∧ j)

prop-inhabited→is-contr : ∀ {u} {A : Type u} → is-prop A → A → is-contr A
prop-inhabited→is-contr p c .center = c
prop-inhabited→is-contr p c .paths = p c

dep-rx : ∀ {ℓ} (w z : Level) (A : Type ℓ) → Type (ℓ ⊔ w ₊ ⊔ z ₊)
dep-rx w z A = A → reflexive-graph w z

-- Tier 1 ---------------------------------------------------------------

module _ {ℓ w z} (A : Type ℓ) (B : dep-rx w z A) where
  private module B x = reflexive-graph (B x)

  product : reflexive-graph (ℓ ⊔ w) (ℓ ⊔ z)
  product .reflexive-graph.vtx      = (x : A) → B.vtx x
  product .reflexive-graph.edge f g = (x : A) → B.edge x (f x) (g x)
  product .reflexive-graph.rx f x   = B.rx x (f x)

module rx {v e} (G : reflexive-graph v e) where
  open reflexive-graph G

  vfam : (w z : Level) → Type (v ⊔ w ₊ ⊔ z ₊)
  vfam w z = dep-rx w z vtx

  efam : (w z : Level) → Type (v ⊔ e ⊔ w ₊ ⊔ z ₊)
  efam w z = (x y : vtx) → edge x y → reflexive-graph w z

  disp : (w z : Level) → Type (v ⊔ e ⊔ w ₊ ⊔ z ₊)
  disp w z = reflexive-graphᴰ w z G

  diag : ∀ {w z} → efam w z → vfam w z
  diag B x = B x x (rx x)

  cotensor : ∀ {ℓ} (A : Type ℓ) → reflexive-graph (ℓ ⊔ v) (ℓ ⊔ e)
  cotensor A = product A (λ _ → G)

  fan : vtx → Type (v ⊔ e)
  fan x = Σ y ∶ vtx , edge x y

  cofan : vtx → Type (v ⊔ e)
  cofan y = Σ x ∶ vtx , edge x y

  fan-center : ∀ x → fan x
  fan-center x = x , rx x

  cofan-center : ∀ x → cofan x
  cofan-center x = x , rx x

  involutive : Type (v ⊔ e)
  involutive = ∀ {x y} → edge x y → edge y x

  transitive : Type (v ⊔ e)
  transitive = ∀ {x y z} → edge x y → edge y z → edge x z

  is-univalent : Type (v ⊔ e)
  is-univalent = ∀ x → is-prop (fan x)

  is-univalent-op : Type (v ⊔ e)
  is-univalent-op = ∀ y → is-prop (cofan y)

  op : reflexive-graph v e
  op .reflexive-graph.vtx    = vtx
  op .reflexive-graph.edge x y = edge y x
  op .reflexive-graph.rx     = rx

  -- to-id needs only `ap fst`, so it is below Kan
  module univalence (univ : is-univalent) where
    fan-contr : ∀ x → is-contr (fan x)
    fan-contr x = prop-inhabited→is-contr (univ x) (fan-center x)

    to-id : (x y : vtx) → edge x y → x ≡ y
    to-id x y p = ap fst (univ x (fan-center x) (y , p))

  record hom {v' e'} (H : reflexive-graph v' e') : Type (v ⊔ v' ⊔ e ⊔ e') where
    private module H = reflexive-graph H
    field
      vmap    : vtx → H.vtx
      emap    : (x y : vtx) → edge x y → H.edge (vmap x) (vmap y)
      pres-rx : (x : vtx) → emap x x (rx x) ≡ H.rx (vmap x)

  module _ {v' e'} (D : reflexive-graphᴰ v' e' G) where
    private module D = reflexive-graphᴰ D

    total : reflexive-graph (v ⊔ v') (e ⊔ e')
    total .reflexive-graph.vtx                  = Σ x ∶ vtx , D.vtx x
    total .reflexive-graph.edge (x , u) (y , w) = Σ p ∶ edge x y , D.edge x y p u w
    total .reflexive-graph.rx (x , u)           = rx x , D.rx u

    total-op : reflexive-graphᴰ v' e' op
    total-op .reflexive-graphᴰ.vtx            = D.vtx
    total-op .reflexive-graphᴰ.edge x y p u w = D.edge y x p w u
    total-op .reflexive-graphᴰ.rx u           = D.rx u

    component : vfam v' e'
    component x .reflexive-graph.vtx      = D.vtx x
    component x .reflexive-graph.edge u w = D.edge x x (rx x) u w
    component x .reflexive-graph.rx u     = D.rx u

    is-cov-fibration : Type (v ⊔ v' ⊔ e ⊔ e')
    is-cov-fibration = ∀ x y (p : edge x y) (u : D.vtx x)
                     → is-contr (Σ w ∶ D.vtx y , D.edge x y p u w)

    is-ctrv-fibration : Type (v ⊔ v' ⊔ e ⊔ e')
    is-ctrv-fibration = ∀ x y (p : edge x y) (w : D.vtx y)
                      → is-contr (Σ u ∶ D.vtx x , D.edge x y p u w)

    module cov-fibration (fib : is-cov-fibration) where
      push : (x y : vtx) → edge x y → D.vtx x → D.vtx y
      push x y p u = fib x y p u .center .fst

      lift : (x y : vtx) (p : edge x y) (u : D.vtx x)
           → D.edge x y p u (push x y p u)
      lift x y p u = fib x y p u .center .snd

  binary-product : ∀ {w z} (H : reflexive-graph w z)
                 → reflexive-graph (v ⊔ w) (e ⊔ z)
  binary-product H .reflexive-graph.vtx = vtx × reflexive-graph.vtx H
  binary-product H .reflexive-graph.edge (a , b) (c , d) =
    edge a c × reflexive-graph.edge H b d
  binary-product H .reflexive-graph.rx (a , b) = rx a , reflexive-graph.rx H b

  comprehension : ∀ {ℓ} (P : vtx → Type ℓ) → reflexive-graph (v ⊔ ℓ) e
  comprehension P .reflexive-graph.vtx = Σ x ∶ vtx , P x
  comprehension P .reflexive-graph.edge (x , _) (y , _) = edge x y
  comprehension P .reflexive-graph.rx (x , _) = rx x

  constant : ∀ {w z} (S : reflexive-graph w z) → disp w z
  constant S .reflexive-graphᴰ.vtx _          = reflexive-graph.vtx S
  constant S .reflexive-graphᴰ.edge _ _ _ u v = reflexive-graph.edge S u v
  constant S .reflexive-graphᴰ.rx u           = reflexive-graph.rx S u

discrete : ∀ {ℓ} → Type ℓ → reflexive-graph ℓ ℓ
discrete A .reflexive-graph.vtx      = A
discrete A .reflexive-graph.edge x y = x ≡ y
discrete A .reflexive-graph.rx x     = refl

codiscrete : ∀ {ℓ} → Type ℓ → reflexive-graph ℓ 0ℓ
codiscrete A .reflexive-graph.vtx      = A
codiscrete A .reflexive-graph.edge _ _ = ⊤
codiscrete A .reflexive-graph.rx _     = tt

is-path-objects : ∀ {ℓ w z} {A : Type ℓ} → dep-rx w z A → Type (ℓ ⊔ w ⊔ z)
is-path-objects B = ∀ x → rx.is-univalent (B x)

is-displayed-univalent : ∀ {v e v' e'} {G : reflexive-graph v e}
                       → rx.disp G v' e' → Type (v ⊔ v' ⊔ e')
is-displayed-univalent {G = G} D = is-path-objects (rx.component G D)

-- the fan of `discrete` is the singleton, on the nose
fan-of-discrete
  : ∀ {ℓ} {A : Type ℓ} (x : A) → rx.fan (discrete A) x ≡ (Σ y ∶ A , x ≡ y)
fan-of-discrete x = refl

-- and it is contractible without any Kan operation
disc-fan-contr : ∀ {ℓ} (A : Type ℓ) (x : A) → is-contr (rx.fan (discrete A) x)
disc-fan-contr A x = Singl-contr x
```
