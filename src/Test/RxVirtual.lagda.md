Placement certificate: the virtual-graph and push/pull vocabulary sits
strictly below `Core.Kan`, and the unit laws are where the displayed
packaging begins.

Imports are limited to `Core.Type`, `Core.Base`, `Core.Data.Sigma`.
This measures placement, not record design — the declarations are
transcribed, and the bundling and currying choices here are the
probe's convenience, not a proposal.

Two results. First, `push` and `pull` are definable from the ternary
action alone, and contravariant lifting over a graph is covariant
lifting over its opposite, definitionally. Second, packaging terms and
coterms as displayed *reflexive* graphs is not free: the displayed
reflexivity field is exactly the emb-action unit law, per hand, so it
is stated here as a hypothesis. That boundary is why the closure
calculus over displays comes online only on the unital side.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.RxVirtual where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma

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

module rx {v e} (G : reflexive-graph v e) where
  open reflexive-graph G

  op : reflexive-graph v e
  op .reflexive-graph.vtx      = vtx
  op .reflexive-graph.edge x y = edge y x
  op .reflexive-graph.rx       = rx

  module _ {v' e'} (D : reflexive-graphᴰ v' e' G) where
    private module D = reflexive-graphᴰ D

    is-cov-fibration : Type (v ⊔ v' ⊔ e ⊔ e')
    is-cov-fibration = ∀ x y (p : edge x y) (u : D.vtx x)
                     → is-contr (Σ w ∶ D.vtx y , D.edge x y p u w)

    is-ctrv-fibration : Type (v ⊔ v' ⊔ e ⊔ e')
    is-ctrv-fibration = ∀ x y (p : edge x y) (w : D.vtx y)
                      → is-contr (Σ u ∶ D.vtx x , D.edge x y p u w)

    module cov (fib : is-cov-fibration) where
      push : (x y : vtx) → edge x y → D.vtx x → D.vtx y
      push x y p u = fib x y p u .center .fst

      lift : (x y : vtx) (p : edge x y) (u : D.vtx x)
           → D.edge x y p u (push x y p u)
      lift x y p u = fib x y p u .center .snd

    module ctrv (fib : is-ctrv-fibration) where
      pull : (x y : vtx) → edge x y → D.vtx y → D.vtx x
      pull x y p w = fib x y p w .center .fst

      colift : (x y : vtx) (p : edge x y) (w : D.vtx y)
             → D.edge x y p (pull x y p w) w
      colift x y p w = fib x y p w .center .snd

-- pull over G is push over op, definitionally ------------------------

module _ {v e v' e'} (G : reflexive-graph v e)
         (D : reflexive-graphᴰ v' e' G) where
  private module D = reflexive-graphᴰ D

  total-op : reflexive-graphᴰ v' e' (rx.op G)
  total-op .reflexive-graphᴰ.vtx            = D.vtx
  total-op .reflexive-graphᴰ.edge x y p u w = D.edge y x p w u
  total-op .reflexive-graphᴰ.rx u           = D.rx u

  pull-is-op-push
    : rx.is-ctrv-fibration G D → rx.is-cov-fibration (rx.op G) total-op
  pull-is-op-push fib = λ x y p u → fib y x p u
```

## The virtual graph and its two representable displays

`emb` is the ternary representable action. Terms at `w` are `edge w −`
and coterms at `z` are `edge − z`; each is a displayed graph over the
virtual graph, and the display edges are exactly the `emb` actions.

```agda

record virtual-graph v e : Type₊ (v ⊔ e) where
  field
    graph : reflexive-graph v e

  open reflexive-graph graph public

  field
    emb : {x y : vtx} → edge x y
        → ∀ w → edge w x → ∀ z → edge y z → edge w z

-- The displayed *reflexive* graph of terms needs the unit laws: the
-- rx field of `term w` is exactly `emb (rx x) w u x (rx x) ≡ u`.
-- Per hand, as ruled.
record unital-vg v e : Type₊ (v ⊔ e) where
  field
    virt : virtual-graph v e

  open virtual-graph virt public

  field
    emb-idn▿ : ∀ {w x} (u : edge w x) → emb (rx x) w u x (rx x) ≡ u
    emb-idn▵ : ∀ {x z} (u : edge x z) → emb (rx x) x (rx x) z u ≡ u

module vg {v e} (V : unital-vg v e) where
  open unital-vg V

  -- terms at w: the covariant slot. push along p is post-composition.
  term : (w : vtx) → reflexive-graphᴰ e e graph
  term w .reflexive-graphᴰ.vtx x           = edge w x
  term w .reflexive-graphᴰ.edge x y p u u' = emb p w u _ (rx y) ≡ u'
  term w .reflexive-graphᴰ.rx u            = emb-idn▿ u

  -- coterms at z: the contravariant slot. pull along p is
  -- pre-composition, i.e. push in the opposite virtual graph.
  coterm : (z : vtx) → reflexive-graphᴰ e e graph
  coterm z .reflexive-graphᴰ.vtx x           = edge x z
  coterm z .reflexive-graphᴰ.edge x y p u u' = emb p x (rx x) z u' ≡ u
  coterm z .reflexive-graphᴰ.rx u            = emb-idn▵ u

  push-contr : Type (v ⊔ e)
  push-contr = ∀ w → rx.is-cov-fibration graph (term w)

  pull-contr : Type (v ⊔ e)
  pull-contr = ∀ z → rx.is-ctrv-fibration graph (coterm z)

  is-composable : Type (v ⊔ e)
  is-composable = push-contr × pull-contr

  module composable (c : is-composable) where
    push : ∀ w {x y} → edge x y → edge w x → edge w y
    push w {x} {y} p = rx.cov.push graph (term w) (c .fst w) x y p

    pull : ∀ z {x y} → edge x y → edge y z → edge x z
    pull z {x} {y} p = rx.ctrv.pull graph (coterm z) (c .snd z) x y p
```

## The Core instance

`discrete A` is a virtual graph as soon as a ternary composite is
supplied — `Core.Kan.pcom` is that argument, so the instance is
Kan-free here and Kan-inhabited downstream. `term w` is then the based
path space and `push` is post-composition.

```agda

Ternary : ∀ {ℓ} → Type ℓ → Type ℓ
Ternary A = {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z

discrete-vg
  : ∀ {ℓ} (A : Type ℓ) (t : Ternary A)
  → (∀ {w x} (u : w ≡ x) → t refl w u x refl ≡ u)
  → (∀ {x z} (u : x ≡ z) → t refl x refl z u ≡ u)
  → unital-vg ℓ ℓ
discrete-vg A t l r .unital-vg.virt .virtual-graph.graph
  .reflexive-graph.vtx = A
discrete-vg A t l r .unital-vg.virt .virtual-graph.graph
  .reflexive-graph.edge x y = x ≡ y
discrete-vg A t l r .unital-vg.virt .virtual-graph.graph
  .reflexive-graph.rx x = refl
discrete-vg A t l r .unital-vg.virt .virtual-graph.emb = t
discrete-vg A t l r .unital-vg.emb-idn▿ = l
discrete-vg A t l r .unital-vg.emb-idn▵ = r

-- term w over discrete A is the based path space at w
term-of-discrete
  : ∀ {ℓ} (A : Type ℓ) (t : Ternary A)
    {l : ∀ {w x} (u : w ≡ x) → t refl w u x refl ≡ u}
    {r : ∀ {x z} (u : x ≡ z) → t refl x refl z u ≡ u}
    (w x : A)
  → reflexive-graphᴰ.vtx (vg.term (discrete-vg A t l r) w) x ≡ (w ≡ x)
term-of-discrete A t w x = refl

-- push over it is post-composition by the supplied ternary op
push-of-discrete
  : ∀ {ℓ} (A : Type ℓ) (t : Ternary A)
    {l : ∀ {w x} (u : w ≡ x) → t refl w u x refl ≡ u}
    {r : ∀ {x z} (u : x ≡ z) → t refl x refl z u ≡ u}
    (w : A)
    (c : vg.is-composable (discrete-vg A t l r))
    {x y : A} (p : x ≡ y)
  → (w ≡ x) → (w ≡ y)
push-of-discrete A t {l} {r} w c p =
  vg.composable.push (discrete-vg A t l r) c w p
```
