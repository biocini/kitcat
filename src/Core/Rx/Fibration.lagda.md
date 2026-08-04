Fibred reflexive graphs, after Sterling, *Reflexive Graph Lenses*. A fibration
is a displayed reflexive graph whose lifts are contractible rather than merely
chosen. Fibrations are path objects, they exchange variance under the total
opposite, and they arise from lenses whose transport is universal. Straightening
identifies the displayed edges of a covariant fibration with vertical edges in
the components, and carries the fibration back to a lens on its diagonal family.

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Core.Rx.Fibration where

open import Core.Type
open import Core.Data.Sigma
open import Core.Base
open import Core.Kan using (is-contr→is-prop)
open import Core.Equiv
open import Core.IdSys
  using ( is-based-identity-system; based-singl-contr→Ids; Ids-based→equiv
        ; is-identity-system; to-path; to-path-over; Ids-based→equiv⁻ )
open import Core.Transport.Base using (transport; module Path-over)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.Rx.Type
open import Core.Rx.Base
open import Core.Rx.Properties
open import Core.Rx.Lens

module _ {v v' e e'} {G : reflexive-graph v e} (D : rx.disp G v' e') where
  private
    module G = reflexive-graph G
    module D = reflexive-graphᴰ D
```

## Fibrations are path objects

The component fan of a covariant fibration at `u` is the lift of the reflexive
edge out of `u`, contractible by assumption. The same computation lands on the
cofan contravariantly, and the two fan conditions agree.

```agda

  cov-fibration-path-object : rx.is-cov-fibration G D → is-displayed-univalent D
  cov-fibration-path-object fib x u = is-contr→is-prop (fib x x (G.rx x) u)

  ctrv-fibration-path-object : rx.is-ctrv-fibration G D → is-displayed-univalent D
  ctrv-fibration-path-object fib x =
    po.is-univalent-op→ (rx.component G D x) (λ u → is-contr→is-prop (fib x x (G.rx x) u))

```

## Duality

Reversing the displayed edges exchanges the two lifting conditions: the total
opposite of a covariant fibration is a contravariant fibration over the opposite
base, and conversely. Both directions are definitional.

```agda

  fibration-duality : rx.is-cov-fibration G D → rx.is-ctrv-fibration (rx.op G) (rx.total-op G D)
  fibration-duality fib x y p w = fib y x p w

  fibration-duality⁻ : rx.is-ctrv-fibration G D → rx.is-cov-fibration (rx.op G) (rx.total-op G D)
  fibration-duality⁻ fib x y p u = fib y x p u
```

## Straightening

Fix a covariant fibration. Both the displayed edges out of `u` over `p` and the
vertical edges out of the pushforward `push p u` have contractible total space,
the first by the lifting condition at `p`, the second by the lifting condition at
reflexivity. Each is therefore a based identity system — the first based at
`push p u` with the lifting edge, the second at `push p u` with displayed
reflexivity — so both are identified with the paths out of `push p u`.

```agda

module cov-straightening {v v' e e'} {G : reflexive-graph v e}
  (D : rx.disp G v' e') (fib : rx.is-cov-fibration G D) where
  private
    module G = reflexive-graph G
    module D = reflexive-graphᴰ D
  open rx.cov-fibration G D fib

  edge-ids : (x y : G.vtx) (p : G.edge x y) (u : D.vtx x)
           → is-based-identity-system (push x y p u) (D.edge x y p u) (lift x y p u)
  edge-ids x y p u = based-singl-contr→Ids (fib x y p u)

  vert-ids : ∀ {y} (w : D.vtx y)
           → is-based-identity-system w (D.edge y y (G.rx y) w) (D.rx w)
  vert-ids {y} w = based-singl-contr→Ids (fib y y (G.rx y) w)

  straighten-equiv : (x y : G.vtx) (p : G.edge x y) (u : D.vtx x) {w : D.vtx y}
                   → D.edge x y p u w ≃ D.edge y y (G.rx y) (push x y p u) w
  straighten-equiv x y p u =
    Ids-based→equiv⁻ (edge-ids x y p u) ∙e Ids-based→equiv (vert-ids (push x y p u))

  straighten : (x y : G.vtx) {p : G.edge x y} {u : D.vtx x} {w : D.vtx y}
             → D.edge x y p u w → D.edge y y (G.rx y) (push x y p u) w
  straighten x y {p} {u} = straighten-equiv x y p u .fst

  unstraighten : (x y : G.vtx) {p : G.edge x y} {u : D.vtx x} {w : D.vtx y}
               → D.edge y y (G.rx y) (push x y p u) w → D.edge x y p u w
  unstraighten x y {p} {u} = esym (straighten-equiv x y p u) .fst
```

The pushforward is an oplax covariant lens structure on the diagonal family of
components: straightening displayed reflexivity gives the unitor, a vertical edge
from the pushforward along reflexivity back to the vertex.

```agda

  underlying-lens : oplax-cov-lens G (rx.component G D)
  underlying-lens .oplax-cov-lens.has-push          = push
  underlying-lens .oplax-cov-lens.has-unitor {x} u  = straighten x x (D.rx u)
```


## Fibrations from lenses

A lens has *universal pushforwards* when the fan of every pushforward is a
proposition, and *universal pullbacks* when the cofan of every pullback is. The
displayed edges of a covariant display over `p` out of `u` are exactly that fan,
so the display becomes a fibration with the reflexive edge at `push p u` as the
chosen lift; the contravariant case is dual.

```agda

module _ {v e w z} {G : reflexive-graph v e} {B : rx.vfam G w z} where
  private
    module G = reflexive-graph G
    module B x = reflexive-graph (B x)

  cov-lens-to-fibration : (L : oplax-cov-lens G B)
                        → universal-push G B (oplax-cov-lens.has-push L)
                        → rx.is-cov-fibration G (oplax-cov-lens.display L)
  cov-lens-to-fibration L univ x y p u =
    prop-inhabited→is-contr (univ x y p u)
      (rx.fan-center (B y) (oplax-cov-lens.has-push L x y p u))

  ctrv-lens-to-fibration : (M : lax-ctrv-lens G B)
                         → universal-pull G B (lax-ctrv-lens.has-pull M)
                         → rx.is-ctrv-fibration G (lax-ctrv-lens.display M)
  ctrv-lens-to-fibration M univ x y p u =
    prop-inhabited→is-contr (univ x y p u)
      (rx.cofan-center (B x) (lax-ctrv-lens.has-pull M x y p u))

```

Universality of the transport is the same condition as univalence of every
component. One direction instantiates univalence at the transported vertex. For
the other, the unitor and the reflexive edge are two elements of the fan of
`push (G.rx x) u`, which is a proposition; their first components identify the
pushforward along reflexivity with the vertex itself, and the fan condition
transports along that identification.

```agda

  path-object→universal-push : (L : oplax-cov-lens G B) → is-path-objects B
                             → universal-push G B (oplax-cov-lens.has-push L)
  path-object→universal-push L B-univ x y p u =
    B-univ y (oplax-cov-lens.has-push L x y p u)

  universal-push→path-object : (L : oplax-cov-lens G B)
                             → universal-push G B (oplax-cov-lens.has-push L)
                             → is-path-objects B
  universal-push→path-object L univ x u =
    transport (λ i → is-prop (rx.fan (B x) (unit i))) (univ x x (G.rx x) u)
    where
    push-rx = oplax-cov-lens.has-push L x x (G.rx x) u

    unit : push-rx ≡ u
    unit = ap fst (univ x x (G.rx x) u (rx.fan-center (B x) push-rx)
                                       (u , oplax-cov-lens.has-unitor L u))

  path-object→universal-pull : (M : lax-ctrv-lens G B) → is-path-objects B
                             → universal-pull G B (lax-ctrv-lens.has-pull M)
  path-object→universal-pull M B-univ x y p u =
    po.is-univalent→op (B x) (B-univ x) (lax-ctrv-lens.has-pull M x y p u)

  universal-pull→path-object : (M : lax-ctrv-lens G B)
                             → universal-pull G B (lax-ctrv-lens.has-pull M)
                             → is-path-objects B
  universal-pull→path-object M univ x = po.is-univalent-op→ (B x) cofan-prop
    where
    pull-rx : B.vtx x → B.vtx x
    pull-rx = lax-ctrv-lens.has-pull M x x (G.rx x)

    unit : ∀ u → pull-rx u ≡ u
    unit u = ap fst (univ x x (G.rx x) u (rx.cofan-center (B x) (pull-rx u))
                                         (u , lax-ctrv-lens.has-unitor M u))

    cofan-prop : rx.is-univalent-op (B x)
    cofan-prop u = transport (λ i → is-prop (rx.cofan (B x) (unit u i))) (univ x x (G.rx x) u)
```

The components of a covariant display carry the vertices of the lens' own family
and the edges out of the pushforward along reflexivity. Over a family of path
objects the two agree: the oplax unitor is an incoming edge at `u`, so the cofan
identity system identifies `u` with its pushforward and carries reflexivity to
the unitor over that identification.

```agda

  module _ (L : oplax-cov-lens G B) (B-univ : is-path-objects B) where
    private
      module L = oplax-cov-lens L

      cofan-ids : ∀ x → is-identity-system (λ q u → B.edge x u q) (B.rx x)
      cofan-ids x = po.cofan-idsys (B x) (po.is-univalent→op (B x) (B-univ x))

      shift : ∀ x (u : B.vtx x) → u ≡ L.has-push x x (G.rx x) u
      shift x u = cofan-ids x .to-path (L.has-unitor u)

    component-of-display : ∀ x → B x ≡ rx.component G L.display x
    component-of-display x i .reflexive-graph.vtx      = B.vtx x
    component-of-display x i .reflexive-graph.edge u q = B.edge x (shift x u i) q
    component-of-display x i .reflexive-graph.rx u     =
      cofan-ids x .to-path-over (L.has-unitor u) i
```

The lens is carried onto its display's underlying lens along that identification.
Pushforwards need no adjustment: the fibration's chosen lift is the lens'
own, so the two agree on the nose and the identification is constant on vertices.
For the unitors, straightening at reflexivity transports the unitor at the
pushforward along the identification the lift provides, while the cofan identity
system transports reflexivity along the identification the unitor provides; the
two meet because the lift of a lens-built fibration *is* reflexivity at the
pushforward.

```agda

    private
      lens-fib : rx.is-cov-fibration G L.display
      lens-fib = cov-lens-to-fibration L (path-object→universal-push L B-univ)

    open cov-straightening L.display lens-fib

    private
      fwd : ∀ x (u : B.vtx x) → B.vtx x
      fwd x u = L.has-push x x (G.rx x) u

      lift-path : ∀ x (u : B.vtx x) → fwd x u ≡ u
      lift-path x u = edge-ids x x (G.rx x) u .to-path (L.has-unitor u)

      lift-over : ∀ x (u : B.vtx x)
                → subst (B.edge x (fwd x u)) (lift-path x u) (B.rx x (fwd x u))
                  ≡ L.has-unitor u
      lift-over x u =
        Path-over.from-pathp (edge-ids x x (G.rx x) u .to-path-over (L.has-unitor u))

      unitor-over : ∀ x (u : B.vtx x)
                  → PathP (λ i → B.edge x (shift x (fwd x u) i) u)
                          (subst (B.edge x (fwd x u)) (lift-path x u) (B.rx x (fwd x u)))
                          (oplax-cov-lens.has-unitor underlying-lens u)
      unitor-over x u i =
        subst (B.edge x (shift x (fwd x u) i)) (lift-path x u)
              (cofan-ids x .to-path-over (L.has-unitor (fwd x u)) i)

      unitor-line : ∀ x (u : B.vtx x)
                  → PathP (λ i → B.edge x (shift x (fwd x u) i) u)
                          (L.has-unitor u)
                          (oplax-cov-lens.has-unitor underlying-lens u)
      unitor-line x u =
        transport (λ j → PathP (λ i → B.edge x (shift x (fwd x u) i) u)
                               (lift-over x u j)
                               (oplax-cov-lens.has-unitor underlying-lens u))
                  (unitor-over x u)

    underlying-lens-of-display
      : PathP (λ i → oplax-cov-lens G (λ x → component-of-display x i))
              L underlying-lens
    underlying-lens-of-display i .oplax-cov-lens.has-push         = L.has-push
    underlying-lens-of-display i .oplax-cov-lens.has-unitor {x} u = unitor-line x u i
```
