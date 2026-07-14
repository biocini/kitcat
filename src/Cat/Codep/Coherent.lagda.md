Lane Biocini
July 2026

The coherence overlay over the `hcategory` bundle. Three 2-cells that
the five base axioms leave undetermined: `absorb-lcoh` and
`absorb-rcoh` pin the identity-flanked absorptions (`absorb-l`/
`absorb-r` at an argument that is itself a representable action of the
identity) against the `interchange` twist, and `couple-D₀` couples the
two at the doubly-centered point. They are the wild-categorical residue
of Kelly's unit coherences — the identity-flanked fragments of the base
associator that a set-level category discharges for free but a wild
(untruncated) one must posit.

The cells are independent of the five axioms: the twist is genuine
2-cell data, not derivable by `∙`-algebra from `compose-contr`/
`interchange`/`post-eval`/the unit equivalences (`interchange` is only
supplied pointwise, so no natural comparison of its members exists at
the base). They live in an *overlay* record over the bundle, not in
`hcategory-axioms`: the base five-field category and its strict
`op-invol` stay untouched as the self-dual core, and the overlay is
built or dualized on top.

From the three cells the θ-core is *derived*, not posited:

```text
ap (pre (idn x)) (post-eval (idn x))
  ≡ interchange (idn x) (idn x) (idn x) (idn x)
    ∙ ap (post (idn x)) (post-eval (idn x))
```

The `L`/`R`/`CD'` chain collapses the two identity-flanked absorptions
against the doubly-centered coupling. θ-core is the single
reconciliation that `op` needs, and it is exactly what the three cells
buy: no fourth cell, no fibre argument.

`op` dualizes the overlay *covariantly* (`op-coherent`): the two absorb
cells trade places through the θ-bridges (`bridge-l`/`bridge-r`, each
`ap _ θ`), and `couple-D₀` conjugates by `sym`. This self-duality is up
to the θ-bridges, NOT strict — there is no `op-coherent-invol`, and the
independence theorem forbids one:

```text
-- op-invol for the coherence cells is INDEPENDENT of the fields
-- (coherent-twist countermodel over the S² path groupoid; the
-- defect lives in π₃(S²) = ℤ). Strict op-involution of any finite
-- cell tower forces hom-truncation, so the category (five fields)
-- is strictly self-dual and the coherence overlay dualizes
-- covariantly, up to the θ-bridges.
```

The Route-B `op-axioms` (definitional fibre center, `Cat.Codep.Op`) is
what makes the bridges close: the op extraction is *definitionally* the
base extraction swapped, so `idemᵒ` and `idem` share a type and θ can
relate them.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Coherent where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; pcom)
open import Core.Path.Base using (cancell; move-r)
open import Core.Groupoid using (sym-distr)
open import Core.Homotopy using (homotopy-natural)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (is-prop→is-set)
open import Core.Function.Embedding using (equiv→lc)

open import Cat.Codep.Base
open import Cat.Codep.Op using (op)
```

## The coherence overlay

`hcategory-2-coherent` sits over a bundle: it opens `hcategory C` for
the whole derived API and posits only the three cells. Everything the
cell types mention — `absorb-l`/`absorb-r`, `pre`/`post`, `interchange`,
`post-eval`, `emb`/`idn` — is a base-derived name of the bundle. No
field interleaving, so no inline-square gymnastics: the cells come
first, and the θ-core is derived after.

```agda
record hcategory-2-coherent {o h} (C : hcategory o h) : Type (o ⊔ h) where
  no-eta-equality
  open hcategory C

  field
    absorb-lcoh
      : ∀ {y z} (g : hom y z) {v} (b : hom z v)
      → absorb-l (pre g b)
      ≡ interchange (idn y) g (idn y) b
      ∙ ap (λ a' → emb g ((y , a') , (v , b))) (post-eval (idn y))
    absorb-rcoh
      : ∀ {x y} (f : hom x y) {w} (a : hom w x)
      → absorb-r (post f a)
      ≡ sym (interchange f (idn y) a (idn y))
      ∙ ap (λ b' → emb f ((w , a) , (y , b'))) (post-eval (idn y))
    couple-D₀
      : ∀ {x}
      → absorb-l (post (idn x) (idn x))
      ∙ sym (absorb-r (post (idn x) (idn x)))
      ≡ interchange (idn x) (idn x) (idn x) (idn x)

  θ-core
    : ∀ {x}
    → ap (pre (idn x)) (post-eval (idn x))
    ≡ interchange (idn x) (idn x) (idn x) (idn x)
      ∙ ap (post (idn x)) (post-eval (idn x))
  θ-core {x} = sym i ∙ L
    where
      e : hom x x
      e = idn x

      D₀ : hom x x
      D₀ = pre e (idn x)

      IC : pre e D₀ ≡ post e D₀
      IC = interchange e e e e

      apPre : pre e D₀ ≡ pre e e
      apPre = ap (pre e) (post-eval e)

      apPost : post e D₀ ≡ post e e
      apPost = ap (post e) (post-eval e)

      L : absorb-l D₀ ≡ IC ∙ apPost
      L = absorb-lcoh e e

      R : absorb-r D₀ ≡ sym IC ∙ apPre
      R = absorb-rcoh e e

      CD : absorb-l D₀ ∙ sym (absorb-r D₀) ≡ IC
      CD = couple-D₀

      CD' : absorb-l D₀ ≡ IC ∙ absorb-r D₀
      CD' = move-r (absorb-l D₀) (absorb-r D₀) IC CD

      i : absorb-l D₀ ≡ apPre
      i = CD'
        ∙ ap (IC ∙_) R
        ∙ Path.assoc IC (sym IC) apPre
        ∙ ap (_∙ apPre) (Path.invr IC)
        ∙ Path.unitl apPre

  -- gauge-r/gauge-l derived: homotopy-naturality of absorb-r/absorb-l
  -- along post-eval, + couple-D₀/absorb-lcoh. Not a field. gauge-r
  -- collapses the identity-argument freedom of absorb-r onto post-eval
  -- (and gauge-l onto absorb-l), the residue the θ-core reconciliations
  -- (★)/i leave over the doubly-centered point.
  gauge-r : ∀ {x} → absorb-r (idn x) ≡ post-eval (idn x)
  gauge-r {x} =
    pcom (cancell apPost ar)
      (ap (sym apPost ∙_) (Nr ∙ ap (_∙ pe) star))
      (cancell apPost pe)
    where
      e : hom x x
      e = idn x
      D₀ : hom x x
      D₀ = pre e (idn x)
      IC : pre e D₀ ≡ post e D₀
      IC = interchange e e e e
      apPost : post e D₀ ≡ post e e
      apPost = ap (post e) (post-eval e)
      aR : post e D₀ ≡ D₀
      aR = absorb-r D₀
      pe : D₀ ≡ e
      pe = post-eval e
      ar : post e e ≡ e
      ar = absorb-r e
      L : absorb-l D₀ ≡ IC ∙ apPost
      L = absorb-lcoh e e
      CD' : absorb-l D₀ ≡ IC ∙ aR
      CD' = move-r (absorb-l D₀) aR IC (couple-D₀ {x})
      M : IC ∙ apPost ≡ IC ∙ aR
      M = sym L ∙ CD'
      -- (★): cancel IC from M
      star : aR ≡ apPost
      star = pcom (cancell IC aR) (ap (sym IC ∙_) (sym M)) (cancell IC apPost)
      Nr : apPost ∙ ar ≡ aR ∙ pe
      Nr = homotopy-natural (absorb-r {x} {x}) pe

  gauge-l : ∀ {x} → absorb-l (idn x) ≡ post-eval (idn x)
  gauge-l {x} =
    pcom (cancell apPre al)
      (ap (sym apPre ∙_) (Nl ∙ ap (_∙ pe) i))
      (cancell apPre pe)
    where
      e : hom x x
      e = idn x
      D₀ : hom x x
      D₀ = pre e (idn x)
      IC : pre e D₀ ≡ post e D₀
      IC = interchange e e e e
      apPre : pre e D₀ ≡ pre e e
      apPre = ap (pre e) (post-eval e)
      aR : post e D₀ ≡ D₀
      aR = absorb-r D₀
      pe : D₀ ≡ e
      pe = post-eval e
      al : pre e e ≡ e
      al = absorb-l e
      R : absorb-r D₀ ≡ sym IC ∙ apPre
      R = absorb-rcoh e e
      CD' : absorb-l D₀ ≡ IC ∙ aR
      CD' = move-r (absorb-l D₀) aR IC (couple-D₀ {x})
      -- i: cancel IC from CD' ∙ ap (IC ∙_) R (the θ-core (★)-analog)
      i : absorb-l D₀ ≡ apPre
      i = CD'
        ∙ ap (IC ∙_) R
        ∙ Path.assoc IC (sym IC) apPre
        ∙ ap (_∙ apPre) (Path.invr IC)
        ∙ Path.unitl apPre
      Nl : apPre ∙ al ≡ absorb-l D₀ ∙ pe
      Nl = homotopy-natural (absorb-l {x} {x}) pe

  gauge-lr : ∀ {x} → absorb-l (idn x) ≡ absorb-r (idn x)
  gauge-lr {x} = gauge-l {x} ∙ sym (gauge-r {x})
```

## Assembling the overlay

`assemble` is the refactor equation: the bundle plus the three cells
give the overlay. With the cells as the only fields, it is a trivial
constructor.

```agda
assemble
  : ∀ {o h} (C : hcategory o h)
    (open hcategory C)
    (coh-l : ∀ {y z} (g : hom y z) {v} (b : hom z v)
           → absorb-l (pre g b)
           ≡ interchange (idn y) g (idn y) b
           ∙ ap (λ a' → emb g ((y , a') , (v , b))) (post-eval (idn y)))
    (coh-r : ∀ {x y} (f : hom x y) {w} (a : hom w x)
           → absorb-r (post f a)
           ≡ sym (interchange f (idn y) a (idn y))
           ∙ ap (λ b' → emb f ((w , a) , (y , b'))) (post-eval (idn y)))
    (coh-θ : ∀ {x}
           → absorb-l (post (idn x) (idn x))
           ∙ sym (absorb-r (post (idn x) (idn x)))
           ≡ interchange (idn x) (idn x) (idn x) (idn x))
  → hcategory-2-coherent C
assemble C coh-l coh-r coh-θ .hcategory-2-coherent.absorb-lcoh = coh-l
assemble C coh-l coh-r coh-θ .hcategory-2-coherent.absorb-rcoh = coh-r
assemble C coh-l coh-r coh-θ .hcategory-2-coherent.couple-D₀   = coh-θ
```

## Prop-homs instance

Over a bundle whose homs are propositions, every hom-path space is a
proposition (`is-prop→is-set`), so each 2-cell is inhabited on the
nose and the three cells are one-liners.

```agda
module prop-homs {o h} (C : hcategory o h)
  (hom-prop : ∀ {x y} → is-prop (hcategory.hom C x y))
  where
  open hcategory C

  hom-set : ∀ {x y} → is-set (hom x y)
  hom-set = is-prop→is-set hom-prop

  coherent : hcategory-2-coherent C
  coherent .hcategory-2-coherent.absorb-lcoh g b = hom-set _ _ _ _
  coherent .hcategory-2-coherent.absorb-rcoh f a = hom-set _ _ _ _
  coherent .hcategory-2-coherent.couple-D₀       = hom-set _ _ _ _
```

## Covariant dualization

`op-coherent` transports the overlay onto `op C`. Under Route-B
(`Cat.Codep.Op`), the op extraction is definitionally the base
extraction swapped, so `Aᵒ.idem` and `A.idem` share a type; the θ-core
reconciles them, and the two bridges `ap _ θ` relay the op record's
absorptions onto the base's. The three cells discharge by whiskering
the bridges against the base cells; `couple-D₀ᵒ` conjugates the base
coupling by `sym`. There is deliberately no `op-coherent-invol`: strict
op-involution of the cells is independent of the fields (the S²/π₃
countermodel of the header).

```agda
module _ {o h} {C : hcategory o h} (A2 : hcategory-2-coherent C) where
  private
    module A  = hcategory C
    module Aᵒ = hcategory (op C)
    module A2 = hcategory-2-coherent A2

  private
    pre-compᵒ-is-post-comp
      : ∀ {w x} (c : A.hom w x)
      → Aᵒ.pre-comp (A.idn x) (A.idn x) c
      ≡ A.post-comp (A.idn x) (A.idn x) c
    pre-compᵒ-is-post-comp c = refl

    post-compᵒ-is-pre-comp
      : ∀ {x v} (c : A.hom x v)
      → Aᵒ.post-comp (A.idn x) (A.idn x) c
      ≡ A.pre-comp (A.idn x) (A.idn x) c
    post-compᵒ-is-pre-comp {x} {v} c =
        sym (Path.assoc H IC' (sym IC'))
      ∙ ap (H ∙_) (Path.invr IC')
      ∙ Path.unitr H
      where
        H = A.pre-comp (A.idn x) (A.idn x) c
        IC' = A.interchange (A.idn x) (A.idn x) (A.idn x) c

    module θ-derivation {x : A.ob} where
      private
        e : A.hom x x
        e = A.idn x

        ee : A.hom x x
        ee = A._⨾_ e e

        H0 = happly (A.emb-comp e e) ((x , e) , (x , e))
        IC = A.interchange e e e e
        apPost = ap (A.post e) (A.post-eval e)
        apPre = ap (A.pre e) (A.post-eval e)

        κ : (H0 ∙ IC) ∙ sym IC ≡ H0
        κ = sym (Path.assoc H0 IC (sym IC))
          ∙ ap (H0 ∙_) (Path.invr IC)
          ∙ Path.unitr H0

        θ-core : apPre ≡ IC ∙ apPost
        θ-core = A2.θ-core {x}

        M-B≡M-A : (((H0 ∙ IC) ∙ sym IC) ∙ apPre) ≡ ((H0 ∙ IC) ∙ apPost)
        M-B≡M-A =
            ap (_∙ apPre) κ
          ∙ ap (H0 ∙_) θ-core
          ∙ Path.assoc H0 IC apPost

        ξ : Aᵒ.comp-eq e e ≡ A.comp-eq e e
        ξ = ap (sym (A.post-eval ee) ∙_) M-B≡M-A

      θ : Aᵒ.idem {x} ≡ A.idem {x}
      θ = ap (_∙ A.post-eval e) ξ

    θ : ∀ {x} → Aᵒ.idem {x} ≡ A.idem {x}
    θ {x} = θ-derivation.θ {x}

    bridge-l : ∀ {w x} (c : A.hom w x) → Aᵒ.absorb-l c ≡ A.absorb-r c
    bridge-l {w} {x} c = ap Φ (θ {x})
      where
        Φ : (A._⨾_ (A.idn x) (A.idn x) ≡ A.idn x)
          → (A.post (A.idn x) c ≡ c)
        Φ z = equiv→lc A.unit-eqvr
          (sym (subst (λ t → A.post t c
                           ≡ A.post (A.idn x) (A.post (A.idn x) c))
            z (A.post-comp (A.idn x) (A.idn x) c)))

    bridge-r : ∀ {x v} (c : A.hom x v) → Aᵒ.absorb-r c ≡ A.absorb-l c
    bridge-r {x} {v} c =
        ap (λ z → Θ z (Aᵒ.post-comp (A.idn x) (A.idn x) c)) (θ {x})
      ∙ ap (Θ (A.idem {x})) (post-compᵒ-is-pre-comp c)
      where
        Θ : (A._⨾_ (A.idn x) (A.idn x) ≡ A.idn x)
          → (A.pre (A._⨾_ (A.idn x) (A.idn x)) c
             ≡ A.pre (A.idn x) (A.pre (A.idn x) c))
          → (A.pre (A.idn x) c ≡ c)
        Θ z u = equiv→lc A.unit-eqvl
          (sym (subst (λ t → A.pre t c
                           ≡ A.pre (A.idn x) (A.pre (A.idn x) c)) z u))

    couple-D₀ᵒ
      : ∀ {x}
      → Aᵒ.absorb-l (A.post (A.idn x) (A.idn x))
      ∙ sym (Aᵒ.absorb-r (A.post (A.idn x) (A.idn x)))
      ≡ sym (A.interchange (A.idn x) (A.idn x) (A.idn x) (A.idn x))
    couple-D₀ᵒ {x} =
      (λ i → bridge-l D₀ i ∙ sym (bridge-r D₀ i)) ∙ conj
      where
        D₀ = A.post (A.idn x) (A.idn x)
        IC = A.interchange (A.idn x) (A.idn x) (A.idn x) (A.idn x)

        conj : A.absorb-r D₀ ∙ sym (A.absorb-l D₀) ≡ sym IC
        conj =
            sym (sym-distr (A.absorb-l D₀) (sym (A.absorb-r D₀)))
          ∙ ap sym (A2.couple-D₀ {x})

  op-coherent : hcategory-2-coherent (op C)
  op-coherent .hcategory-2-coherent.absorb-lcoh g b =
    bridge-l (A.post g b) ∙ A2.absorb-rcoh g b
  op-coherent .hcategory-2-coherent.absorb-rcoh f a =
    bridge-r (A.pre f a) ∙ A2.absorb-lcoh f a
  op-coherent .hcategory-2-coherent.couple-D₀ = couple-D₀ᵒ
```
