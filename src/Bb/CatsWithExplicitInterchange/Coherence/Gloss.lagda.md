Lane Biocini
July 2026

A gloss on `Bb.CatsWithExplicitInterchange.Coherence`: the elementary
forms of the nrm-straightening and the triangle faces. The main line
proves `assoc●-nrm` by the `nrm-slide` connection — each witness rides
its own path back to normal form along an `∧`-connection, so both
endpoints of the straightening are definitional and its displaced mate
is the same slide one level up — and dissolves the triangle faces into
propositional witness squares on `↝-fill` slides, filled by
`is-prop→SquareP`. Those arguments are cubical through and through: they
need interval connections, the type-directed boundary reduction of
`PathP`, and square fillers at propositional families, none of which
exists in standard MLTT.

This module records the transport-only constructions. The
straightening is one `J` per witness path component, innermost
first. The faces are `repr`-calculus chains: each face factors
through the `●`-whisker of a one-sided witness, `repr-refl`
discharges the characterization mismatch, and `repr-lc` at the
sealed σ-lines lands the chain on the unitors and the associator —
the seals are consumed as opaque paths, never unfolded. It is the
port source for an elementary presentation — with the straightening
and the faces in this form, every other leaf of the coherence
`∙`-trees (`ap-comp`, `is-contr→is-set`, the whiskers) is already
J-expressible, so the object-level coherence suite transfers to
MLTT verbatim. The cost the slides avoid shows up here as
computation: the `J`s reduce only propositionally (`J-refl`), so no
endpoint is strict, and the `∙ refl` tails of the `●`-witnesses
survive to be discharged by whoever consumes the endpoints.

The two constructions share their types and are interchangeable
under the coherence trees, which consume the lemmas only through
their values. No agreement cell between them is stated: bridging
two straightenings of the same projection is exactly the fst-wobble
the one-construction discipline exists to avoid, and nothing
consumes such a bridge.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Coherence.Gloss where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp)
open import Core.Transport.J using (J)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Base
open import Bb.CatsWithExplicitInterchange.Coherence using (is-2-coherent; module is-2-coherent)

module _ {o h} (C : category o h) where
  open category C
  open theory C

  assoc●-nrm
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {C : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable C)
    → assoc● U V W ≡ assoc (U .fst) (V .fst) (W .fst)
  assoc●-nrm (m , p) (n , q) (o , r) =
      J (λ _ r' → assoc● (m , p) (n , q) (o , r') ≡ assoc● (m , p) (n , q) (nrm o)) refl r
    ∙ J (λ _ q' → assoc● (m , p) (n , q') (nrm o) ≡ assoc● (m , p) (nrm n) (nrm o)) refl q
    ∙ J (λ _ p' → assoc● (m , p') (nrm n) (nrm o) ≡ assoc● (nrm m) (nrm n) (nrm o)) refl p

  module triangle {x y z} (f : hom x y) (g : hom y z) where
    A = emb f
    E = emb (idn y)
    B = emb g

    -- 1 = source of assoc (right-nested), 2 = target (left-nested)
    e₁ : A ▿ (E ▿ B) ≡ A ▿ B ;  e₁ = ap (A ▿_) (emb-idn-absorb g)
    e₂ : (A ▿ E) ▿ B ≡ A ▿ B ;  e₂ = ap (_▿ B) (▾-idn A)

    r₁ r₂ : is-representable (A ▿ E ▿ B)
    r₁ = nrm f ● (nrm (idn y) ● nrm g)      -- fst = f ⨾ (idn y ⨾ g)
    r₂ = (nrm f ● nrm (idn y)) ● nrm g      -- fst = (f ⨾ idn y) ⨾ g

    Uf : is-representable A ; Uf = (nrm f ● nrm (idn y)) ↝ ▾-idn A
    Vg : is-representable B ; Vg = (nrm (idn y) ● nrm g) ↝ emb-idn-absorb g

    s₀ s₁ s₂ : is-representable (A ▿ B)
    s₀ = nrm f ● nrm g          ;  s₁ = r₁ ↝ e₁  ;  s₂ = r₂ ↝ e₂

    Ĝr : is-representable A → is-representable (A ▿ B) ; Ĝr u = u ● nrm g
    Ĝl : is-representable B → is-representable (A ▿ B) ; Ĝl v = nrm f ● v

    private
      W  = (nrm f ● nrm (idn y)) .snd ; X  = emb-comp (f ⨾ idn y) g
      W' = (nrm (idn y) ● nrm g) .snd ; X' = emb-comp f (idn y ⨾ g)

      wr : s₂ .snd ≡ Ĝr Uf .snd
      wr = sym (Path.assoc X (ap (_▿ B) W) e₂)
         ∙ ap (X ∙_) (sym (ap-comp (_▿ B) W (▾-idn A)))

      wl : s₁ .snd ≡ Ĝl Vg .snd
      wl = sym (Path.assoc X' (ap (A ▿_) W') e₁)
         ∙ ap (X' ∙_) (sym (ap-comp (A ▿_) W' (emb-idn-absorb g)))

    face-r : repr-unique s₂ s₀ ≡ ap (_⨾ g) (unitr f)
    face-r = sym (repr-∙ s₂ (Ĝr Uf) s₀)
           ∙ ap (_∙ repr-unique (Ĝr Uf) s₀) (repr-refl (s₂ .snd) (Ĝr Uf .snd) wr)
           ∙ Path.unitl (repr-unique (Ĝr Uf) s₀)
           ∙ sym (repr-lc (ap Ĝr (unitr-σ● f)))

    face-l : repr-unique s₁ s₀ ≡ ap (f ⨾_) (unitl g)
    face-l = sym (repr-∙ s₁ (Ĝl Vg) s₀)
           ∙ ap (_∙ repr-unique (Ĝl Vg) s₀) (repr-refl (s₁ .snd) (Ĝl Vg .snd) wl)
           ∙ Path.unitl (repr-unique (Ĝl Vg) s₀)
           ∙ sym (repr-lc (ap Ĝl (unitl-σ● g)))

    face-a : is-2-coherent C → repr-unique s₁ s₂ ≡ assoc f (idn y) g
    face-a mid =
        ap (λ t → repr-unique (r₁ ↝ e₁) (r₂ ↝ t)) (mid .is-2-coherent.is-coh f g)
      ∙ ↝-repr r₁ r₂ e₁
      ∙ sym (repr-lc (assoc-σ● (nrm f) (nrm (idn y)) (nrm g)))

    triangle-weak : repr-unique s₁ s₂ ∙ ap (_⨾ g) (unitr f) ≡ ap (f ⨾_) (unitl g)
    triangle-weak = ap (repr-unique s₁ s₂ ∙_) (sym face-r) ∙ repr-∙ s₁ s₂ s₀ ∙ face-l

    triangle : is-2-coherent C
             → assoc f (idn y) g ∙ ap (_⨾ g) (unitr f) ≡ ap (f ⨾_) (unitl g)
    triangle mid = ap (_∙ ap (_⨾ g) (unitr f)) (sym (face-a mid)) ∙ triangle-weak
```
