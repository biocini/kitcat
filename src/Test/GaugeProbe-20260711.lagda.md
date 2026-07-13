Scratch: derive the identity-argument gauges from the coherence
overlay. gauge-r/gauge-l are the homotopy-naturality of absorb-r/
absorb-l along post-eval, whiskered against the θ-core reconciliations
(★)/i and couple-D₀/absorb-lcoh. Not fields.

Scratch file — not in All.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.GaugeProbe-20260711 where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; pcom)
open import Core.Path.Base using (cancell)
open import Core.Homotopy using (homotopy-natural)

open import Cat.Codep.Base
open import Cat.Codep.Coherent

module _ {o h} (C : hcategory o h) (A2 : hcategory-2-coherent C) where
  open hcategory C
  open hcategory-2-coherent A2

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
