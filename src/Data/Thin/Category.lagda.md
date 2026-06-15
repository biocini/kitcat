The category of thinnings as a Cat.Type category.

Objects are scopes (lists), morphisms are thinnings (OPEs).
The ternary `emb` is `representation`: given a thinning
`θ : iz ≤ jz`, embed it into a composition
`a ⨾ θ ⨾ b` for any `a : w ≤ iz` and `b : jz ≤ v`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.Thin.Category where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv.Base using (is-equiv; iso→equiv)
open import Core.Data.List using (List; []; _∷_)
open import Data.Thin.Type
open import Data.Thin.Base
open import Data.Thin.Tri
open import Cat.Type



private module _ {u} {K : Type u} where
  private variable
    iz jz kz mz : List K
  emb : {iz jz : List K} → iz ≤ jz
    → ∀ wz → wz ≤ iz → ∀ vz → jz ≤ vz → wz ≤ vz
  emb θ _ a _ b = representation a θ b

  -- representation oi f oi ≡ f: the identity thinning is
  -- absorbed on both sides. Induction on f.
  emb-yon-eval
    : (f : iz ≤ jz) → emb f iz oi jz oi ≡ f
  emb-yon-eval (o' f) = ap o' (emb-yon-eval f)
  emb-yon-eval (os f) = ap os (emb-yon-eval f)
  emb-yon-eval oz     = refl

  -- representation a f (representation oi g b)
  --   ≡ representation (representation a f oi) g b
  -- The noy/yon interchange. Use with-abstraction on
  -- tri3 to decompose the intermediate compositions.
  emb-interchange
    : (f : iz ≤ jz) (g : jz ≤ kz)
      (w : List K) (a : w ≤ iz) (v : List K) (b : kz ≤ v)
    → emb f w a v (emb g jz oi v b)
    ≡ emb g w (emb f w a jz oi) v b
  emb-interchange f g w a v (o' b) = ap o' (emb-interchange f g w a _ b)
  emb-interchange f (o' g) w a v (os b) = ap o' (emb-interchange f g w a _ b)
  emb-interchange (o' f) (os g) w a v (os b) = ap o' (emb-interchange f g w a _ b)
  emb-interchange (os f) (os g) w (o' a) v (os b) = ap o' (emb-interchange f g _ a _ b)
  emb-interchange (os f) (os g) w (os a) v (os b) = ap os (emb-interchange f g _ a _ b)
  emb-interchange oz oz w a v oz = refl

  -- representation a (f ⨾ g) b
  --   ≡ representation a f (representation oi g b)
  -- The composite decomposes via noy on the right factor.
  -- Use with tri f g to expose f ⨾ g in constructor form.
  -- representation a (f ⨾ g) b ≡ representation a f (representation oi g b)
  -- Induction on g and b simultaneously, following representation's pattern.
  emb-fiber-paths
    : {f : iz ≤ jz} {g : jz ≤ kz}
    → (wz : List K) (a : wz ≤ iz) (vz : List K) (b : kz ≤ vz)
    → emb (f ⨾ g) wz a vz b ≡ emb f wz a vz (emb g jz oi vz b)
  emb-fiber-paths {f = f} {g} wz a vz (o' b) =
    ap o' (emb-fiber-paths {f = f} {g} wz a _ b)
  emb-fiber-paths {f = f} {o' g} wz a vz (os b) =
    ap o' (emb-fiber-paths {f = f} {g} wz a _ b)
  emb-fiber-paths {f = o' f} {os g} wz a vz (os b) =
    ap o' (emb-fiber-paths {f = f} {g} wz a _ b)
  emb-fiber-paths {f = os f} {os g} wz (o' a) vz (os b) =
    ap o' (emb-fiber-paths {f = f} {g} _ a _ b)
  emb-fiber-paths {f = os f} {os g} wz (os a) vz (os b) =
    ap os (emb-fiber-paths {f = f} {g} _ a _ b)
  emb-fiber-paths {f = oz} {(oz)} wz oz vz oz = refl

  -- noy absorbs: representation oi f b ≡ f ⨾ b
  noy-absorb
    : (f : iz ≤ jz) (b : jz ≤ kz) → emb f iz oi kz b ≡ f ⨾ b
  noy-absorb f (o' b) = ap o' (noy-absorb f b)
  noy-absorb (o' f) (os b) = ap o' (noy-absorb f b)
  noy-absorb (os f) (os b) = ap os (noy-absorb f b)
  noy-absorb oz oz = refl

  -- yon absorbs: representation a f oi ≡ a ⨾ f
  yon-absorb
    : (a : iz ≤ jz) (f : jz ≤ kz) → emb f iz a kz oi ≡ a ⨾ f
  yon-absorb a (o' f) = ap o' (yon-absorb a f)
  yon-absorb (o' a) (os f) = ap o' (yon-absorb a f)
  yon-absorb (os a) (os f) = ap os (yon-absorb a f)
  yon-absorb oz oz = refl

  unitl : (h : iz ≤ jz) → oi ⨾ h ≡ h
  unitl (o' h) = ap o' (unitl h)
  unitl (os h) = ap os (unitl h)
  unitl oz     = refl

  unitr : (h : iz ≤ jz) → h ⨾ oi ≡ h
  unitr (o' h) = ap o' (unitr h)
  unitr (os h) = ap os (unitr h)
  unitr oz     = refl

  ideml-equiv : {jz : List K} → is-equiv (λ h → emb oi iz oi jz h)
  ideml-equiv = iso→equiv
    (λ h → emb oi _ oi _ h) id
    noy-id noy-id .snd
    where
      noy-id : (h : iz ≤ jz) → emb oi iz oi jz h ≡ h
      noy-id h = noy-absorb oi h ∙ unitl h

  idemr-equiv : {ez : List K} → is-equiv (λ g → emb oi ez g iz oi)
  idemr-equiv = iso→equiv
    (λ g → emb oi _ g _ oi) id
    yon-id yon-id .snd
    where
      yon-id : (g : iz ≤ jz) → emb oi iz g jz oi ≡ g
      yon-id g = yon-absorb g oi ∙ unitr g

  oi-unital : emb oi iz oi iz oi ≡ oi
  oi-unital = emb-yon-eval oi

  emb-unit
    : Σ e ∶ iz ≤ iz
    , (∀ {v} → is-equiv (λ (h : iz ≤ v) → emb e iz e v h))
    × (∀ {w} → is-equiv (λ (g : w ≤ iz) → emb e w g iz e))
  emb-unit .fst = oi
  emb-unit .snd = ideml-equiv , idemr-equiv

  emb-compose-contr
    : (f : iz ≤ jz) (g : jz ≤ kz)
    → is-contr
        (fiber (emb {iz} {kz})
          (λ wz a vz b →
            emb f wz a vz (emb g jz oi vz b)))
  emb-compose-contr fz gz .center =
    fz ⨾ gz
    , funext λ wz → funext λ a →
      funext λ vz → funext λ b →
        emb-fiber-paths wz a vz b
  emb-compose-contr fz gz .paths (hz , q) = {!!}
    where
      p : fz ⨾ gz ≡ hz
      p = sym (
        sym (emb-yon-eval hz)
        ∙ (λ i → q i _ oi _ oi)
        ∙ ap (emb fz _ oi _) (emb-yon-eval gz)
        ∙ noy-absorb fz gz)

thin-category : ∀ {u} (K : Type u) → category u u
thin-category K .category.ob = List K
thin-category K .category.hom = _≤_
thin-category K .category.emb = emb
thin-category K .category.unit = emb-unit
thin-category K .category.compose-contr = emb-compose-contr
thin-category K .category.interchange = emb-interchange
thin-category K .category.yon-eval = emb-yon-eval

```
