Identity certificate: the Kan system vocabulary, the reference
cylinder construction, and the reflexive-graph fan calculus name the
same objects.

Eight checks, each `refl` or a retyping. Together they establish that
the composite-singleton is the fan of the discrete graph, that its
contractibility is `Singl-contr`, that a type family's Kan condition
is the covariant fibration condition of its displayed graph, and that
the two ternary embeddings in `Core` are one operation under different
currying.

`Sys` and the system operations land in `Exo`, so the first two checks
are by retyping rather than by a path.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.KanIdentities where

open import Core.Type using (Level; Type; Exo; Exoω)
open import Core.Base
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Kan
open import Core.Transport.Base using (Singl-contr)
open import Core.Transport.Properties using (SinglP-contr)
open import Core.Composite
open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base

private variable
  u v : Level
  A : Type u

-- 1. Sys is PartialsP at a constant family, on the nose.
--    (Sys lands in Exo, so the check is by retyping, not by a path.)
probe-Sys : (φ : I) (B : Type u) → Sys φ B → PartialsP φ (λ _ → B)
probe-Sys φ B s = s

-- 2. HSys is PartialsP, on the nose.
probe-HSys : (φ : I) (B : I → Type u) → HSys φ B → PartialsP φ B
probe-HSys φ B s = s

-- 3. Total-sys is the fan of the discrete graph at the composite.
probe-Total-fan
  : (φ : I) (s : Sys φ A)
  → Total-sys φ s ≡ rx.fan (discrete A) (sys-composite φ s)
probe-Total-fan φ s = refl

-- 4. Total-sys-contr IS Singl-contr at the composite.
probe-Total-contr
  : (φ : I) (s : Sys φ A)
  → Total-sys-contr φ s ≡ Singl-contr (sys-composite φ s)
probe-Total-contr φ s = refl

-- 5. hfil at φ ∨ ~ i is the filler; sys-filler is hfil permuted.
probe-sys-filler
  : (φ : I) (s : Sys φ A) (i : I)
  → sys-filler φ s i ≡ hfil φ i s
probe-sys-filler φ s i = refl

-- 6. sys-composite is hcom.
probe-sys-composite : (φ : I) (s : Sys φ A) → sys-composite φ s ≡ hcom φ s
probe-sys-composite φ s = refl

-- 7. SysP.SysLift over a discrete base is the fan of the displayed
--    graph of the family; its contractibility is SinglP-contr.
module _ {A : Type u} (P : A → Type v) where
  open SysP P

  disp-of : rx.disp (discrete A) v v
  disp-of .reflexive-graphᴰ.vtx = P
  disp-of .reflexive-graphᴰ.edge x y p a b = PathP (λ i → P (p i)) a b
  disp-of .reflexive-graphᴰ.rx u = refl

  probe-lift-is-disp-fan
    : {x y : A} (p : x ≡ y) (a : P x)
    → SysLift p a
    ≡ (Σ b ∶ reflexive-graphᴰ.vtx disp-of y
       , reflexive-graphᴰ.edge disp-of x y p a b)
  probe-lift-is-disp-fan p a = refl

  -- the Kan condition for P, read as: disp-of is a covariant fibration
  probe-lift-contr : rx.is-cov-fibration (discrete A) disp-of
  probe-lift-contr x y p a = SinglP-contr {A = λ i → P (p i)} a

-- 8. The two representable embeddings are one ternary operation.
module _ {A : Type u} where
  open import Core.Groupoid using (emb)
  open import Core.Groupoid.Virtual using (module repr)

  probe-emb-agree
    : {w x y z : A} (a : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    → emb a y q z r ≡ repr.emb {A = λ _ → A} q w a z r
  probe-emb-agree a q r = refl
```
