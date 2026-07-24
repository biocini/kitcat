Identifications of reflexive-graph structures read off from equivalences between
them. `ua` is erased under `--erased-cubical`, so proofs appealing to it — and
proofs consuming their results — run on full cubical and are collected here.
Everything that does without it stays in the ordinary scheme.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Cat.Graph.Refl.Univalent where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Equiv using (_≃_; iso→equiv; esym; _∙e_)
open import Core.HLevel.Base using (Π-is-prop)
open import Core.Transport.Base using (module Path-over; is-prop→PathP)
open import Core.Transport.Properties using (is-contr-is-prop; is-prop-is-prop)
open import Core.Univalence using (ua; ua-β)
open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base
open import Cat.Graph.Refl.Properties
open import Cat.Graph.Refl.Lens
open import Cat.Graph.Refl.Fibration

private
  family-univ-is-prop : ∀ {ℓ w z} {X : Type ℓ} (B : dep-rx w z X)
                      → is-prop (is-path-objects B)
  family-univ-is-prop B = Π-is-prop λ _ → Π-is-prop λ _ → is-prop-is-prop _
```

## The display of an underlying lens

The display of the lens underlying a covariant fibration is the fibration itself.
Displayed vertices agree definitionally; the displayed edges agree along
straightening, and univalence turns each straightening into an identification of
edge types. The reflexivity datum lies over that line by the computation rule
`ua-β`, since the display sends it to its own straightening.

```agda

module _ {v v' e e'} {G : reflexive-graph v e}
  (D : rx.disp G v' e') (fib : rx.is-cov-fibration G D) where
  private
    module G = reflexive-graph G
    module D = reflexive-graphᴰ D
  open cov-straightening D fib

  display-of-underlying-lens : D ≡ oplax-cov-lens.display underlying-lens
  display-of-underlying-lens i .reflexive-graphᴰ.vtx            = D.vtx
  display-of-underlying-lens i .reflexive-graphᴰ.edge x y p u q = ua (straighten-equiv x y p u {q}) i
  display-of-underlying-lens i .reflexive-graphᴰ.rx {x} u       =
    Path-over.to-pathp {A = λ j → ua (straighten-equiv x x (G.rx x) u {u}) j}
                       (ua-β (straighten-equiv x x (G.rx x) u {u}) (D.rx u)) i
```

## Fibrations are lenses of path objects

Displaying a lens of path objects and taking the underlying lens of a fibration
are mutually inverse. Each roundtrip moves the underlying family or displayed
graph by the identification above, and the remaining data — the lifting
condition, componentwise univalence, the lens structure — either is a
proposition or travels with `underlying-lens-of-display`.

```agda

module _ {v e} (w z : Level) (G : reflexive-graph v e) where
  private
    module G = reflexive-graph G

    fibration-is-prop : (D : rx.disp G w z) → is-prop (rx.is-cov-fibration G D)
    fibration-is-prop D =
      Π-is-prop λ _ → Π-is-prop λ _ → Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _

  lens-of-path-objects : Type (v ⊔ w ⊔ e ⊔ z ⊔ w ₊ ⊔ z ₊)
  lens-of-path-objects =
    Σ B ∶ rx.vfam G w z
      , (is-path-objects B × oplax-cov-lens G B)

  fibration-of-path-objects : Type (v ⊔ w ⊔ e ⊔ z ⊔ w ₊ ⊔ z ₊)
  fibration-of-path-objects = Σ D ∶ rx.disp G w z , rx.is-cov-fibration G D

  lens-to-fibration : lens-of-path-objects → fibration-of-path-objects
  lens-to-fibration (B , B-univ , L) =
      oplax-cov-lens.display L
    , cov-lens-to-fibration L (path-object→universal-push L B-univ)

  fibration-to-lens : fibration-of-path-objects → lens-of-path-objects
  fibration-to-lens (D , fib) =
      rx.component G D
    , cov-fibration-path-object D fib
    , cov-straightening.underlying-lens D fib

  characterisation-of-fibs : lens-of-path-objects ≃ fibration-of-path-objects
  characterisation-of-fibs = iso→equiv lens-to-fibration fibration-to-lens sec retr
    where
    sec : (Λ : lens-of-path-objects) → fibration-to-lens (lens-to-fibration Λ) ≡ Λ
    sec (B , B-univ , L) i .fst x       = component-of-display L B-univ x (~ i)
    sec (B , B-univ , L) i .snd .fst    =
      is-prop→PathP (λ j → family-univ-is-prop (λ x → component-of-display L B-univ x (~ j)))
                    (fibration-to-lens (lens-to-fibration (B , B-univ , L)) .snd .fst)
                    B-univ i
    sec (B , B-univ , L) i .snd .snd    = underlying-lens-of-display L B-univ (~ i)

    retr : (F : fibration-of-path-objects) → lens-to-fibration (fibration-to-lens F) ≡ F
    retr (D , fib) i .fst = display-of-underlying-lens D fib (~ i)
    retr (D , fib) i .snd =
      is-prop→PathP (λ j → fibration-is-prop (display-of-underlying-lens D fib (~ j)))
                    (lens-to-fibration (fibration-to-lens (D , fib)) .snd) fib i
```

## The contravariant statement

The same equivalence for the other variance, obtained by reading both sides
against the opposite base. Opposition is involutive on reflexive graphs and on
displayed ones, and it carries lax contravariant lenses to oplax covariant ones
and contravariant fibrations to covariant ones, so each side transports along it;
only the componentwise univalence proofs need adjusting, and they are
propositions.

```agda

module _ {v e} (w z : Level) (G : reflexive-graph v e) where
  private
    module G = reflexive-graph G

  ctrv-lens-of-path-objects : Type (v ⊔ w ⊔ e ⊔ z ⊔ w ₊ ⊔ z ₊)
  ctrv-lens-of-path-objects =
    Σ B ∶ rx.vfam G w z
      , (is-path-objects B × lax-ctrv-lens G B)

  ctrv-fibration-of-path-objects : Type (v ⊔ w ⊔ e ⊔ z ⊔ w ₊ ⊔ z ₊)
  ctrv-fibration-of-path-objects = Σ D ∶ rx.disp G w z , rx.is-ctrv-fibration G D

  private
    lens-op : ctrv-lens-of-path-objects ≃ lens-of-path-objects w z (rx.op G)
    lens-op = iso→equiv fwd bwd sec retr
      where
      fwd : ctrv-lens-of-path-objects → lens-of-path-objects w z (rx.op G)
      fwd (B , B-univ , M) = (λ x → rx.op (B x))
                           , (λ x → po.op-path-object (B x) (B-univ x))
                           , tot-op-lens⁻ M

      bwd : lens-of-path-objects w z (rx.op G) → ctrv-lens-of-path-objects
      bwd (B' , B'-univ , L) = (λ x → rx.op (B' x))
                             , (λ x → po.op-path-object (B' x) (B'-univ x))
                             , tot-op-lens L

      sec : ∀ Λ → bwd (fwd Λ) ≡ Λ
      sec Λ@(B , B-univ , M) i .fst      = B
      sec Λ@(B , B-univ , M) i .snd .fst = family-univ-is-prop B (bwd (fwd Λ) .snd .fst) B-univ i
      sec Λ@(B , B-univ , M) i .snd .snd = M

      retr : ∀ Λ → fwd (bwd Λ) ≡ Λ
      retr Λ@(B' , B'-univ , L) i .fst      = B'
      retr Λ@(B' , B'-univ , L) i .snd .fst =
        family-univ-is-prop B' (fwd (bwd Λ) .snd .fst) B'-univ i
      retr Λ@(B' , B'-univ , L) i .snd .snd = L

    fibration-op
      : ctrv-fibration-of-path-objects ≃ fibration-of-path-objects w z (rx.op G)
    fibration-op = iso→equiv fwd bwd (λ _ → refl) (λ _ → refl)
      where
      fwd : ctrv-fibration-of-path-objects → fibration-of-path-objects w z (rx.op G)
      fwd (D , fib) = rx.total-op G D , fibration-duality⁻ D fib

      bwd : fibration-of-path-objects w z (rx.op G) → ctrv-fibration-of-path-objects
      bwd (D' , fib') = rx.total-op (rx.op G) D' , fibration-duality D' fib'

  ctrv-characterisation-of-fibs
    : ctrv-lens-of-path-objects ≃ ctrv-fibration-of-path-objects
  ctrv-characterisation-of-fibs =
    lens-op ∙e characterisation-of-fibs w z (rx.op G) ∙e esym fibration-op
```
