The double-loop instance of the two-field record: the tensor on
`∞-groupoid (Ω² Y)` by `Emb x (l , r) = l ∙ (x ∙ r)`, unit `refl`,
for a pointed `Y` supplied with the two collapse hypotheses the
pull fiber needs (`Ω² Y` connected and 1-truncated suffice; at
`Y = S²` the fiber is genuinely non-contractible, so the
hypotheses mark the honest boundary of the axiom, not a
convenience). The routes share every leg through the junction
`l ∙ ((x ∙ y) ∙ r)`: `ι⁻` resolves it planarly, `ι⁺` inserts the
positive full twist, and `ω-junction` certifies that the record's
derived discrepancy is exactly the whiskered Eckmann–Hilton
commutator conjugated into position — the derived framing. On a
unit flank the twist degenerates, inhabiting both vanishing
statements and, through the flank-boundary theorem, both unitor
agreement types — the `θ I ≡ refl` normalization holds here in
derived form; `routes-differ-from` converts any π₃-nontriviality
certificate for `Y` into the distinctness of the two fields.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.CatsWithExplicitInterchange.Gist.DoubleLoopTensor where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Data.Empty using (⊥)
open import Core.Data.Pointed
open import Core.Path.Base using (conj-cancel)
open import Core.Path.Exchange
  using ( Ω²; full-twist; full-twist-unit-l; full-twist-unit-r
        ; ∙-pre-equiv; ∙-post-equiv)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (SinglP-contr)
open import Core.Equiv.Base using (_≃_; iso→equiv; is-equiv)
open import Core.Equiv.Properties using (is-contr-equiv; Σ-equiv-snd; _∙e_)
open import Core.Function.Embedding
  using (is-equiv→is-embedding; is-embedding→ap-equiv; equiv→lc)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Groupoid using (∞-groupoid)
open import Bb.CatsWithExplicitInterchange.Monoidal
open import Bb.CatsWithExplicitInterchange.Monoidal.Properties
  using (flank-vanish→unitr-agreement; flank-vanish→unitl-agreement)

module double-loop-tensor {u} (Y : Type* u)
  (flank-collapse : {c c' : Ω² Y → Ω² Y}
    → ((l r : Ω² Y) → l ∙ c r ≡ l ∙ c' r) ≃ ((r : Ω² Y) → c r ≡ c' r))
  (slot-faithful : (k h : Ω² Y)
    → ((r : Ω² Y) → k ∙ r ≡ h ∙ r) ≃ (k ≡ h))
  where

  private
    C∘ : category u u
    C∘ = ∞-groupoid (Ω² Y)

    I∘ : Ω² Y
    I∘ = refl

  open tensor-virtual C∘ I∘

  Emb : Ω² Y → ⊗₀-composite
  Emb x (l , r) = l ∙ (x ∙ r)

  open tensor-representable C∘ I∘ Emb
```

## The pull fiber

```agda
  private
    rev-path : {x y : Ω² Y} → (x ≡ y) ≃ (y ≡ x)
    rev-path = iso→equiv (λ p i → p (~ i)) (λ p i → p (~ i))
      (λ _ → refl) (λ _ → refl)

    curry-equiv : (k : Ω² Y) {G : ⊗₀-composite}
      → (Emb k ≡ G) ≃ ((l r : Ω² Y) → Emb k (l , r) ≡ G (l , r))
    curry-equiv k = iso→equiv
      (λ w l r → happly w (l , r))
      (λ fam → funext λ γ → fam (γ .fst) (γ .snd))
      (λ _ → refl) (λ _ → refl)

    middle-nf : (x y r : Ω² Y) → (x ∙ (refl ∙ y)) ∙ r ≡ x ∙ (refl ∙ (y ∙ r))
    middle-nf x y r =
        sym (Path.assoc x (refl ∙ y) r)
      ∙ ap (x ∙_) (sym (Path.assoc refl y r))

  pull-contr : ∀ x y → is-contr (is-⊗₀-representable (Emb x ▾₀ y))
  pull-contr x y =
    is-contr-equiv (Σ-equiv-snd λ k → curry-equiv k)
      (is-contr-equiv (Σ-equiv-snd λ k → flank-collapse)
        (subst
          (λ h → is-contr (Σ k ∶ Ω² Y , ((r : Ω² Y) → k ∙ r ≡ h r)))
          (funext (middle-nf x y))
          (is-contr-equiv (Σ-equiv-snd λ k → slot-faithful k (x ∙ (refl ∙ y)))
            (is-contr-equiv (Σ-equiv-snd λ _ → rev-path)
              (SinglP-contr {A = λ _ → Ω² Y} (x ∙ (refl ∙ y)))))))
```

## The two routes

Both routes travel through the junction form and share their legs;
the only difference is the loop inserted there. Neither leg touches
the interchange machinery: the in-leg absorbs the unit padding and
reassociates the junction together, the out-leg redistributes it
toward the over-flank reading.

```agda
  module _ (m n : Ω² Y) where

    in-leg : (γ : ⊗₀-ctx) → (Emb m ▾₀ n) γ ≡ γ .fst ∙ ((m ∙ n) ∙ γ .snd)
    in-leg (l , r) =
      ap (l ∙_) (ap (m ∙_) (Path.unitl (n ∙ r)) ∙ Path.assoc m n r)

    out-leg : (γ : ⊗₀-ctx) → γ .fst ∙ ((m ∙ n) ∙ γ .snd) ≡ (m ▴₀ Emb n) γ
    out-leg (l , r) =
        ap (l ∙_) (sym (Path.assoc m n r))
      ∙ Path.assoc l m (n ∙ r)
      ∙ ap (_∙ (n ∙ r)) (ap (l ∙_) (sym (Path.unitr m)))

    twist-leg : (γ : ⊗₀-ctx)
              → γ .fst ∙ ((m ∙ n) ∙ γ .snd) ≡ γ .fst ∙ ((m ∙ n) ∙ γ .snd)
    twist-leg (l , r) = ap (λ t → l ∙ (t ∙ r)) (full-twist m n)

    ι-core⁻ : Emb m ▾₀ n ≡ m ▴₀ Emb n
    ι-core⁻ = funext λ γ → in-leg γ ∙ out-leg γ

    ι-core⁺ : Emb m ▾₀ n ≡ m ▴₀ Emb n
    ι-core⁺ = funext λ γ → in-leg γ ∙ twist-leg γ ∙ out-leg γ

  ι⁻♭ : {A B : ⊗₀-composite}
      → is-⊗₀-representable A → is-⊗₀-representable B → A ▿₀ B ≡ A ▵₀ B
  ι⁻♭ (m , p) (n , q) = sym (λ i → p i ▿₀ q i) ∙ ι-core⁻ m n ∙ (λ i → p i ▵₀ q i)

  ι⁺♭ : {A B : ⊗₀-composite}
      → is-⊗₀-representable A → is-⊗₀-representable B → A ▿₀ B ≡ A ▵₀ B
  ι⁺♭ (m , p) (n , q) = sym (λ i → p i ▿₀ q i) ∙ ι-core⁺ m n ∙ (λ i → p i ▵₀ q i)
```

## The instance

```agda
  Double-loop-tensor : monoidal-axioms₀ C∘
  Double-loop-tensor .monoidal-axioms₀.I = I∘
  Double-loop-tensor .monoidal-axioms₀.⊗₀-emb = Emb
  Double-loop-tensor .monoidal-axioms₀.ι⁺ = ι⁺♭
  Double-loop-tensor .monoidal-axioms₀.ι⁻ = ι⁻♭
  Double-loop-tensor .monoidal-axioms₀.⊗₀-pull-contr = pull-contr
  Double-loop-tensor .monoidal-axioms₀.⊗₀-unit =
    λ x → Path.unitl (x ∙ refl) ∙ Path.unitr x
```

## `ω` is the full twist

Stripping the shared legs by conjugation cancellation exhibits the
derived discrepancy as the junction-whiskered full twist — the
framing is read off the record, never stored in it.

```agda
  private module M = monoidal-axioms₀ Double-loop-tensor

  private
    refl-conj : ∀ {v} {X : Type v} {x y : X} (P : x ≡ y)
              → refl ∙ P ∙ refl ≡ P
    refl-conj P = Path.unitl (P ∙ refl) ∙ Path.unitr P

    q-cancel : ∀ {v} {X : Type v} {x y z : X} (p : x ≡ y) (q : y ≡ z)
             → q ∙ sym (p ∙ q) ≡ sym p
    q-cancel p q =
        sym (Path.unitl (q ∙ sym (p ∙ q)))
      ∙ ap (_∙ (q ∙ sym (p ∙ q))) (sym (Path.invl p))
      ∙ sym (Path.assoc (sym p) p (q ∙ sym (p ∙ q)))
      ∙ ap (sym p ∙_) (Path.assoc p q (sym (p ∙ q)) ∙ Path.invr (p ∙ q))
      ∙ Path.unitr (sym p)

    conj-collapse : ∀ {v} {X : Type v} {x y z : X}
      (p : x ≡ y) (t : y ≡ y) (q : y ≡ z)
      → (p ∙ t ∙ q) ∙ sym (p ∙ q) ≡ p ∙ t ∙ sym p
    conj-collapse p t q =
        sym (Path.assoc p (t ∙ q) (sym (p ∙ q)))
      ∙ ap (p ∙_) ( sym (Path.assoc t q (sym (p ∙ q)))
                  ∙ ap (t ∙_) (q-cancel p q))

    conj-refl : ∀ {v} {X : Type v} {x y : X} (p : x ≡ y)
              → p ∙ refl ∙ sym p ≡ refl
    conj-refl p = ap (p ∙_) (Path.unitl (sym p)) ∙ Path.invr p

  ω-junction : (m n : Ω² Y)
    → M.ω-pt m n
    ≡ funext (λ γ → in-leg m n γ ∙ twist-leg m n γ ∙ sym (in-leg m n γ))
  ω-junction m n =
      (λ i → refl-conj (ι-core⁺ m n) i ∙ sym (refl-conj (ι-core⁻ m n) i))
    ∙ (λ i → funext (λ γ →
        conj-collapse (in-leg m n γ) (twist-leg m n γ) (out-leg m n γ) i))
```

## The unit flanks vanish

The full twist degenerates on either unit flank, so the whiskered
junction loop collapses and `ω` vanishes there — the `θ I ≡ refl`
normalization arriving in derived form.

```agda
  ω-vanish-l : (t : Ω² Y) → M.ω-pt I∘ t ≡ refl
  ω-vanish-l t =
      ω-junction I∘ t
    ∙ (λ i → funext (λ γ → in-leg I∘ t γ
        ∙ ap (λ s → γ .fst ∙ (s ∙ γ .snd)) (full-twist-unit-l t i)
        ∙ sym (in-leg I∘ t γ)))
    ∙ (λ i → funext (λ γ → conj-refl (in-leg I∘ t γ) i))

  ω-vanish-r : (m : Ω² Y) → M.ω-pt m I∘ ≡ refl
  ω-vanish-r m =
      ω-junction m I∘
    ∙ (λ i → funext (λ γ → in-leg m I∘ γ
        ∙ ap (λ s → γ .fst ∙ (s ∙ γ .snd)) (full-twist-unit-r m i)
        ∙ sym (in-leg m I∘ γ)))
    ∙ (λ i → funext (λ γ → conj-refl (in-leg m I∘ γ) i))
```

## The routes are conditionally distinct

No in-tree `Y` carries π₃ evidence yet — S²/Hopf is a parallel
tier — so distinctness is stated against a nontriviality
certificate for the full twist: agreement of the fields forces the
junction loop to `refl` through the same cancellation that drives
`ω-junction`, and the junction whisker is an equivalence, so the
full twist itself collapses.

```agda
  routes-differ-from
    : (m n : Ω² Y)
    → (full-twist m n ≡ refl → ⊥)
    → M.ι⁺-pt m n ≡ M.ι⁻-pt m n → ⊥
  routes-differ-from m n H e = H (equiv→lc ap-jm-equiv tw-refl)
    where
    jm : Ω² Y → Ω² Y
    jm s = refl ∙ (s ∙ refl)

    ap-jm-equiv : is-equiv (ap jm {x = m ∙ n} {y = m ∙ n})
    ap-jm-equiv = is-embedding→ap-equiv
      (is-equiv→is-embedding ((∙-post-equiv refl ∙e ∙-pre-equiv refl) .snd))

    ω-refl : M.ω-pt m n ≡ refl
    ω-refl = ap (_∙ sym (M.ι⁻-pt m n)) e ∙ Path.invr (M.ι⁻-pt m n)

    pointwise : in-leg m n (I∘ , I∘) ∙ twist-leg m n (I∘ , I∘)
              ∙ sym (in-leg m n (I∘ , I∘)) ≡ refl
    pointwise =
      ap (λ w → happly w (I∘ , I∘)) (sym (ω-junction m n) ∙ ω-refl)

    tw-refl : ap jm (full-twist m n) ≡ refl
    tw-refl = conj-cancel
      (in-leg m n (I∘ , I∘)) (sym (in-leg m n (I∘ , I∘)))
      (ap jm (full-twist m n))
      (Path.invr (in-leg m n (I∘ , I∘)) ∙ sym pointwise)
```

## The agreement types are inhabited

```agda
  unitr-agreement-holds : theory₀.unitr-agreement Double-loop-tensor
  unitr-agreement-holds =
    flank-vanish→unitr-agreement Double-loop-tensor ω-vanish-l

  unitl-agreement-holds : theory₀.unitl-agreement Double-loop-tensor
  unitl-agreement-holds =
    flank-vanish→unitl-agreement Double-loop-tensor ω-vanish-l ω-vanish-r
```
