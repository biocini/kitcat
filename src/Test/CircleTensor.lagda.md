The circle instance of the two-field record: the tensor on
`∞-groupoid Circle` by `Emb x (l , r) = mult l (mult x r)`, unit
`base`. The pull fiber is contractible by a four-step reduction —
currying (definitional), left-translation cancellation
(`mult-l-cancel`), one transport along associativity, first-slot
faithfulness (`mult-faithful`) — landing on the path singleton.
`ι⁻` is the canonical reassociation route; `ι⁺` deforms it by the
pointwise rotation of the `▵₀`-composite, so `ω` winds positively at
the detection point; `routes-differ` detects the deformation through
`loop-nontrivial`: the record's first concrete inhabitant carries two
genuinely distinct interchange paths.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Test.CircleTensor where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Data.Empty using (⊥)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (SinglP-contr)
open import Core.Equiv.Base using (_≃_; iso→equiv)
open import Core.Equiv.Properties using (is-contr-equiv; Σ-equiv-snd)

open import Cat.Type
open import Cat.Groupoid using (∞-groupoid)
open import Cat.Monoidal

open import HData.Circle
open Circle

private
  C∘ : category _ _
  C∘ = ∞-groupoid Circle

open tensor-virtual C∘ base

Emb : Circle → ⊗₀-composite
Emb x (l , r) = mult l (mult x r)

open tensor-representable C∘ base Emb
```

## The pull fiber

```agda
private
  rev-path : {x y : Circle} → (x ≡ y) ≃ (y ≡ x)
  rev-path = iso→equiv (λ p i → p (~ i)) (λ p i → p (~ i))
    (λ _ → refl) (λ _ → refl)

  curry-equiv : (k : Circle) {G : ⊗₀-composite}
    → (Emb k ≡ G) ≃ ((l r : Circle) → Emb k (l , r) ≡ G (l , r))
  curry-equiv k = iso→equiv
    (λ w l r → happly w (l , r))
    (λ fam → funext λ γ → fam (γ .fst) (γ .snd))
    (λ _ → refl) (λ _ → refl)

pull-contr : ∀ x y → is-contr (is-⊗₀-representable (Emb x ▾₀ y))
pull-contr x y =
  is-contr-equiv (Σ-equiv-snd λ k → curry-equiv k)
    (is-contr-equiv (Σ-equiv-snd λ k → mult-l-cancel)
      (subst
        (λ h → is-contr (Σ k ∶ Circle , ((r : Circle) → mult k r ≡ h r)))
        (funext (mult-assoc x y))
        (is-contr-equiv (Σ-equiv-snd λ k → mult-faithful k (mult x y))
          (is-contr-equiv (Σ-equiv-snd λ _ → rev-path)
            (SinglP-contr {A = λ _ → Circle} (mult x y))))))
```

## The two routes

```agda
ι-nrm : (m n : Circle) → Emb m ▾₀ n ≡ m ▴₀ Emb n
ι-nrm m n = funext λ (l , r) →
    sym (mult-assoc l m (mult n r))
  ∙ ap (λ t → mult t (mult n r)) (ap (mult l) (sym (mult-unit-r m)))

ι⁻♭ : {A B : ⊗₀-composite}
    → is-⊗₀-representable A → is-⊗₀-representable B → A ▿₀ B ≡ A ▵₀ B
ι⁻♭ (m , p) (n , q) = sym (λ i → p i ▿₀ q i) ∙ ι-nrm m n ∙ (λ i → p i ▵₀ q i)

ι⁺♭ : {A B : ⊗₀-composite}
    → is-⊗₀-representable A → is-⊗₀-representable B → A ▿₀ B ≡ A ▵₀ B
ι⁺♭ {A} {B} U V = ι⁻♭ U V ∙ funext (λ γ → rot ((A ▵₀ B) γ))
```

## The instance

```agda
Circle-tensor : monoidal-axioms₀ C∘
Circle-tensor .monoidal-axioms₀.I = base
Circle-tensor .monoidal-axioms₀.⊗₀-emb = Emb
Circle-tensor .monoidal-axioms₀.ι⁺ = ι⁺♭
Circle-tensor .monoidal-axioms₀.ι⁻ = ι⁻♭
Circle-tensor .monoidal-axioms₀.⊗₀-pull-contr = pull-contr
Circle-tensor .monoidal-axioms₀.⊗₀-unit = mult-unit-r
```

## The routes are distinct

Cancelling `ι⁻` forces the deformation to `refl`; its value at the
context `(base , base)` is `rot base = loop`, and `loop` does not
wind trivially.

```agda
routes-differ
  : ι⁺♭ (⊗₀-nrm base) (⊗₀-nrm base) ≡ ι⁻♭ (⊗₀-nrm base) (⊗₀-nrm base) → ⊥
routes-differ e = loop-nontrivial (ap (λ w → happly w (base , base)) D-trivial)
  where
  P = ι⁻♭ (⊗₀-nrm base) (⊗₀-nrm base)
  D = funext (λ γ → rot ((Emb base ▵₀ Emb base) γ))

  D-trivial : D ≡ refl
  D-trivial =
      sym (Path.unitl D)
    ∙ ap (_∙ D) (sym (Path.invl P))
    ∙ sym (Path.assoc (sym P) P D)
    ∙ ap (sym P ∙_) e
    ∙ Path.invl P
```
