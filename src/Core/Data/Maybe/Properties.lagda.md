Properties of Maybe: equivalence with coproducts and h-level closure.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Maybe.Properties where

open import Core.Type
open import Core.Data.Nat.Type using (Nat; S)
open import Core.Base using (_≡_; refl; Contr; is-contr)
open import Core.Equiv using (_≃_; iso→equiv; Equiv; esym)
open import Core.Data.Sum.Type using (_⊎_; inl; inr)
open import Core.Data.Sum.Properties using (⊎-is-hlevel)

open import Core.Trait.Trunc
  using (is-hlevel; is-contr→is-hlevel)
open import Core.HLevel.Base using (equiv→is-hlevel)

open import Agda.Builtin.Maybe

Maybe-equiv-⊎
  : ∀ {u} {A : Type u} → Maybe A ≃ (⊤ ⊎ A)
Maybe-equiv-⊎ {A = A} = iso→equiv to from linv rinv
  where
    to : Maybe A → ⊤ ⊎ A
    to nothing  = inl tt
    to (just a) = inr a

    from : ⊤ ⊎ A → Maybe A
    from (inl _) = nothing
    from (inr a) = just a

    linv : (x : Maybe A) → from (to x) ≡ x
    linv nothing  = refl
    linv (just a) = refl

    rinv : (y : ⊤ ⊎ A) → to (from y) ≡ y
    rinv (inl tt) = refl
    rinv (inr a)  = refl

Maybe-is-hlevel
  : ∀ {u} {A : Type u} (n : Nat)
  → is-hlevel (S (S n)) A
  → is-hlevel (S (S n)) (Maybe A)
Maybe-is-hlevel {A = A} n ahl =
  equiv→is-hlevel (S (S n)) (esym Maybe-equiv-⊎) sum-hlevel
  where
    ⊤-hlevel : is-hlevel (S (S n)) ⊤
    ⊤-hlevel =
      is-contr→is-hlevel (S (S n)) (Contr tt (λ _ → refl))

    sum-hlevel : is-hlevel (S (S n)) (⊤ ⊎ A)
    sum-hlevel = ⊎-is-hlevel n ⊤-hlevel ahl

```
