H-level definitions and closure properties.

The H-Level machinery in this module is largely derived from 1Lab
(Amélia Liao et al.), with additional influence from Chen's
semicategories-with-identities formalization.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.HLevel.Base where

open import Core.Type
open import Core.Base
open import Core.Sub
open import Core.Kan
open Core.Kan.Path
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat.Type
open import Core.Data.Nat.Base using (_+_; _<_; _≤_; suc; step)
import Core.Data.Nat.Properties as Nat
open import Core.Path.Base
open import Core.Equiv.Base
open import Core.Transport

private variable
  ℓ ℓ' : Level
  A B : Type ℓ
  n k : Nat

is-hlevel : Nat → Type ℓ → Type ℓ
is-hlevel Z A = is-contr A
is-hlevel (S Z) A = is-prop A
is-hlevel (S (S n)) A = (x y : A) → is-hlevel (S n) (x ≡ y)

is-hlevel-suc : is-hlevel n A → is-hlevel (S n) A
is-hlevel-suc {n = Z} c = is-contr→is-prop c
is-hlevel-suc {n = S Z} p x y = is-prop→is-set p x y
is-hlevel-suc {n = S (S n)} hl x y = is-hlevel-suc (hl x y)

is-hlevel-+ : (n k : Nat) → is-hlevel n A → is-hlevel (n + k) A
is-hlevel-+ {A = A} n Z hl = subst (λ m → is-hlevel m A) (sym (Nat.add.unitr n)) hl
is-hlevel-+ {A = A} n (S k) hl =
  subst (λ m → is-hlevel m A) (sym (Nat.add.+suc n k))
    (is-hlevel-suc (is-hlevel-+ n k hl))

is-contr→is-hlevel : (n : Nat) → is-contr A → is-hlevel n A
is-contr→is-hlevel Z c = c
is-contr→is-hlevel (S n) c = is-hlevel-suc (is-contr→is-hlevel n c)

is-prop→is-hlevel-suc : is-prop A → is-hlevel (S n) A
is-prop→is-hlevel-suc {n = Z} p = p
is-prop→is-hlevel-suc {n = S Z} p x y = is-prop→is-set p x y
is-prop→is-hlevel-suc {n = S (S n)} p x y =
  is-prop→is-hlevel-suc {n = S n} (is-prop→is-set p x y)

is-hlevel-is-prop : (n : Nat) → is-prop (is-hlevel n A)
is-hlevel-is-prop Z = is-contr-is-prop _
is-hlevel-is-prop (S Z) = is-prop-is-prop _
is-hlevel-is-prop (S (S n)) p q i x y = is-hlevel-is-prop (S n) (p x y) (q x y) i

retract→is-hlevel : (n : Nat)
                  → (f : A → B) (g : B → A)
                  → is-left-inverse f g
                  → is-hlevel n A → is-hlevel n B
retract→is-hlevel Z f g r c .center = f (c .center)
retract→is-hlevel Z f g r c .paths y = ap f (c .paths (g y)) ∙ r y
retract→is-hlevel (S Z) f g r p x y = sym (r x) ∙ ap f (p (g x) (g y)) ∙ r y
retract→is-hlevel (S (S n)) f g r hl x y =
  retract→is-hlevel (S n) fwd (ap g) retract-proof (hl (g x) (g y))
  where
    fwd : g x ≡ g y → x ≡ y
    fwd p = sym (r x) ∙ ap f p ∙ r y

    retract-proof : is-left-inverse fwd (ap g)
    retract-proof q = J (λ y' q' → sym (r x) ∙ ap f (ap g q') ∙ r y' ≡ q')
      (ap (sym (r x) ∙_) (Path.unitl (r x)) ∙ (Path.invl (r x))) q

Path-is-hlevel : {x y : A} → is-hlevel (S n) A → is-hlevel n (x ≡ y)
Path-is-hlevel {n = Z} p = prop-inhabited→is-contr (is-prop→is-set p _ _) (p _ _)
Path-is-hlevel {n = S n} hl = hl _ _

PathP-is-hlevel : ∀ {A : I → Type ℓ} {x : A i0} {y : A i1}
                → is-hlevel (S n) (A i1) → is-hlevel n (PathP A x y)
PathP-is-hlevel {A = A} {x = x} {y = y} hl =
  subst (is-hlevel _) pathp-eq (Path-is-hlevel {x = coe01 A x} {y = y} hl)
  where
    pathp-eq : (coe01 A x ≡ y) ≡ PathP A x y
    pathp-eq i = PathP (∂.contract A (~ i)) (coe-filler A x (~ i)) y

Π-is-prop : {B : A → Type ℓ'}
          → ((a : A) → is-prop (B a))
          → is-prop ((a : A) → B a)
Π-is-prop prop f g i = λ a → prop a (f a) (g a) i

Πi-is-prop : {B : A → Type ℓ'}
           → ((a : A) → is-prop (B a))
           → is-prop ({a : A} → B a)
Πi-is-prop prop f g i {a} = prop a f g i

Π-is-hlevel : {B : A → Type ℓ'} (n : Nat)
            → ((a : A) → is-hlevel n (B a))
            → is-hlevel n ((a : A) → B a)
Π-is-hlevel Z hl .center a = hl a .center
Π-is-hlevel Z hl .paths f i a = hl a .paths (f a) i
Π-is-hlevel (S Z) hl = Π-is-prop hl
Π-is-hlevel (S (S n)) hl f g =
  retract→is-hlevel (S n) funext happly (λ _ → refl)
    (Π-is-hlevel (S n) (λ a → hl a (f a) (g a)))

Σ-prop-path : ∀ {B : A → Type ℓ'} (bp : ∀ x → is-prop (B x))
            → {x y : Σ B}
            → (x .fst ≡ y .fst) → x ≡ y
Σ-prop-path bp {x} {y} p i =
  p i , is-prop→PathP (λ i → bp (p i)) (x .snd) (y .snd) i

Σ-is-prop : {B : A → Type ℓ'}
          → is-prop A → (∀ a → is-prop (B a)) → is-prop (Σ B)
Σ-is-prop aprop bprop (a₁ , b₁) (a₂ , b₂) = Σ-prop-path bprop (aprop a₁ a₂)

Σ-prop² : ∀ {u v} {A : Type u} {B : A → Type v}
        → is-prop A → ((a : A) → is-prop (B a)) → is-prop (Σ B)
Σ-prop² aprop bprop (a₁ , b₁) (a₂ , b₂) i =
  aprop a₁ a₂ i , is-prop→PathP (λ j → bprop (aprop a₁ a₂ j)) b₁ b₂ i

Σ-is-hlevel : {B : A → Type ℓ'} (n : Nat)
            → is-hlevel n A → ((a : A) → is-hlevel n (B a))
            → is-hlevel n (Σ B)
Σ-is-hlevel Z acontr bcontr .center =
  acontr .center , bcontr (acontr .center) .center
Σ-is-hlevel Z acontr bcontr .paths (a , b) i =
  acontr .paths a i
  , is-prop→PathP (λ i → is-contr→is-prop (bcontr (acontr .paths a i)))
      (bcontr (acontr .center) .center) b i
Σ-is-hlevel (S Z) aprop bprop = Σ-is-prop aprop bprop
Σ-is-hlevel {B = B} (S (S n)) ahl bhl (a₁ , b₁) (a₂ , b₂) =
  retract→is-hlevel (S n) fwd bwd (λ _ → refl) inner
  where
    Σ-Path : Type _
    Σ-Path = Σ p ∶ a₁ ≡ a₂ , PathP (λ i → B (p i)) b₁ b₂

    fwd : Σ-Path → (a₁ , b₁) ≡ (a₂ , b₂)
    fwd (p , bp) i = p i , bp i

    bwd : (a₁ , b₁) ≡ (a₂ , b₂) → Σ-Path
    bwd q = (λ i → q i .fst) , (λ i → q i .snd)

    inner : is-hlevel (S n) Σ-Path
    inner = Σ-is-hlevel (S n) (ahl a₁ a₂) λ p → PathP-is-hlevel (bhl a₂)

×-is-hlevel : (n : Nat) → is-hlevel n A → is-hlevel n B → is-hlevel n (A × B)
×-is-hlevel n ahl bhl = Σ-is-hlevel n ahl (λ _ → bhl)

Lift-is-hlevel : ∀ {v} (n : Nat) → is-hlevel n A → is-hlevel n (Lift v A)
Lift-is-hlevel Z c .center = liftℓ (c .center)
Lift-is-hlevel Z c .paths (liftℓ a) i = liftℓ (c .paths a i)
Lift-is-hlevel (S Z) p (liftℓ a) (liftℓ b) i = liftℓ (p a b i)
Lift-is-hlevel {v = v} (S (S n)) hl (liftℓ a) (liftℓ b) =
  retract→is-hlevel (S n) fwd bwd (λ _ → refl) (Lift-is-hlevel (S n) (hl a b))
  where
    fwd : Lift v (a ≡ b) → liftℓ a ≡ liftℓ b
    fwd (liftℓ p) i = liftℓ (p i)

    bwd : liftℓ a ≡ liftℓ b → Lift v (a ≡ b)
    bwd q = liftℓ (λ i → q i .lower)
```

Additional h-level utilities.

```agda

is-groupoid : ∀ {ℓ} → Type ℓ → Type ℓ
is-groupoid = is-hlevel 3


-- nType: bundled n-truncated types (the n-type classifier)

record nType ℓ n : Type₊ ℓ where
  no-eta-equality
  field
    ∣_∣   : Type ℓ
    is-tr : is-hlevel n ∣_∣

{-# INLINE nType.constructor #-}

PathP-is-hlevel'
  : ∀ {ℓ} {A : I → Type ℓ} {n} {x : A i0} {y : A i1}
  → ((i : I) → is-hlevel (S n) (A i)) → is-hlevel n (PathP A x y)
PathP-is-hlevel' hl = PathP-is-hlevel (hl i1)

equiv→is-hlevel
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : Nat)
  → A ≃ B → is-hlevel n A → is-hlevel n B
equiv→is-hlevel n e =
  retract→is-hlevel n (Equiv.fwd e) (Equiv.inv e) (Equiv.counit e)

is-prop-×
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → is-prop A → is-prop B → is-prop (A × B)
is-prop-× aprop bprop (a , b) (a' , b') i = aprop a a' i , bprop b b' i

is-prop-equiv
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → A ≃ B → is-prop B → is-prop A
is-prop-equiv e bprop x y = p
  where
    module E = Equiv e
    p : x ≡ y
    p = sym (E.unit x) ∙ ap E.inv (bprop (E.fwd x) (E.fwd y)) ∙ E.unit y

singl-contr-in-contr
  : ∀ {ℓ} {A : Type ℓ}
  → is-contr A → (x : A) → is-contr (Σ y ∶ A , x ≡ y)
singl-contr-in-contr c x .center = x , refl
singl-contr-in-contr c x .paths (y , p) = Σ-prop-path (is-contr→is-set c x) p

subst-prop
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'}
  → is-prop A → ∀ a → P a → ∀ b → P b
subst-prop {P = P} prop a pa b = subst P (prop a b) pa

contr→contr-fiber
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) → is-contr A → is-contr B
  → ∀ b → is-contr (Σ a ∶ A , f a ≡ b)
contr→contr-fiber {A = A} f acontr bcontr b =
  prop-inhabited→is-contr fiber-is-prop fiber-inhabited
  where
    β : (x : A) → is-prop (f x ≡ b)
    β x f g = is-contr→is-set bcontr _ _ f g

    fiber-is-prop : is-prop (Σ a ∶ A , f a ≡ b)
    fiber-is-prop (a₁ , p₁) (a₂ , p₂) =
      Σ-prop-path β (is-contr→is-prop acontr a₁ a₂)

    fiber-inhabited : Σ a ∶ A , f a ≡ b
    fiber-inhabited = acontr .center , is-contr→is-prop bcontr _ _
```

H-level closure under function types and ordering.

```agda

→-is-prop
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → is-prop B → is-prop (A → B)
→-is-prop bprop = Π-is-prop (λ _ → bprop)

Π-is-set
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → ((x : A) → is-set (B x))
  → is-set ((x : A) → B x)
Π-is-set bset f g =
  retract→is-hlevel 1 funext happly (λ _ → refl)
    (Π-is-prop (λ x → bset x (f x) (g x)))

→-is-set
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → is-set B → is-set (A → B)
→-is-set bset = Π-is-set (λ _ → bset)

Σ-is-set
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → is-set A → ((x : A) → is-set (B x))
  → is-set (Σ B)
Σ-is-set aset bset = Σ-is-hlevel 2 aset bset

is-hlevel-<
  : ∀ {ℓ} {A : Type ℓ} {n m : Nat}
  → n < m → is-hlevel n A → is-hlevel m A
is-hlevel-< suc      hl = is-hlevel-suc hl
is-hlevel-< (step p) hl = is-hlevel-suc (is-hlevel-< p hl)

is-hlevel-≤
  : ∀ {ℓ} {A : Type ℓ} {n m : Nat}
  → n ≤ m → is-hlevel n A → is-hlevel m A
is-hlevel-≤ suc      hl = hl
is-hlevel-≤ (step p) hl = is-hlevel-< p hl
```


Proposition utilities.

```agda

is-prop→Path-is-contr
  : ∀ {ℓ} {A : Type ℓ}
  → is-prop A → (x y : A) → is-contr (x ≡ y)
is-prop→Path-is-contr aprop x y =
  prop-inhabited→is-contr (is-prop→is-set aprop x y) (aprop x y)

retract→is-prop
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) (g : B → A)
  → is-left-inverse f g
  → is-prop A → is-prop B
retract→is-prop f g r aprop = retract→is-hlevel 1 f g r aprop
```
