Properties and lemmas for lists.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.List.Properties where

open import Core.Type hiding (id)
open import Core.Data.Nat.Type using (Nat; S; Z)
open import Core.Base
  using (_≡_; refl; ap; sym; is-contr; center; paths; _∧_)
open import Core.Kan using (_∙_)
open import Core.Transport using (subst)
open import Core.Equiv using (_≃_; Equiv; esym; is-contr-equiv)
open import Core.IdSys
  using ( is-based-identity-system; to-path; to-path-over
        ; Ids-based→equiv )
open import Core.Data.Sigma using (_×_; Σ; _,_)
open import Core.Data.Empty using (⊥; ex-falso)
open import Core.Data.List.Type
open import Core.Data.List.Base

open import Core.Trait.Trunc
  using ( is-hlevel; is-contr→is-hlevel; is-prop→is-hlevel-suc
        ; ×-is-hlevel )
open import Core.HLevel.Base using (equiv→is-hlevel)

private variable
  u v w : Level
  A B C : Type u

```

## map

```agda

module map where
  id : (xs : List A) → map (λ x → x) xs ≡ xs
  id [] = refl
  id (x ∷ xs) i = x ∷ id xs i

  comp
    : (f : B → C) (g : A → B) (xs : List A)
    → map (f ∘ g) xs ≡ (map f ∘ map g) xs
  comp f g [] = refl
  comp f g (x ∷ xs) i = f (g x) ∷ comp f g xs i

  cat
    : (f : A → B) (xs ys : List A)
    → map f (xs ++ ys) ≡ (map f xs ++ map f ys)
  cat f [] ys = refl
  cat f (x ∷ xs) ys i = f x ∷ cat f xs ys i

```

## cat (append)

```agda

module cat where
  unitr : (xs : List A) → (xs ++ []) ≡ xs
  unitr [] = refl
  unitr (x ∷ xs) i = x ∷ unitr xs i

  assoc
    : (xs ys zs : List A)
    → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  assoc [] ys zs = refl
  assoc (x ∷ xs) ys zs i = x ∷ assoc xs ys zs i

```

## concat

```agda

module concat where
  cat
    : (xss yss : List (List A))
    → concat (xss ++ yss) ≡ (concat xss ++ concat yss)
  cat [] yss = refl
  cat (xs ∷ xss) yss =
    ap (xs ++_) (cat xss yss)
    ∙ sym (cat.assoc xs (concat xss) (concat yss))

```

## concatMap

```agda

module concatMap where
  cat
    : (f : A → List B) (xs ys : List A)
    → concatMap f (xs ++ ys)
      ≡ (concatMap f xs ++ concatMap f ys)
  cat f xs ys =
    ap concat (map.cat f xs ys)
    ∙ concat.cat (map f xs) (map f ys)

  singleton
    : (f : A → List B) (x : A)
    → concatMap f (x ∷ []) ≡ f x
  singleton f x = cat.unitr (f x)

  unitr : (xs : List A) → concatMap (_∷ []) xs ≡ xs
  unitr [] = refl
  unitr (x ∷ xs) i = x ∷ unitr xs i

  assoc
    : (f : A → List B) (g : B → List C) (xs : List A)
    → concatMap g (concatMap f xs)
      ≡ concatMap (λ x → concatMap g (f x)) xs
  assoc f g [] = refl
  assoc f g (x ∷ xs) =
    cat g (f x) (concatMap f xs)
    ∙ ap (concatMap g (f x) ++_) (assoc f g xs)

```

## H-levels

Lists are (S (S n))-truncated when their element type is.

```agda

cons-injective
  : ∀ {u} {A : Type u} {x y : A} {xs ys : List A}
  → x ∷ xs ≡ y ∷ ys → (x ≡ y) × (xs ≡ ys)
cons-injective {x = x} {xs = xs} p =
  ap head' p , ap tail' p
  where
    head' : List _ → _
    head' []      = x
    head' (z ∷ _) = z

    tail' : List _ → List _
    tail' []       = xs
    tail' (_ ∷ zs) = zs

List-is-hlevel
  : ∀ {u} {A : Type u} (n : Nat)
  → is-hlevel (S (S n)) A → is-hlevel (S (S n)) (List A)
List-is-hlevel {A = A} n ahl [] [] =
  is-contr→is-hlevel (S n) nil-path-contr
  where
    Code : List A → Type
    Code []      = ⊤
    Code (_ ∷ _) = ⊥

    nil-ids : is-based-identity-system ([] {A = A}) Code tt
    nil-ids .to-path {b = []}    _ = refl
    nil-ids .to-path {b = _ ∷ _} ()
    nil-ids .to-path-over {b = []}    _ = refl
    nil-ids .to-path-over {b = _ ∷ _} ()

    ⊤-is-contr : is-contr ⊤
    ⊤-is-contr .center = tt
    ⊤-is-contr .paths _ = refl

    nil-path-contr : is-contr ([] ≡ [])
    nil-path-contr = is-contr-equiv (Ids-based→equiv nil-ids) ⊤-is-contr

List-is-hlevel n ahl [] (y ∷ ys) =
  is-prop→is-hlevel-suc {n = n}
    (λ p _ → ex-falso (subst discrim p tt))
  where
    discrim : List _ → Type
    discrim []      = ⊤
    discrim (_ ∷ _) = ⊥
List-is-hlevel n ahl (x ∷ xs) [] =
  is-prop→is-hlevel-suc {n = n}
    (λ p _ → ex-falso (subst discrim p tt))
  where
    discrim : List _ → Type
    discrim []      = ⊥
    discrim (_ ∷ _) = ⊤
List-is-hlevel n ahl (x ∷ xs) (y ∷ ys) =
  equiv→is-hlevel (S n)
    (esym List-cons-path-equiv) inner
  module ListCons where
    Code : List _ → Type _
    Code []       = Lift _ ⊥
    Code (z ∷ zs) = (x ≡ z) × (xs ≡ zs)

    cons-ids
      : is-based-identity-system
          (x ∷ xs) Code (refl , refl)
    cons-ids .to-path {b = []}     (liftℓ ())
    cons-ids .to-path {b = z ∷ zs} (p , q) i =
      p i ∷ q i
    cons-ids .to-path-over {b = []}     (liftℓ ())
    cons-ids .to-path-over {b = z ∷ zs} (p , q) i =
      (λ j → p (i ∧ j)) , (λ j → q (i ∧ j))

    List-cons-path-equiv
      : ((x ∷ xs) ≡ (y ∷ ys)) ≃ ((x ≡ y) × (xs ≡ ys))
    List-cons-path-equiv = Ids-based→equiv cons-ids

    inner : is-hlevel (S n) ((x ≡ y) × (xs ≡ ys))
    inner = ×-is-hlevel (S n) (ahl x y)
      (List-is-hlevel n ahl xs ys)
```
