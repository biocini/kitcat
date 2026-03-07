Univalence: the equivalence between paths and equivalences.

This module uses `--cubical` (not `--erased-cubical`) because the Glue type
primitives require full cubical. Modules importing univalence can still use
`--erased-cubical`.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Core.Univalence where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Sub
open import Core.Transport
open import Core.Equiv
open import Core.Glue
open import Core.Composite using (_≡⟨_⟩_; _∎)
open Core.Kan.Path using (unitl; unitr; invl; invr; assoc)

private variable
  u v w : Level
  A B C : Type u

```

## Path to equivalence

Transport along a path between types is an equivalence (proved in
Core.Transport.Properties). Here we package it as `idtoeqv`.

```agda
idtoeqv : A ≡ B → A ≃ B
idtoeqv p = transport p , transport-equiv p

-- Synonym
path→equiv : A ≡ B → A ≃ B
path→equiv = idtoeqv

-- idtoeqv of refl is the identity equivalence
idtoeqv-refl : idtoeqv refl ≡ aut {A = A}
idtoeqv-refl {A} i .fst a = transport-refl a i
idtoeqv-refl {A} i .snd = is-prop→PathP (λ i → is-equiv-is-prop (λ a → transport-refl a i))
  (transport-equiv refl) id-equiv i
```

## Equivalence to path (ua)

The univalence axiom: equivalences give paths. This uses Glue types.

```agda
ua : A ≃ B → A ≡ B
ua {A} {B} e i = Glue B λ where
  (i = i0) → A , e
  (i = i1) → B , aut
```

## ua of identity

```agda
-- ua of the identity equivalence is refl
ua-equiv : ua (aut {A = A}) ≡ refl
ua-equiv {A} i j = Glue A λ where
  (i = i1) → A , aut
  (j = i0) → A , aut
  (j = i1) → A , aut
```

## Computation rules

The ua function computes correctly: transporting along ua e applies e.

Transport along `ua e` computes to the forward map of the equivalence. This is
a fundamental property of the Glue type. The computation works as follows:

1. `transport (ua e) a = coe01 (λ i → ua e i) a`
2. The Glue type's transp reduces to: unglue applied to the coerced element
3. At i=i1, unglue extracts the B component, which equals `e .fst a`
4. The final coercion through B is identity since B is constant

```agda
ua-β : (e : A ≃ B) (a : A) → transport (ua e) a ≡ e .fst a
ua-β {A} {B} e a = transport-refl (e .fst a)

-- ua is a retraction of idtoeqv
ua-η : (p : A ≡ B) → ua (idtoeqv p) ≡ p
ua-η {A} {B} p = J (λ X q → ua (idtoeqv q) ≡ q) ua-refl p
  where
  ua-refl : ua (idtoeqv refl) ≡ refl
  ua-refl = ap ua idtoeqv-refl ∙ ua-equiv
```

## Singleton contractibility for equivalences

The type of equivalences out of A, pointed at (A, aut), is contractible.

```agda
private
  -- The type of equivalences out of A, pointed at (A, aut), is contractible.
  -- Credit: Adapted from 1lab's univalence proof
  module _ {u : Level} (A : Type u) where
    ≃-singl-contr : is-contr (Σ X ∶ Type u , A ≃ X)
    ≃-singl-contr .center = A , aut
    ≃-singl-contr .paths (B , e) i = ua e i , p i , q i
      where
      -- The type-equivalence pair at each boundary
      Te : (i : I) → Partial (∂ i) (Σ T ∶ Type u , T ≃ B)
      Te i (i = i0) = A , e
      Te i (i = i1) = B , aut

      -- The forward function over ua: id at i=i0, e.fst at i=i1
      -- At boundary i=i0: ua e i0 = A, so we need A → A (identity)
      -- At boundary i=i1: ua e i1 = B, so we need A → B (e.fst)
      p : PathP (λ i → A → ua e i) id (e .fst)
      p i a = glue {φ = ∂ i} {Te = Te i}
        (λ { (i = i0) → a ; (i = i1) → e .fst a })
        (inS (e .fst a))

      -- The is-equiv component: use is-prop→PathP since is-equiv is a prop
      q : PathP (λ i → is-equiv (p i)) id-equiv (e .snd)
      q = is-prop→PathP (λ i → is-equiv-is-prop (p i)) id-equiv (e .snd)
```

## Univalence theorem

```agda
-- idtoeqv (ua e) ≡ e
-- This follows from contractibility of the equivalence singleton
idtoeqv-ua : (e : A ≃ B) → idtoeqv (ua e) ≡ e
idtoeqv-ua {A} {B} e = p
  where
  singl-path : (A , aut) ≡ (B , e)
  singl-path = ≃-singl-contr A .paths (B , e)

  eqv-pathp : PathP (λ i → A ≃ singl-path i .fst) aut e
  eqv-pathp i = singl-path i .snd

  p : idtoeqv (ua e) ≡ e
  p i .fst a = ua-β e a i
  p i .snd = is-prop→PathP
    (λ i → is-equiv-is-prop (λ a → ua-β e a i))
    (idtoeqv (ua e) .snd)
    (e .snd)
    i

-- The main theorem: idtoeqv is an equivalence
univalence : is-equiv (idtoeqv {A = A} {B = B})
univalence = qinv.to-equiv (qinv idtoeqv ua ua-η idtoeqv-ua)

-- Bundled form
Univalence : (A ≡ B) ≃ (A ≃ B)
Univalence = idtoeqv , univalence
```

## Derived operations

```agda
-- Equivalence induction
equiv-ind
  : ∀ {w} (P : (B : Type u) → A ≃ B → Type w)
  → P A aut
  → (B : Type u) (e : A ≃ B) → P B e
equiv-ind {A = A} P prefl B e = transport (λ i → P (ua e i) (path i)) prefl
  where
  path : PathP (λ i → A ≃ ua e i) aut e
  path i = ≃-singl-contr A .paths (B , e) i .snd
```

## Path algebra with ua

The univalence axiom gives us a rich algebra between paths in the universe
and equivalences. This section develops the key compatibility lemmas.

```agda
-- Transport along a composed path is composition of transports
-- This is a fundamental lemma relating path composition and transport
transport-∙ : {A B C : Type u} (p : A ≡ B) (q : B ≡ C) (a : A)
            → transport (p ∙ q) a ≡ transport q (transport p a)
transport-∙ {A} {B} {C} p q a =
  J {x = A}
    (λ B' p' → (q' : B' ≡ C) → transport (p' ∙ q') a ≡ transport q' (transport p' a))
    base
    p q
  where
  -- Base case: p = refl, so we need transport (refl ∙ q) a ≡ transport q (transport refl a)
  base : (q' : A ≡ C) → transport (refl ∙ q') a ≡ transport q' (transport refl a)
  base q' = ap (λ r → transport r a) (Path.unitl q') ∙ sym (ap (λ x → transport q' x) (transport-refl a))

-- ua respects equivalence composition
-- Credit: Adapted from 1lab's proof
ua-∙e : (e : A ≃ B) (f : B ≃ C) → ua (e ∙e f) ≡ ua e ∙ ua f
ua-∙e {A} {B} {C} e f = sym (ap ua eqv-composite-path) ∙ ua-η (ua e ∙ ua f)
  where
  -- Show that idtoeqv (ua e ∙ ua f) ≡ e ∙e f
  fwd-agree : (a : A) → transport (ua e ∙ ua f) a ≡ (e ∙e f) .fst a
  fwd-agree a = transport-∙ (ua e) (ua f) a
              ∙ ap (transport (ua f)) (ua-β e a)
              ∙ ua-β f (e .fst a)

  eqv-composite-path : idtoeqv (ua e ∙ ua f) ≡ e ∙e f
  eqv-composite-path i .fst a = fwd-agree a i
  eqv-composite-path i .snd = is-prop→PathP
    (λ i → is-equiv-is-prop (λ a → fwd-agree a i))
    (idtoeqv (ua e ∙ ua f) .snd)
    ((e ∙e f) .snd)
    i

-- ua respects symmetry/inverse
ua-esym : (e : A ≃ B) → ua (esym e) ≡ sym (ua e)
ua-esym {A} {B} e =
  ua (esym e)                       ≡⟨ sym (Path.unitr (ua (esym e))) ⟩
  ua (esym e) ∙ refl                ≡⟨ ap (ua (esym e) ∙_) (sym (Path.invr (ua e))) ⟩
  ua (esym e) ∙ (ua e ∙ sym (ua e)) ≡⟨ Path.assoc (ua (esym e)) (ua e) (sym (ua e)) ⟩
  (ua (esym e) ∙ ua e) ∙ sym (ua e) ≡⟨ ap (_∙ sym (ua e)) (sym (ua-∙e (esym e) e)) ⟩
  ua (esym e ∙e e) ∙ sym (ua e)     ≡⟨ ap (λ x → ua x ∙ sym (ua e)) esym-invr ⟩
  ua aut ∙ sym (ua e)             ≡⟨ ap (_∙ sym (ua e)) ua-equiv ⟩
  refl ∙ sym (ua e)                 ≡⟨ Path.unitl (sym (ua e)) ⟩
  sym (ua e) ∎
  where
  -- esym e ∙e e ≡ equiv
  esym-invr : esym e ∙e e ≡ aut
  esym-invr i .fst b = Equiv.counit e b i
  esym-invr i .snd = is-prop→PathP
    (λ i → is-equiv-is-prop (λ b → Equiv.counit e b i))
    ((esym e ∙e e) .snd)
    id-equiv
    i

-- Characterization of subst along ua
-- This shows that subst along ua e is the same as transporting along ap P (ua e)
subst-ua : (P : Type u → Type v) (e : A ≃ B) (x : P A)
         → subst P (ua e) x ≡ transport (ap P (ua e)) x
subst-ua P e x = refl

-- ua of the identity is refl (already have ua-equiv, this is an alias)
ua-id : ua (aut {A = A}) ≡ refl
ua-id = ua-equiv
```
