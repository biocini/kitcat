Lane Biocini
February 2025

Wild Categories with Families: categorical semantics for dependent type theory.

References:
- Dybjer (1996), "Internal Type Theory"
- Castellan, Clairambault, Dybjer (2019), "Categories with Families"
- Capriotti, Kraus (2017), "Univalent Higher Categories via Complete Semi-Segal Types"

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Cwf where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel
open import Core.Kan hiding (assoc; unitl; unitr)
open import Core.Transport
open import Core.Equiv

open import Cat.Base

private variable
  u v w w' : Level

record Typed-terms (C : precategory u v) (w w' : Level) : Type (u ⊔ v ⊔ w ₊ ⊔ w' ₊) where
  no-eta-equality
  private module C = precategory C
  open C using (ob; hom; _⨾_; idn)

  field
    Ty    : ob → Type w
    _[_]  : ∀ {Γ Δ} → Ty Δ → hom Γ Δ → Ty Γ
    Tm    : (Γ : ob) → Ty Γ → Type w'
    _⟨_⟩  : ∀ {Γ Δ A} → Tm Δ A → (σ : hom Γ Δ) → Tm Γ (A [ σ ])

  field
    [id]  : ∀ {Γ} {A : Ty Γ} → A [ idn ] ≡ A
    [⨾]   : ∀ {Β Γ Δ} {A : Ty Δ} {σ : hom Γ Δ} {τ : hom Β Γ}
          → A [ τ ⨾ σ ] ≡ A [ σ ] [ τ ]

  field
    ⟨id⟩  : ∀ {Γ} {A : Ty Γ} {a : Tm Γ A}
          → PathP (λ i → Tm Γ ([id] {A = A} i)) (a ⟨ idn ⟩) a
    ⟨⨾⟩   : ∀ {Β Γ Δ} {A : Ty Δ} {a : Tm Δ A} {σ : hom Γ Δ} {τ : hom Β Γ}
          → PathP (λ i → Tm Β ([⨾] {A = A} {σ} {τ} i)) (a ⟨ τ ⨾ σ ⟩) (a ⟨ σ ⟩ ⟨ τ ⟩)

{-# INLINE Typed-terms.constructor #-}

record Context-ext {u v w w'} (C : precategory u v) (T : Typed-terms C w w') : Type (u ⊔ v ⊔ w ⊔ w') where
  no-eta-equality
  private module C = precategory C
  open C using (ob; hom; _⨾_; idn)
  open Typed-terms T

  field
    _⦂_ : (Γ : ob) → Ty Γ → ob
  infixl 5 _⦂_

  field
    p     : ∀ {Γ} {A : Ty Γ} → hom (Γ ⦂ A) Γ
    q     : ∀ {Γ} {A : Ty Γ} → Tm (Γ ⦂ A) (A [ p ])
    ⟨_,_⟩ : ∀ {Γ Δ} {A : Ty Δ} → (σ : hom Γ Δ) → Tm Γ (A [ σ ]) → hom Γ (Δ ⦂ A)
  infixr 4 ⟨_,_⟩

  field
    p-β   : ∀ {Γ Δ} {A : Ty Δ} {σ : hom Γ Δ} {t : Tm Γ (A [ σ ])}
          → ⟨ σ , t ⟩ ⨾ p ≡ σ
    q-β   : ∀ {Γ Δ} {A : Ty Δ} {σ : hom Γ Δ} {t : Tm Γ (A [ σ ])}
          → Σ eq ∶ ((A [ p ]) [ ⟨ σ , t ⟩ ] ≡ A [ σ ]) ,
              PathP (λ i → Tm Γ (eq i)) (q ⟨ ⟨ σ , t ⟩ ⟩) t
    ext-η : ∀ {Γ} {A : Ty Γ} → ⟨ p , q ⟩ ≡ idn {x = Γ ⦂ A}

{-# INLINE Context-ext.constructor #-}

record Wild-cwf u v w w' : Type (u ₊ ⊔ v ₊ ⊔ w ₊ ⊔ w' ₊) where
  no-eta-equality
  field
    ctx   : precategory u v
    typed : Typed-terms ctx w w'
    ext   : Context-ext ctx typed

  open precategory ctx public
  open Typed-terms typed public
  open Context-ext ext public

{-# INLINE Wild-cwf.constructor #-}

module type-coherence {u v w w'} (cwf : Wild-cwf u v w w') where
  open Wild-cwf cwf
  private module H = Cat ctx

  has-type-triangles : Type (u ⊔ v ⊔ w)
  has-type-triangles = ∀ {Γ Δ} (σ : hom Γ Δ) (A : Ty Δ)
    → [⨾] {A = A} {σ = σ} {τ = idn} ∙ [id]
    ≡ ap (A [_]) (H.idn.lneutral H.idn-is-eqv idem σ)

  has-type-pentagons : Type (u ⊔ v ⊔ w)
  has-type-pentagons = ∀ {Β Γ Δ Ε} (ρ : hom Β Γ) (σ : hom Γ Δ) (τ : hom Δ Ε) (A : Ty Ε)
    → A [ ρ ⨾ σ ⨾ τ ] ≡ A [ τ ] [ σ ] [ ρ ]

record 2-coh-wild-cwf u v w w' : Type (u ₊ ⊔ v ₊ ⊔ w ₊ ⊔ w' ₊) where
  no-eta-equality
  field cwf : Wild-cwf u v w w'
  open Wild-cwf cwf public
  open type-coherence cwf

  field
    ctx-2coh       : Cat.is-2-coherent ctx
    type-triangles : has-type-triangles
    type-pentagons : has-type-pentagons

{-# INLINE 2-coh-wild-cwf.constructor #-}

module pi-types {u v w w'} (cwf : Wild-cwf u v w w') where
  open Wild-cwf cwf

  record has-Pi : Type (u ⊔ v ⊔ w ⊔ w') where
    no-eta-equality
    field
      Pi   : ∀ {Γ} (A : Ty Γ) → Ty (Γ ⦂ A) → Ty Γ
      Pi[] : ∀ {Γ Δ} {A : Ty Δ} {B : Ty (Δ ⦂ A)} {σ : hom Γ Δ}
           → Pi A B [ σ ] ≡ Pi (A [ σ ]) (B [ ⟨ p ⨾ σ , subst (Tm _) (sym [⨾]) q ⟩ ])
      lam  : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⦂ A)} → Tm (Γ ⦂ A) B → Tm Γ (Pi A B)
      app  : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⦂ A)} → Tm Γ (Pi A B) → Tm (Γ ⦂ A) B
      Pi-β : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⦂ A)} {b : Tm (Γ ⦂ A) B} → app (lam b) ≡ b
      Pi-η : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⦂ A)} {f : Tm Γ (Pi A B)} → lam (app f) ≡ f

  {-# INLINE has-Pi.constructor #-}

module sigma-types {u v w w'} (cwf : Wild-cwf u v w w') where
  open Wild-cwf cwf

  record has-Sigma : Type (u ⊔ v ⊔ w ⊔ w') where
    no-eta-equality
    field
      Σ'   : ∀ {Γ} (A : Ty Γ) → Ty (Γ ⦂ A) → Ty Γ
      Σ[]  : ∀ {Γ Δ} {A : Ty Δ} {B : Ty (Δ ⦂ A)} {σ : hom Γ Δ}
           → Σ' A B [ σ ] ≡ Σ' (A [ σ ]) (B [ ⟨ p ⨾ σ , subst (Tm _) (sym [⨾]) q ⟩ ])
      pair : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⦂ A)}
           → (a : Tm Γ A) → Tm Γ (B [ ⟨ idn , subst (Tm Γ) (sym [id]) a ⟩ ]) → Tm Γ (Σ' A B)
      fst' : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⦂ A)} → Tm Γ (Σ' A B) → Tm Γ A
      snd' : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⦂ A)}
           → (s : Tm Γ (Σ' A B)) → Tm Γ (B [ ⟨ idn , subst (Tm Γ) (sym [id]) (fst' s) ⟩ ])
      Σ-β₁ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⦂ A)} {a : Tm Γ A}
               {b : Tm Γ (B [ ⟨ idn , subst (Tm Γ) (sym [id]) a ⟩ ])}
           → fst' (pair a b) ≡ a
      Σ-η  : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⦂ A)} {s : Tm Γ (Σ' A B)}
           → pair (fst' s) (snd' s) ≡ s

  {-# INLINE has-Sigma.constructor #-}

module identity-types {u v w w'} (cwf : Wild-cwf u v w w') where
  open Wild-cwf cwf

  Id-Motive : ∀ {Γ} (A : Ty Γ) → Type w
  Id-Motive {Γ} A = Ty (Γ ⦂ A ⦂ A [ p ])

  record has-Id : Type (u ⊔ v ⊔ w ⊔ w') where
    no-eta-equality
    field
      Id    : ∀ {Γ} {A : Ty Γ} → Tm Γ A → Tm Γ A → Ty Γ
      Id[]  : ∀ {Γ Δ} {A : Ty Δ} {a b : Tm Δ A} {σ : hom Γ Δ}
            → Id a b [ σ ] ≡ Id (a ⟨ σ ⟩) (b ⟨ σ ⟩)
      refl' : ∀ {Γ} {A : Ty Γ} (a : Tm Γ A) → Tm Γ (Id a a)

  {-# INLINE has-Id.constructor #-}
```
