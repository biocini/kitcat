Lane Biocini
July 2026

Presentation-comparison material for the monoidal axioms, at both
grades. The records' interchange fields are the ♭ forms and
instances prove them in that shape; the pointwise-to-♭ closures
below are the nontrivial directions of the comparison between the
two possible presentations of each axiom — J-towers over the
fibers of the embeddings, agreeing with their inputs at normal
forms only propositionally (the J lottery that ruled the fields).
Nothing on the spine routes through them: they live here as the
material a presentation-equivalence theorem would consume.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Properties where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Transport.J using (J)

open import Cat.Type
open import Cat.Monoidal
```

## The object grade

```agda
module _ {o h} (C : category o h) (I : category.ob C)
  (⊗₀-emb : category.ob C → tensor-virtual.⊗₀-composite C I)
  where

  open tensor-virtual C I
  open tensor-representable C I ⊗₀-emb
  private module C = category C

  ⊗₀-interchange♭-from
    : ((x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y)
    → {A B : ⊗₀-composite}
    → is-⊗₀-representable A → is-⊗₀-representable B
    → A ▿₀ B ≡ A ▵₀ B
  ⊗₀-interchange♭-from ι {B = B} (m , p) (n , q) =
    J (λ F' _ → F' ▿₀ B ≡ F' ▵₀ B)
      (J (λ G' _ → ⊗₀-emb m ▿₀ G' ≡ ⊗₀-emb m ▵₀ G') (ι m n) q)
      p
```

## The morphism grade

One dependent J per side, each over the witness's total path —
the base lines paired with the characterization, re-bent as a
single path in the graph Σ of `⊗₁-composite`.

```agda
module _ {o h} (C : category o h) (I : category.ob C)
  (⊗₀-emb : category.ob C → tensor-virtual.⊗₀-composite C I)
  (⊗₁-emb : ∀ {x x'} → category.hom C x x'
          → tensor-virtual₁.⊗₁-composite C I (⊗₀-emb x) (⊗₀-emb x'))
  where

  open tensor-virtual C I
  open tensor-virtual₁ C I
  open tensor-representable C I ⊗₀-emb
  open tensor-representable₁ C I ⊗₀-emb ⊗₁-emb
  private module C = category C

  ⊗₁-interchange♭-from
    : (ι : ∀ {A B : ⊗₀-composite}
         → is-⊗₀-representable A → is-⊗₀-representable B
         → A ▿₀ B ≡ A ▵₀ B)
    → (∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
       → PathP (λ i → ⊗₁-composite (ι (⊗₀-nrm x) (⊗₀-nrm y) i)
                                    (ι (⊗₀-nrm x') (⊗₀-nrm y') i))
               (⊗₁-emb φ ▾₁ ψ) (φ ▴₁ ⊗₁-emb ψ))
    → ∀ {A A' B B' : ⊗₀-composite}
        {U : is-⊗₀-representable A} {U' : is-⊗₀-representable A'}
        {V : is-⊗₀-representable B} {V' : is-⊗₀-representable B'}
        {η : ⊗₁-composite A A'} {ζ : ⊗₁-composite B B'}
    → ⊗₁-wit U U' η → ⊗₁-wit V V' ζ
    → PathP (λ i → ⊗₁-composite (ι U V i) (ι U' V' i))
            (η ▿₁ ζ) (η ▵₁ ζ)
  ⊗₁-interchange♭-from ι ι₁
    {U = m , p} {m' , p'} {n , q} {n' , q'} {ζ = ζ} (σ , P) (τ , Q) =
    J {A = Σ T ∶ ⊗₀-composite × ⊗₀-composite , ⊗₁-composite (T .fst) (T .snd)}
      (λ T t →
        PathP (λ i → ⊗₁-composite (ι (m , λ j → t j .fst .fst) (n , q) i)
                                   (ι (m' , λ j → t j .fst .snd) (n' , q') i))
              (T .snd ▿₁ ζ) (T .snd ▵₁ ζ))
      (J {A = Σ T ∶ ⊗₀-composite × ⊗₀-composite , ⊗₁-composite (T .fst) (T .snd)}
         (λ T t →
           PathP (λ i → ⊗₁-composite (ι (⊗₀-nrm m) (n , λ j → t j .fst .fst) i)
                                      (ι (⊗₀-nrm m') (n' , λ j → t j .fst .snd) i))
                 (⊗₁-emb σ ▿₁ T .snd) (⊗₁-emb σ ▵₁ T .snd))
         (ι₁ σ τ)
         (λ i → (q i , q' i) , Q i))
      (λ i → (p i , p' i) , P i)
```
