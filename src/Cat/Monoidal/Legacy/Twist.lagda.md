Lane Biocini
July 2026

Perturbing the flat interchange of a `monoidal-axioms₀` by a
loop family `ω` at witness arguments conjugates the `absorb-coh`
defect. The twisted structure `Mω` shares `I`, `⊗₀-emb`, and
`⊗₀-unit` with the base outright, and its spine re-assembles
from the base's interchange-free pull fiber extended by the
contractible tail over the twisted line — so the derived tensor,
its pre-side comparison, and every cell not routed through
interchange reduce identically for both structures, and only the
interchange-routed cells differ, by exactly the loop family.

The absorption coherence is the irreducible content: the
left-hand side is transported unchanged, while the right-hand
interchange side acquires the evaluated loop
`ζ = happly (ω (⊗₀-nrm I) (⊗₀-nrm x)) (I , r)` as a conjugating
factor, so any `absorb-coh` witness on `Mω` forces `ζ ≡ refl`.
The triviality hypothesis reshapes with the derivation: the new
absorption chain routes the spine center through
`⊗₀-comp-eq-post I t` at every `t`, so where the old form pinned
one diagonal point, the hypothesis here is that the loop family
evaluates trivially at the identity context along the left-unit
line — the forced loop sits at an arbitrary right context `r`,
strictly beyond it.

The morphism level never enters: with contractible homs the
indiscrete builder extends `Mω` to a full `monoidal` untouched,
which is what makes the defect a counterexample against the
whole bundle and not an artifact of level 0.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Legacy.Twist where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp; conj-cancel)

open import Cat.Type
open import Cat.Groupoid using (spine-tail)
open import Cat.Monoidal.Legacy
open import Cat.Monoidal.Legacy.Indiscrete
```

## The two absorption coherence sides

```agda
module _ {o h} {C : category o h} where
  private module C = category C

  module absorb-coh (N₀ : monoidal-axioms₀ C) where
    open monoidal-axioms₀ N₀
    open theory₀ N₀

    lhs : (x r : C.ob) → ⊗₀-pre I (⊗₀-pre x r) ≡ ⊗₀-pre x r
    lhs x r = ⊗₀-absorb-l (⊗₀-pre x r)

    rhs : (x r : C.ob) → ⊗₀-pre I (⊗₀-pre x r) ≡ ⊗₀-pre x r
    rhs x r =
        happly (⊗₀-interchange I x) (I , r)
      ∙ ap (λ t → ⊗₀-emb x (t , r)) (⊗₀-absorb-r I)
```

## The base structure and its twist

The twisted spine: the pull fiber never mentions interchange, so
the base center extends along `spine-tail` over the twisted
line, and the twisted composite comparisons are the base's with
the loop appended — definitionally on the pre side, up to the
spine's 2-cell on the post side.

```agda
  module twist (M₀ : monoidal-axioms₀ C) where
    open monoidal-axioms₀ M₀
    open theory₀ M₀

    module _ (ω : ∀ {A B : ⊗₀-composite}
                → is-⊗₀-representable A → is-⊗₀-representable B
                → A ▵₀ B ≡ A ▵₀ B) where

      ι♭ω : ∀ {A B : ⊗₀-composite}
          → is-⊗₀-representable A → is-⊗₀-representable B
          → A ▿₀ B ≡ A ▵₀ B
      ι♭ω U V = ⊗₀-interchange♭ U V ∙ ω U V

      ιω : (a b : C.ob) → ⊗₀-emb a ▾₀ b ≡ a ▴₀ ⊗₀-emb b
      ιω a b = ι♭ω (⊗₀-nrm a) (⊗₀-nrm b)

      private
        spine-contrω
          : (a b : C.ob)
          → is-contr (Σ k ∶ C.ob ,
              Σ p ∶ (⊗₀-emb k ≡ ⊗₀-emb a ▾₀ b) ,
              Σ q ∶ (⊗₀-emb k ≡ a ▴₀ ⊗₀-emb b) ,
                PathP (λ i → ⊗₀-emb k ≡ ιω a b i) p q)
        spine-contrω a b = reshape c
          where
            c = Σ-contr-contr (⊗₀-pull-contr a b)
                  λ (k , p) → spine-tail p (ιω a b)

            reshape
              : is-contr (Σ λ (k , p) →
                  Σ q ∶ (⊗₀-emb k ≡ a ▴₀ ⊗₀-emb b) ,
                    PathP (λ i → ⊗₀-emb k ≡ ιω a b i) p q)
              → is-contr (Σ k ∶ C.ob ,
                  Σ p ∶ (⊗₀-emb k ≡ ⊗₀-emb a ▾₀ b) ,
                  Σ q ∶ (⊗₀-emb k ≡ a ▴₀ ⊗₀-emb b) ,
                    PathP (λ i → ⊗₀-emb k ≡ ιω a b i) p q)
            reshape c' .center =
              c' .center .fst .fst , c' .center .fst .snd ,
              c' .center .snd .fst , c' .center .snd .snd
            reshape c' .paths (k , p , q , θ) i =
              φ i .fst .fst , φ i .fst .snd , φ i .snd .fst , φ i .snd .snd
              where φ = c' .paths ((k , p) , (q , θ))

      Mω : monoidal-axioms₀ C
      Mω .monoidal-axioms₀.I = I
      Mω .monoidal-axioms₀.⊗₀-emb = ⊗₀-emb
      Mω .monoidal-axioms₀.⊗₀-interchange♭ = ι♭ω
      Mω .monoidal-axioms₀.⊗₀-spine-contr = spine-contrω
      Mω .monoidal-axioms₀.⊗₀-unit = ⊗₀-unit

      private module Mω₀ = monoidal-axioms₀ Mω
      private module θω = theory₀ Mω
```

With contractible homs the twist extends to a full `monoidal`
through the indiscrete builder, morphism level untouched.

```agda
      twist-monoidal
        : (∀ {a b} → is-contr (C.hom a b))
        → monoidal C
      twist-monoidal hom-contr = indiscrete-monoidal hom-contr Mω
```

## Twist algebra

How the twisted derived cells relate to the base's. The pre-side
chain is shared definitionally; the post side carries the loop:
the twisted `⊗₀-emb-comp-op` is definitionally the base pre-side
comparison extended along the twisted line, so its `⊗₀-ev` image
splits as the base image conjugated by the evaluated loop, and
the spine's 2-cell `⊗₀-coh→∙` folds the interchange half back
into the base post-side comparison. The hypothesis `Hω` kills
the evaluated loop on the left-unit line, collapsing each
comparison to the base's.

```agda
      module _ (Hω : (t : C.ob)
                   → ap ⊗₀-ev (ω (⊗₀-nrm I) (⊗₀-nrm t)) ≡ refl) where

        private
          ev-comp-op-eq
            : (a b : C.ob)
            → ap ⊗₀-ev (ω (⊗₀-nrm a) (⊗₀-nrm b)) ≡ refl
            → ap ⊗₀-ev (Mω₀.⊗₀-emb-comp-op a b)
            ≡ ap ⊗₀-ev (⊗₀-emb-comp-op a b)
          ev-comp-op-eq a b h =
              ap-comp ⊗₀-ev (⊗₀-emb-comp a b) (ιω a b)
            ∙ ap (ap ⊗₀-ev (⊗₀-emb-comp a b) ∙_)
                 ( ap-comp ⊗₀-ev (⊗₀-interchange a b)
                     (ω (⊗₀-nrm a) (⊗₀-nrm b))
                 ∙ ap (ap ⊗₀-ev (⊗₀-interchange a b) ∙_) h
                 ∙ Path.unitr (ap ⊗₀-ev (⊗₀-interchange a b)) )
            ∙ sym (ap-comp ⊗₀-ev (⊗₀-emb-comp a b) (⊗₀-interchange a b))
            ∙ ap (ap ⊗₀-ev) (⊗₀-coh→∙ a b)

          comp-eq-post-eq
            : (a b : C.ob)
            → ap ⊗₀-ev (ω (⊗₀-nrm a) (⊗₀-nrm b)) ≡ refl
            → θω.⊗₀-comp-eq-post a b ≡ ⊗₀-comp-eq-post a b
          comp-eq-post-eq a b h =
            ap (λ c → sym (⊗₀-unit (a ⊗₀ b))
                    ∙ c ∙ ap (⊗₀-post b) (⊗₀-unit a))
               (ev-comp-op-eq a b h)

          absorb-l-eq : (t : C.ob) → θω.⊗₀-absorb-l t ≡ ⊗₀-absorb-l t
          absorb-l-eq t =
            ap (λ c → (sym (⊗₀-comp-eq-pre I t) ∙ c) ∙ ⊗₀-unit t)
               (comp-eq-post-eq I t (Hω t))

          absorb-r-eq : θω.⊗₀-absorb-r I ≡ ⊗₀-absorb-r I
          absorb-r-eq =
            ap (λ c → sym (sym (⊗₀-comp-eq-pre I I) ∙ c) ∙ ⊗₀-unit I)
               (comp-eq-post-eq I I (Hω I))

        module _ (x r : C.ob) where
          private
            α : ⊗₀-pre I (⊗₀-pre x r) ≡ ⊗₀-emb x (⊗₀-post I I , r)
            α = happly (⊗₀-interchange I x) (I , r)

            ζ : ⊗₀-emb x (⊗₀-post I I , r) ≡ ⊗₀-emb x (⊗₀-post I I , r)
            ζ = happly (ω (⊗₀-nrm I) (⊗₀-nrm x)) (I , r)

            β : ⊗₀-emb x (⊗₀-post I I , r) ≡ ⊗₀-pre x r
            β = ap (λ t → ⊗₀-emb x (t , r)) (⊗₀-absorb-r I)

            lhs-eq : absorb-coh.lhs Mω x r ≡ absorb-coh.lhs M₀ x r
            lhs-eq = absorb-l-eq (⊗₀-pre x r)

            rhs-expand : absorb-coh.rhs Mω x r ≡ α ∙ ζ ∙ β
            rhs-expand =
                ap (happly (ιω I x) (I , r) ∙_)
                   (ap (ap (λ t → ⊗₀-emb x (t , r))) absorb-r-eq)
              ∙ ap (_∙ β)
                   (ap-comp (λ F → F (I , r)) (⊗₀-interchange I x)
                     (ω (⊗₀-nrm I) (⊗₀-nrm x)))
              ∙ sym (Path.assoc α ζ β)

          reduce
            : ((a b : C.ob) → absorb-coh.lhs M₀ a b ≡ absorb-coh.rhs M₀ a b)
            → absorb-coh.lhs Mω x r ≡ absorb-coh.rhs Mω x r
            → happly (ω (⊗₀-nrm I) (⊗₀-nrm x)) (I , r) ≡ refl
          reduce cohM g =
            conj-cancel α β ζ
              (sym (cohM x r) ∙ sym lhs-eq ∙ g ∙ rhs-expand)
```

## The reduction theorem

A base coherence `cohM` and a hypothetical twisted coherence `g`
together force the loop `happly (ω (⊗₀-nrm I) (⊗₀-nrm x)) (I , r)`
to be `refl`, provided the loop family already evaluates
trivially at the identity context along the left-unit line.

```agda
      twist-reduces-to-omega
        : (Hω : (t : C.ob)
              → ap ⊗₀-ev (ω (⊗₀-nrm I) (⊗₀-nrm t)) ≡ refl)
        → ((a b : C.ob) → absorb-coh.lhs M₀ a b ≡ absorb-coh.rhs M₀ a b)
        → (x r : C.ob)
        → absorb-coh.lhs Mω x r ≡ absorb-coh.rhs Mω x r
        → happly (ω (⊗₀-nrm I) (⊗₀-nrm x)) (I , r) ≡ refl
      twist-reduces-to-omega Hω cohM x r g = reduce Hω x r cohM g
```
