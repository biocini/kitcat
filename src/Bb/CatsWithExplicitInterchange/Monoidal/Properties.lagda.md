Lane Biocini
July 2026

The comparison of the two presentations of the level-0 axioms: the
archived record is equivalent to the redeveloped one together with
pointwise agreement of its two interchange fields. `unpin` reads the
archive's single field as both of the record's, projecting the pull
fiber from its spine; `pin⁺`/`pin⁻` keep one field and re-assemble
the spine over it by `spine-tail`. The equivalence's forward map is
`unpin` with the diagonal's agreement `refl`; the backward map is
`pin⁺`, discarding the agreement; each round trip is a record line
whose only moving components are a propositional fill in the
contractibility coordinate — `is-contr` of a fixed type is a
proposition — and, on the paired side, the based contraction of the
agreement coordinate into the second interchange field.

Below the comparison sits the flank boundary: the vanishing of `ω`
on either unit line, and the theorem that it forces the unitor
agreement types. The unitor chain consumes an interchange path only
through `⊗₀-emb-comp-op` at unit-flank arguments, so the vanishing
hypotheses rebuild each absorption cell across the choice of field
by congruence; the two unitor σ-lines then compare inside the
propositional representability fiber, whose set-ness identifies
them over the rebuilt absorption, and the `fst`-shadow of the
comparison line is constant. `ω-trace` is the self-discrepancy slid
along the pairing and read back through the same fiber — the
canonical balancing candidate, extracted rather than posited.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Monoidal.Properties where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp; move-r)
open import Core.Transport.J using (J)
open import Core.Transport.Properties using (is-contr-is-prop; is-prop→is-set)
open import Core.Equiv.Base using (_≃_; iso→equiv)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Monoidal
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy as Legacy

module _ {o h} {C : category o h} where

  interchange-agree : monoidal-axioms₀ C → Type o
  interchange-agree M₀ =
    (A B : M.⊗₀-composite)
    (U : M.is-⊗₀-representable A) (V : M.is-⊗₀-representable B)
    → M.ι⁺ {A} {B} U V ≡ M.ι⁻ {A} {B} U V
    where module M = monoidal-axioms₀ M₀
```

## The constructors

```agda
  unpin : Legacy.monoidal-axioms₀ C → monoidal-axioms₀ C
  unpin L = record
    { I = M.I
    ; ⊗₀-emb = M.⊗₀-emb
    ; ι⁺ = M.⊗₀-interchange♭
    ; ι⁻ = M.⊗₀-interchange♭
    ; ⊗₀-pull-contr = θ.⊗₀-pull-contr
    ; ⊗₀-unit = M.⊗₀-unit }
    where
      module M = Legacy.monoidal-axioms₀ L
      module θ = Legacy.theory₀ L

  pin⁺ : monoidal-axioms₀ C → Legacy.monoidal-axioms₀ C
  pin⁺ M₀ = record
    { I = M.I
    ; ⊗₀-emb = M.⊗₀-emb
    ; ⊗₀-interchange♭ = M.ι⁺
    ; ⊗₀-spine-contr = θ.over-interchange.⊗₀-spine-contr M.ι⁺-pt
    ; ⊗₀-unit = M.⊗₀-unit }
    where
      module M = monoidal-axioms₀ M₀
      module θ = theory₀ M₀

  pin⁻ : monoidal-axioms₀ C → Legacy.monoidal-axioms₀ C
  pin⁻ M₀ = record
    { I = M.I
    ; ⊗₀-emb = M.⊗₀-emb
    ; ⊗₀-interchange♭ = M.ι⁻
    ; ⊗₀-spine-contr = θ.over-interchange.⊗₀-spine-contr M.ι⁻-pt
    ; ⊗₀-unit = M.⊗₀-unit }
    where
      module M = monoidal-axioms₀ M₀
      module θ = theory₀ M₀
```

## The equivalence

```agda
  axioms₀-compare
    : Legacy.monoidal-axioms₀ C
    ≃ (Σ M ∶ monoidal-axioms₀ C , interchange-agree M)
  axioms₀-compare = iso→equiv to fro ret sec
    where
    to : Legacy.monoidal-axioms₀ C
       → Σ M ∶ monoidal-axioms₀ C , interchange-agree M
    to L = unpin L , λ A B U V → refl

    fro : (Σ M ∶ monoidal-axioms₀ C , interchange-agree M)
        → Legacy.monoidal-axioms₀ C
    fro (M , _) = pin⁺ M

    ret : ∀ L → fro (to L) ≡ L
    ret L i = record
      { I = M.I
      ; ⊗₀-emb = M.⊗₀-emb
      ; ⊗₀-interchange♭ = M.⊗₀-interchange♭
      ; ⊗₀-spine-contr = λ x y →
          is-contr-is-prop _
            (θN.over-interchange.⊗₀-spine-contr N.ι⁺-pt x y)
            (M.⊗₀-spine-contr x y) i
      ; ⊗₀-unit = M.⊗₀-unit }
      where
      module M = Legacy.monoidal-axioms₀ L
      module N = monoidal-axioms₀ (unpin L)
      module θN = theory₀ (unpin L)

    sec : ∀ Me → to (fro Me) ≡ Me
    sec (M , e) i =
      record
        { I = Mm.I
        ; ⊗₀-emb = Mm.⊗₀-emb
        ; ι⁺ = Mm.ι⁺
        ; ι⁻ = λ {A} {B} U V → e A B U V i
        ; ⊗₀-pull-contr = λ x y →
            is-contr-is-prop _
              (θP.⊗₀-pull-contr x y)
              (Mm.⊗₀-pull-contr x y) i
        ; ⊗₀-unit = Mm.⊗₀-unit }
      , λ A B U V j → e A B U V (i ∧ j)
      where
      module Mm = monoidal-axioms₀ M
      module θP = Legacy.theory₀ (pin⁺ M)
```

## The flank boundary

```agda
module _ {o h} {C : category o h} (M₀ : monoidal-axioms₀ C) where
  private module C = category C
  open monoidal-axioms₀ M₀
  open theory₀ M₀

  ω-vanish-l : Type o
  ω-vanish-l = (t : C.ob) → ω-pt I t ≡ refl

  ω-vanish-r : Type o
  ω-vanish-r = (l : C.ob) → ω-pt l I ≡ refl

  private
    vanish→agree : {x y : C.ob} → ω-pt x y ≡ refl → ι⁺-pt x y ≡ ι⁻-pt x y
    vanish→agree {x} {y} v =
      move-r (ι⁺-pt x y) (ι⁻-pt x y) refl v ∙ Path.unitl (ι⁻-pt x y)

    absorb-l-path
      : ω-vanish-l → ∀ r
      → over-interchange.⊗₀-absorb-l ι⁺-pt r
      ≡ over-interchange.⊗₀-absorb-l ι⁻-pt r
    absorb-l-path v r i =
      ( sym (⊗₀-comp-eq-pre I r)
      ∙ ( sym (⊗₀-unit (I ⊗₀ r))
        ∙ ap ⊗₀-ev (⊗₀-emb-comp I r ∙ vanish→agree (v r) i)
        ∙ ap (⊗₀-post r) (⊗₀-unit I)))
      ∙ ⊗₀-unit r

    absorb-r-path
      : ω-vanish-r → ∀ l
      → over-interchange.⊗₀-absorb-r ι⁺-pt l
      ≡ over-interchange.⊗₀-absorb-r ι⁻-pt l
    absorb-r-path v l i =
        sym ( sym (⊗₀-comp-eq-pre l I)
            ∙ ( sym (⊗₀-unit (l ⊗₀ I))
              ∙ ap ⊗₀-ev (⊗₀-emb-comp l I ∙ vanish→agree (v l) i)
              ∙ ap (⊗₀-post I) (⊗₀-unit l)))
      ∙ ⊗₀-unit l

    ▾₀-idn-path
      : ω-vanish-l → (F : ⊗₀-composite)
      → over-interchange.▾₀-idn ι⁺-pt F ≡ over-interchange.▾₀-idn ι⁻-pt F
    ▾₀-idn-path v F i = funext λ (l , r) →
      ap (λ t → F (l , t)) (absorb-l-path v r i)

    ⊗₀-idn-▴-path
      : ω-vanish-r → (F : ⊗₀-composite)
      → over-interchange.⊗₀-idn-▴ ι⁺-pt F ≡ over-interchange.⊗₀-idn-▴ ι⁻-pt F
    ⊗₀-idn-▴-path v F i = funext λ (l , r) →
      ap (λ t → F (t , r)) (absorb-r-path v l i)

    ⊗₀-emb-idn-absorb-path
      : ω-vanish-l → ω-vanish-r → (x : C.ob)
      → over-interchange.⊗₀-emb-idn-absorb ι⁺-pt x
      ≡ over-interchange.⊗₀-emb-idn-absorb ι⁻-pt x
    ⊗₀-emb-idn-absorb-path vl vr x i =
      vanish→agree (vl x) i ∙ ⊗₀-idn-▴-path vr (⊗₀-emb x) i

  flank-vanish→unitr-agreement : ω-vanish-l → unitr-agreement
  flank-vanish→unitr-agreement v x =
      ap (ap fst)
        (is-prop→is-set (is-⊗₀-representable-prop (⊗₀-emb x)) _ _
          (unitors.unitr-σ●₀ ι⁺-pt x)
          (κ ∙ unitors.unitr-σ●₀ ι⁻-pt x))
    ∙ ap-comp fst κ (unitors.unitr-σ●₀ ι⁻-pt x)
    ∙ Path.unitl (unitors.⊗₀-unitr ι⁻-pt x)
    where
    κ : ((⊗₀-nrm x ●₀ ⊗₀-nrm I) ↝ over-interchange.▾₀-idn ι⁺-pt (⊗₀-emb x))
      ≡ ((⊗₀-nrm x ●₀ ⊗₀-nrm I) ↝ over-interchange.▾₀-idn ι⁻-pt (⊗₀-emb x))
    κ i = (⊗₀-nrm x ●₀ ⊗₀-nrm I) ↝ ▾₀-idn-path v (⊗₀-emb x) i

  flank-vanish→unitl-agreement : ω-vanish-l → ω-vanish-r → unitl-agreement
  flank-vanish→unitl-agreement vl vr x =
      ap (ap fst)
        (is-prop→is-set (is-⊗₀-representable-prop (⊗₀-emb x)) _ _
          (unitors.unitl-σ●₀ ι⁺-pt x)
          (κ ∙ unitors.unitl-σ●₀ ι⁻-pt x))
    ∙ ap-comp fst κ (unitors.unitl-σ●₀ ι⁻-pt x)
    ∙ Path.unitl (unitors.⊗₀-unitl ι⁻-pt x)
    where
    κ : ((⊗₀-nrm I ●₀ ⊗₀-nrm x) ↝ over-interchange.⊗₀-emb-idn-absorb ι⁺-pt x)
      ≡ ((⊗₀-nrm I ●₀ ⊗₀-nrm x) ↝ over-interchange.⊗₀-emb-idn-absorb ι⁻-pt x)
    κ i = (⊗₀-nrm I ●₀ ⊗₀-nrm x) ↝ ⊗₀-emb-idn-absorb-path vl vr x i

  ω-trace : (x : C.ob) → x ⊗₀ x ≡ x ⊗₀ x
  ω-trace x =
    ap fst (is-⊗₀-representable-prop _
      ((⊗₀-nrm x ●₀ ⊗₀-nrm x) ↝ ω-pt x x)
      (⊗₀-nrm x ●₀ ⊗₀-nrm x))
```

## Pointwise to ♭

The nontrivial directions of the comparison between the two
presentations of an interchange axiom: J-towers over the fibers of
the embeddings, agreeing with their inputs at normal forms only
propositionally. Nothing on the spine routes through them — the
records' fields are the ♭ forms and instances prove them in that
shape; these closures are the material a presentation-equivalence
theorem consumes. Stated over the raw embeddings, so either field
of either record instantiates them.

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
