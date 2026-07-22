Lane Biocini
July 2026

The free scaffolding of a braided monoidal structure. The
associator is free because reassociation keeps `⊗₀-emb`'s target
fixed: both bracketings of a nested composite represent the same
ternary operation, so the associator is a `fst`-shadow inside one
propositional fiber. A braiding is different: it *moves* the
target. `A ▿₀ B` and `B ▿₀ A` are genuinely distinct composites,
so the braiding needs one new datum — a path between them — but
half of that path is already the interchange field. The
genuinely-new field is the flank swap `A ▵₀ B ≡ B ▿₀ A`: moving
the swapped factor from the over flank to the under flank.
Interchange carries `A ▿₀ B ≡ A ▵₀ B`, the swap carries the rest,
and the braid composes them.

Both fields take the ♭ form, at witness arguments — the record's
field, an instance's proof, and a builder's input are one shape —
and the morphism grade displaces over the object grade's lines
exactly as `⊗₁-interchange♭` displaces over `⊗₀-interchange♭`.
The pointwise forms are the `nrm`-shadows: against embedded
factors the ternary orders collapse to the one-sided composites
definitionally.

Invertibility is free: the object braiding is a path in `ob`, so
its symmetry is its inverse — there is no separate axiom, unlike
the classical definition where invertibility is an imposed
condition on a natural transformation. The hexagon coherences are
*not* free; they live in `Cat.Monoidal.Legacy.Hexagon`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Legacy.Braid where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan

open import Cat.Type
open import Cat.Monoidal.Legacy
open import Cat.Monoidal.Legacy.Bifunctor
```

## The braided record

One field per grade, each in the shape its consumers project:
the object-level swap at representability witnesses, and the
morphism-level swap as a `PathP` over the object-level lines at
displaced witnesses. The braids are the composites with the
interchange fields, `comp-pathp₂` playing `∙` one grade up.

```agda
record braided {o h} {C : category o h} (M : monoidal C)
  : Type (o ⊔ h) where
  open monoidal M
  private module C = category C

  field
    ⊗₀-flank-swap♭
      : {A B : ⊗₀-composite}
      → is-⊗₀-representable A → is-⊗₀-representable B
      → A ▵₀ B ≡ B ▿₀ A

  ⊗₀-flank-swap : (x y : C.ob) → x ▴₀ ⊗₀-emb y ≡ ⊗₀-emb y ▾₀ x
  ⊗₀-flank-swap x y = ⊗₀-flank-swap♭ (⊗₀-nrm x) (⊗₀-nrm y)

  ⊗₀-braid♭
    : {A B : ⊗₀-composite}
    → is-⊗₀-representable A → is-⊗₀-representable B
    → A ▿₀ B ≡ B ▿₀ A
  ⊗₀-braid♭ U V = ⊗₀-interchange♭ U V ∙ ⊗₀-flank-swap♭ U V

  field
    ⊗₁-flank-swap♭
      : ∀ {A A' B B' : ⊗₀-composite}
          {U : is-⊗₀-representable A} {U' : is-⊗₀-representable A'}
          {V : is-⊗₀-representable B} {V' : is-⊗₀-representable B'}
          {η : ⊗₁-composite A A'} {ζ : ⊗₁-composite B B'}
      → ⊗₁-wit U U' η → ⊗₁-wit V V' ζ
      → PathP (λ i → ⊗₁-composite (⊗₀-flank-swap♭ U V i)
                                   (⊗₀-flank-swap♭ U' V' i))
              (η ▵₁ ζ) (ζ ▿₁ η)

  ⊗₁-flank-swap
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
    → PathP (λ i → ⊗₁-composite (⊗₀-flank-swap x y i)
                                 (⊗₀-flank-swap x' y' i))
            (φ ▴₁ ⊗₁-emb ψ) (⊗₁-emb ψ ▾₁ φ)
  ⊗₁-flank-swap φ ψ = ⊗₁-flank-swap♭ (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ)

  ⊗₁-braid♭
    : ∀ {A A' B B' : ⊗₀-composite}
        {U : is-⊗₀-representable A} {U' : is-⊗₀-representable A'}
        {V : is-⊗₀-representable B} {V' : is-⊗₀-representable B'}
        {η : ⊗₁-composite A A'} {ζ : ⊗₁-composite B B'}
    → ⊗₁-wit U U' η → ⊗₁-wit V V' ζ
    → PathP (λ i → ⊗₁-composite (⊗₀-braid♭ U V i)
                                 (⊗₀-braid♭ U' V' i))
            (η ▿₁ ζ) (ζ ▿₁ η)
  ⊗₁-braid♭ {U = U} {U'} {V} {V'} Û V̂ =
    comp-pathp₂ ⊗₁-composite
      (⊗₀-interchange♭ U V) (⊗₀-flank-swap♭ U V)
      (⊗₀-interchange♭ U' V') (⊗₀-flank-swap♭ U' V')
      (⊗₁-interchange♭ Û V̂) (⊗₁-flank-swap♭ Û V̂)
```

## The derived braidings

The object braiding is a `fst`-shadow, exactly the unitor idiom:
the pairing `U ●₀ V`, slid along the braid to the swapped
composite, inhabits the same propositional fiber as `V ●₀ U`, and
the sealed σ-line between them projects the braid on objects. One
grade up, `⊗₁-wit-σ[_,_]` at the sealed lines threads the `↝̂`-slid
pairing to the swapped pairing, and the `fst`-shadow is the
morphism braiding — naturality is its type.

```agda
module braid-theory {o h} {C : category o h} {M : monoidal C}
  (B : braided M) where
  open monoidal M
  open theory₁ M
  open braided B
  private module C = category C

  opaque
    braid-σ●₀
      : ∀ {F G : ⊗₀-composite}
        (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
      → ((U ●₀ V) ↝ ⊗₀-braid♭ U V) ≡ (V ●₀ U)
    braid-σ●₀ U V = is-⊗₀-representable-prop _ ((U ●₀ V) ↝ ⊗₀-braid♭ U V) (V ●₀ U)

  braid●₀
    : ∀ {F G : ⊗₀-composite}
      (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
    → U .fst ⊗₀ V .fst ≡ V .fst ⊗₀ U .fst
  braid●₀ U V = ap fst (braid-σ●₀ U V)

  ⊗₀-braid : (x y : C.ob) → x ⊗₀ y ≡ y ⊗₀ x
  ⊗₀-braid x y = braid●₀ (⊗₀-nrm x) (⊗₀-nrm y)

  braid-σ●₁
    : ∀ {F F' G G' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
        {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
      (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ)
    → PathP (λ i → ⊗₁-wit (braid-σ●₀ U V i) (braid-σ●₀ U' V' i)
                          (ζ ▿₁ η))
            ((Û ●₁ V̂) ↝̂ ⊗₁-braid♭ Û V̂) (V̂ ●₁ Û)
  braid-σ●₁ {U = U} {U'} {V} {V'} Û V̂ =
    ⊗₁-wit-σ[ braid-σ●₀ U V , braid-σ●₀ U' V' ]
      ((Û ●₁ V̂) ↝̂ ⊗₁-braid♭ Û V̂) (V̂ ●₁ Û)

  braid●₁
    : ∀ {F F' G G' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
        {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
      (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ)
    → PathP (λ i → C.hom (braid●₀ U V i) (braid●₀ U' V' i))
            (Û .fst ⊗₁ V̂ .fst) (V̂ .fst ⊗₁ Û .fst)
  braid●₁ Û V̂ i = braid-σ●₁ Û V̂ i .fst

  ⊗₁-braid
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
    → PathP (λ i → C.hom (⊗₀-braid x y i) (⊗₀-braid x' y' i))
            (φ ⊗₁ ψ) (ψ ⊗₁ φ)
  ⊗₁-braid φ ψ = braid●₁ (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ)
```
