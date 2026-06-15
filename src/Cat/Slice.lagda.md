The slice category C/X over an object X in a virtual category C.
Objects are morphisms into X, and morphisms are commuting triangles
using composite-witness formulation.

The second component of `hom/X` stores `emb fA ≡ tgt(k)` where
`tgt(k) = λ w a v b → emb k w a v (noy fB v b)`. This expresses
`k ⨾ fB => fA` at the emb level. Both `(tgt k, q)` pairs live
in the forward singleton `Singl (emb fA)`, which is contractible
by `Singl-contr`.

STUCK: `hom/X-path` (deriving a path in `hom/X` from a path
on the first component) requires a PathP in the family
`λ i → emb fA ≡ tgt fB (α i)`. The singl `Σ y, emb fA ≡ y`
is contractible and hence a set, but the FIBERS of
`fst : Singl (emb fA) → CodType` at each point are path
spaces, which are not propositional unless the codomain is a
set. Without `hom` being a set, the PathP cannot be filled
generically — there exist (higher) counterexamples where
`hom` has non-trivial loop structure.

This same obstruction affects the original `k ⨾ fB ≡ fA`
formulation: PathP in `λ i → α i ⨾ fB ≡ fA` also requires
hom to be a set. The composite-witness formulation does not
resolve this.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

open import Cat.Type

module Cat.Slice {o h} (C : category o h) where

open Virtual C

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
  using (is-prop→PathP; coe01; Singl-contr; contr-ind;
         transport-refl; is-contr→PathP; is-contr-is-prop;
         is-contr→loop-is-refl; SinglP-contr; weak-funext;
         subst; is-prop→is-set)
open import Core.Sub using (outS; inS)
open import Core.Equiv.Base
  using (is-equiv; eqv-fibers; is-contr-equiv)

```

## Slice data

The `tgt` helper computes `λ w a v b → emb k w a v (noy fB v b)`,
the target function for the composite `k ⨾ fB`.

```agda

module Slice {X : ob} where

  ob/X : Type (o ⊔ h)
  ob/X = Σ A ∶ ob , hom A X

  private
    tgt
      : ∀ {A B}
      → hom B X → hom A B
      → ∀ w → hom w A → ∀ v → hom X v → hom w v
    tgt fB k w a v b = emb k w a v (noy fB v b)

  hom/X : ob/X → ob/X → Type (o ⊔ h)
  hom/X (A , fA) (B , fB) =
    Σ k ∶ hom A B
    , emb fA ≡ (λ w a v b → tgt fB k w a v b)

```

## Identity

The composite `idn ⨾ fA` has target `tgt fA idn`, which equals
`emb fA` by interchange and absorption.

```agda

  private
    absorb-idn
      : ∀ {A} (fA : hom A X)
      → (λ w a v b → tgt fA idn w a v b) ≡ emb fA
    absorb-idn fA = emb-ext λ w a v b →
      interchange idn fA w a v b
      ∙ ap (λ t → emb fA w t v b) (absorb-r a)

  idn/X : ∀ {a : ob/X} → hom/X a a
  idn/X {_ , fA} = idn , sym (absorb-idn fA)

```

## Cast between formulations

The composite-witness `emb fA ≡ tgt fB k` is interconvertible
with `k ⨾ fB ≡ fA` via `emb-inj` and `emb-composite`.

```agda

  private
    cast-path : ∀ {A B} {fA : hom A X} {fB : hom B X}
      (k : hom A B)
      → emb fA ≡ (λ w a v b → tgt fB k w a v b)
      → k ⨾ fB ≡ fA
    cast-path k p = emb-inj-ext (emb-composite-ext k _ ∙ sym p)

```

## Emb construction

The ternary composition in C/X. Given `(k, p) : hom/X a b`,
`(m, q) : hom/X w a`, and `(n, r) : hom/X b z`, the result is
`(emb k _ m _ n, pf)` where the composite witness `pf` chains
through `q`, `p`, and `r` at the hom level via the cast and
associativity.

```agda

  private
    emb-as-comp
      : ∀ {A B W Z}
        (k : hom A B) (m : hom W A) (n : hom B Z)
      → emb k W m Z n ≡ (m ⨾ k) ⨾ n
    emb-as-comp k m n =
      emb-yon k _ m _ n
      ∙ ap (emb idn _ (yon k _ m) _)
            (sym (yon-eval n))
      ∙ interchange idn n _ (yon k _ m) _ idn
      ∙ ap (λ t → emb n _ t _ idn)
            (absorb-r (yon k _ m))
      ∙ sym (comp-eq (yon k _ m) n)
      ∙ ap (_⨾ n) (sym (comp-eq m k))

    slice-chain
      : ∀ {A B W Z}
        {fA : hom A X} {fB : hom B X}
        {fW : hom W X} {fZ : hom Z X}
        (k : hom A B) (m : hom W A) (n : hom B Z)
      → k ⨾ fB ≡ fA
      → m ⨾ fA ≡ fW
      → n ⨾ fZ ≡ fB
      → (emb k W m Z n) ⨾ fZ ≡ fW
    slice-chain k m n p' q' r' =
      ap (_⨾ _) (emb-as-comp k m n)
      ∙ assoc (m ⨾ k) n _
      ∙ ap ((m ⨾ k) ⨾_) r'
      ∙ assoc m k _
      ∙ ap (m ⨾_) p'
      ∙ q'

  emb/X
    : ∀ {a b : ob/X} → hom/X a b
    → ∀ w → hom/X w a
    → ∀ z → hom/X b z
    → hom/X w z
  emb/X {A , fA} {B , fB} (k , p)
    (W , fW) (m , q) (Z , fZ) (n , r) =
    emb k W m Z n
    , sym (ap emb chain) ∙ emb-composite-ext _ _
    where
      chain : (emb k W m Z n) ⨾ fZ ≡ fW
      chain = slice-chain k m n
        (cast-path k p)
        (cast-path m q)
        (cast-path n r)

  noy/X
    : ∀ {a b : ob/X} → hom/X a b
    → ∀ z → hom/X b z → hom/X a z
  noy/X {a} f z h = emb/X f a idn/X z h

  yon/X
    : ∀ {a b : ob/X} → hom/X a b
    → ∀ w → hom/X w a → hom/X w b
  yon/X {b = b} f w g = emb/X f w g b idn/X

```

## Path helper

STUCK: the PathP in `λ i → emb fA ≡ tgt fB (α i)` cannot be
filled without `hom` being a set. The singl `Singl (emb fA)` is
contractible, giving a path between `(tgt fB k₁, q₁)` and
`(tgt fB k₂, q₂)`, but the fst of this singl path need not
coincide with `ap (tgt fB) α` — both are paths in the codomain
type from `tgt fB k₁` to `tgt fB k₂`, and they are equal only
when the codomain is a set.

```agda

  hom/X-path
    : ∀ {a b : ob/X} {f g : hom/X a b}
    → f .fst ≡ g .fst → f ≡ g
  hom/X-path
    {_ , fA} {_ , fB} {k₁ , q₁} {k₂ , q₂} α i =
    α i , pathp i
    where
      Emb : Type (o ⊔ h)
      Emb = ∀ w → hom w _ → ∀ v → hom _ v → hom w v

      S : is-contr (Σ y ∶ Emb , emb fA ≡ y)
      S = Singl-contr (emb fA)

      pathp
        : PathP (λ i → emb fA
          ≡ (λ w a v b → tgt fB (α i) w a v b))
          q₁ q₂
      pathp = {! !}

```

## Interchange

Both sides of `interchange/X` have the same first component by
the base `interchange`. The snd PathP requires `hom/X-path`.

```agda

  interchange/X
    : ∀ {a b c : ob/X}
      (f : hom/X a b) (g : hom/X b c)
      w (dw : hom/X w a) z (dz : hom/X c z)
    → emb/X f w dw z (noy/X g z dz)
    ≡ emb/X g w (yon/X f w dw) z dz
  interchange/X
    {_ , fA} {_ , fB} {_ , fC}
    (fk , fp) (gk , gp)
    (_ , fW) (m , q) (_ , fZ) (n , r) =
    hom/X-path (interchange fk gk _ m _ n)

```

## Yon-eval

```agda

  yon-eval/X
    : ∀ {a b : ob/X} (f : hom/X a b)
    → yon/X f a idn/X ≡ f
  yon-eval/X {A , fA} {B , fB} (k , p) =
    hom/X-path (yon-eval k)

```

## Compose-contr

```agda

  compose-contr/X
    : ∀ {a b c : ob/X}
      (f : hom/X a b) (g : hom/X b c)
    → is-contr
        (Σ s ∶ hom/X a c
        , emb/X s
          ≡ (λ w dw z dz →
              emb/X f w dw z (noy/X g z dz)))
  compose-contr/X
    {a@(A , fA)} {b@(B , fB)} {c@(C , fC)}
    f@(fk , fp) g@(gk , gp) = {! !}

```

## Unit

```agda

  unit/X
    : ∀ {a : ob/X} →
      Σ e ∶ hom/X a a
      , ( (∀ {z} → is-equiv
              (λ (h : hom/X a z) →
                emb/X e a e z h))
        × (∀ {w} → is-equiv
              (λ (g : hom/X w a) →
                emb/X e w g a e)))
      × (emb/X e a e a e ≡ e)
  unit/X = {! !}

```

## Assembly

```agda

  -- slice : category (o ⊔ h) (o ⊔ h)
  -- slice .category.ob = ob/X
  -- slice .category.hom = hom/X
  -- slice .category.emb f = emb/X f
  -- slice .category.unit = unit/X
  -- slice .category.compose-contr = compose-contr/X
  -- slice .category.interchange f g w dw z dz =
  --   interchange/X f g w dw z dz
  -- slice .category.yon-eval = yon-eval/X

```
