Lane Biocini
July 2026

A monoidal category is a one-object bicategory. We present
its object-level structure natively, reading everything off a
ternary tensor embedding `tensor-emb : C.ob → C.ob → C.ob → C.ob`.
The proofs follow the same shapes as the ternary-composition
presentation of categories in `Cat.Type`, but stated directly
for the tensor rather than routed through any delooping.

The tensor unit `I`, the two representable actions `noy` and
`yon`, and the binary tensor `_⊗_` are all definable from
`tensor-emb`. The associator and unitors are projected from
contractible composition fibers exactly as `Cat.Type` derives
`assoc`, `unitl`, and `unitr`.

The correspondence with `Cat.Type` erases the two `Unit`
object indices of `category.emb`: every `hom _ _` becomes
`C.ob`, and the `∀ w`, `∀ v` binders vanish. Four-argument
emb functions collapse to two-argument tensor functions, and
`emb-ext`'s four-fold funext collapses to the two-fold
`tensor-emb-ext`. The tensor unit is unique in the weak sense
(`tensor-unit-is-prop`). Pentagon and triangle are deferred
to a later `Cat.Monoidal.Coherence` submodule.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal where

open import Core.Type
-- hiding I avoids the clash with the re-exported cubical
-- interval I; the monoidal unit is named I below.
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base using (contr-ind)
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding using (equiv→lc)

open import Cat.Type
```

## The monoidal record

The object-level structure is the ternary tensor `tensor-emb`
with its unit and the two composition axioms. The unit slot
gives `noy m r = tensor-emb m I r` (left factor at the unit)
and `yon m l = tensor-emb m l I` (right factor at the unit).

```agda
record monoidal {o h} (C : category o h) : Type₊ (o ⊔ h) where
  -- h is headroom for the C.hom-level fields of the
  -- morphism-level tensor (a later milestone).
  no-eta-equality
  private module C = Virtual C

  field
    tensor-emb : C.ob → C.ob → C.ob → C.ob
    tensor-unit
      : Σ i ∶ C.ob
      , (is-equiv (λ (r : C.ob) → tensor-emb i i r))
      × (is-equiv (λ (l : C.ob) → tensor-emb i l i))

  I : C.ob
  I = tensor-unit .fst

  noy : C.ob → C.ob → C.ob
  noy m r = tensor-emb m I r

  yon : C.ob → C.ob → C.ob
  yon m l = tensor-emb m l I

  field
    tensor-compose-contr
      : (x y : C.ob)
      → is-contr
          (fiber tensor-emb (λ l r → tensor-emb x l (noy y r)))
    tensor-interchange
      : (x y l r : C.ob)
      → tensor-emb x l (noy y r) ≡ tensor-emb y (yon x l) r
    tensor-yon-eval
      : (x : C.ob) → yon x I ≡ x

  tensor-unit-eqvl : is-equiv (λ (r : C.ob) → noy I r)
  tensor-unit-eqvl = tensor-unit .snd .fst

  tensor-unit-eqvr : is-equiv (λ (l : C.ob) → yon I l)
  tensor-unit-eqvr = tensor-unit .snd .snd

  tensor-yon-idpt : yon I I ≡ I
  tensor-yon-idpt = tensor-yon-eval I

  _⊗_ : C.ob → C.ob → C.ob
  x ⊗ y = tensor-compose-contr x y .center .fst
  infixr 40 _⊗_

  tensor-emb-composite
    : (x y : C.ob)
    → tensor-emb (x ⊗ y) ≡ (λ l r → tensor-emb x l (noy y r))
  tensor-emb-composite x y =
    tensor-compose-contr x y .center .snd
```

## Tensor operations and their laws

```agda
  tensor-emb-ext
    : {F G : C.ob → C.ob → C.ob}
    → (∀ l r → F l r ≡ G l r)
    → F ≡ G
  tensor-emb-ext h = funext λ l → funext λ r → h l r

  tensor-emb-comp-pt
    : (x y l r : C.ob)
    → tensor-emb (x ⊗ y) l r ≡ tensor-emb x l (noy y r)
  tensor-emb-comp-pt x y l r i =
    tensor-emb-composite x y i l r

  tensor-emb-yon-composite
    : (x y : C.ob)
    → tensor-emb (x ⊗ y) ≡ (λ l r → tensor-emb y (yon x l) r)
  tensor-emb-yon-composite x y =
    tensor-emb-composite x y
    ∙ tensor-emb-ext λ l r → tensor-interchange x y l r

  tensor-emb-yon-comp-pt
    : (x y l r : C.ob)
    → tensor-emb (x ⊗ y) l r ≡ tensor-emb y (yon x l) r
  tensor-emb-yon-comp-pt x y l r =
    tensor-emb-comp-pt x y l r ∙ tensor-interchange x y l r

  tensor-noy-composite
    : (y z r : C.ob)
    → noy (y ⊗ z) r ≡ noy y (noy z r)
  tensor-noy-composite y z r = tensor-emb-comp-pt y z I r

  tensor-yon-composite
    : (x y l : C.ob)
    → yon (x ⊗ y) l ≡ yon y (yon x l)
  tensor-yon-composite x y l =
    tensor-emb-comp-pt x y l I ∙ tensor-interchange x y l I

  tensor-emb-nest
    : (x y z l r : C.ob)
    → tensor-emb ((x ⊗ y) ⊗ z) l r
    ≡ tensor-emb x l (noy y (noy z r))
  tensor-emb-nest x y z l r =
    tensor-emb-comp-pt (x ⊗ y) z l r
    ∙ tensor-emb-comp-pt x y l (noy z r)

  tensor-emb-nest-ext
    : (x y z : C.ob)
    → tensor-emb ((x ⊗ y) ⊗ z)
    ≡ (λ l r → tensor-emb x l (noy y (noy z r)))
  tensor-emb-nest-ext x y z =
    tensor-emb-ext (tensor-emb-nest x y z)

  ⊗-comp-eq : (x y : C.ob) → x ⊗ y ≡ yon y x
  ⊗-comp-eq x y =
    sym (tensor-yon-eval (x ⊗ y))
    ∙ tensor-yon-composite x y I
    ∙ ap (yon y) (tensor-yon-eval x)

  ⊗-idem : I ⊗ I ≡ I
  ⊗-idem = ⊗-comp-eq I I ∙ tensor-yon-idpt
```

## Morphism-level tensor

The tensor acts on 2-cells (morphisms of `C`) in exact
parallel with the object level. `htensor-emb` is the
trifunctor action: three parallel 2-cells give a 2-cell
between the corresponding tensor objects. The unit-slot
specializations `hnoy` and `hyon` mirror `noy` and `yon`.
The three composition axioms are the object-level equations
`tensor-emb-comp-pt`, `tensor-interchange`, and
`tensor-yon-eval` displaced to `PathP`s over 2-cells, and
`htensor-bifunctor` links the horizontal tensor to the
vertical composite `C.⨾`.

These fields sit here, ahead of the unit-absorption lemmas,
because a record forbids `where`-clause definitions before
its last field.

```agda
  field
    htensor-emb
      : ∀ {m m'} (φ : C.hom m m')
          {l l'} (ψ : C.hom l l')
          {r r'} (χ : C.hom r r')
      → C.hom (tensor-emb m l r) (tensor-emb m' l' r')

  hnoy
    : ∀ {m m'} → C.hom m m'
    → ∀ {r r'} → C.hom r r'
    → C.hom (noy m r) (noy m' r')
  hnoy φ χ = htensor-emb φ (C.idn {I}) χ

  hyon
    : ∀ {m m'} → C.hom m m'
    → ∀ {l l'} → C.hom l l'
    → C.hom (yon m l) (yon m' l')
  hyon φ ψ = htensor-emb φ ψ (C.idn {I})

  field
    htensor-unit
      : (∀ {m m'} → is-equiv (λ (χ : C.hom m m') → hnoy (C.idn {I}) χ))
      × (∀ {l l'} → is-equiv (λ (ψ : C.hom l l') → hyon (C.idn {I}) ψ))

    htensor-compose-contr
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → is-contr
          ( Σ σ ∶ C.hom (x ⊗ y) (x' ⊗ y')
          , ( ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
              → PathP (λ i → C.hom (tensor-emb-comp-pt x  y  l  r  i)
                                   (tensor-emb-comp-pt x' y' l' r' i))
                      (htensor-emb σ α β)
                      (htensor-emb φ α (hnoy ψ β)) ) )

    htensor-interchange
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
          {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
      → PathP (λ i → C.hom (tensor-interchange x  y  l  r  i)
                           (tensor-interchange x' y' l' r' i))
              (htensor-emb φ α (hnoy ψ β))
              (htensor-emb ψ (hyon φ α) β)

    htensor-yon-eval
      : ∀ {x x'} (φ : C.hom x x')
      → PathP (λ i → C.hom (tensor-yon-eval x i) (tensor-yon-eval x' i))
              (hyon φ (C.idn {I}))
              φ

  _⊗ₕ_
    : ∀ {x x'} → C.hom x x'
    → ∀ {y y'} → C.hom y y'
    → C.hom (x ⊗ y) (x' ⊗ y')
  φ ⊗ₕ ψ = htensor-compose-contr φ ψ .center .fst
  infixr 40 _⊗ₕ_

  ⊗ₕ-comp-pt
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
    → PathP (λ i → C.hom (tensor-emb-comp-pt x  y  l  r  i)
                         (tensor-emb-comp-pt x' y' l' r' i))
            (htensor-emb (φ ⊗ₕ ψ) α β)
            (htensor-emb φ α (hnoy ψ β))
  ⊗ₕ-comp-pt φ ψ = htensor-compose-contr φ ψ .center .snd

  field
    htensor-bifunctor
      : ∀ {x x' x''} (φ₁ : C.hom x  x') (φ₂ : C.hom x' x'')
          {l l' l''} (α₁ : C.hom l  l') (α₂ : C.hom l' l'')
          {r r' r''} (β₁ : C.hom r  r') (β₂ : C.hom r' r'')
      → htensor-emb (φ₁ C.⨾ φ₂) (α₁ C.⨾ α₂) (β₁ C.⨾ β₂)
      ≡ htensor-emb φ₁ α₁ β₁ C.⨾ htensor-emb φ₂ α₂ β₂
```

## Unit absorption

Any object left- or right-tensored with the unit `I` is
absorbed. These lemmas use `where`, so they follow the last
field.

```agda
  noy-I-idem : (m : C.ob) → noy I (noy I m) ≡ noy I m
  noy-I-idem m =
    sym (subst (λ t → noy t m ≡ noy I (noy I m))
      ⊗-idem (tensor-noy-composite I I m))

  yon-I-idem : (l : C.ob) → yon I (yon I l) ≡ yon I l
  yon-I-idem l =
    sym (subst (λ t → yon t l ≡ yon I (yon I l))
      ⊗-idem (tensor-yon-composite I I l))

  absorb-l : (r : C.ob) → noy I r ≡ r
  absorb-l r = equiv→lc tensor-unit-eqvl (noy-I-idem r)

  absorb-r : (l : C.ob) → yon I l ≡ l
  absorb-r l = equiv→lc tensor-unit-eqvr (yon-I-idem l)
```

## Composable fiber and its eliminators

`tensor-composable-contr` restates `tensor-compose-contr`
with a pointwise equation. `tensor-emb-ind` eliminates any
`(s , q)` in the fiber back to the canonical center.

```agda
  tensor-composable-contr
    : (x y : C.ob)
    → is-contr
        (Σ s ∶ C.ob
        , ∀ l r → tensor-emb s l r ≡ tensor-emb x l (noy y r))
  tensor-composable-contr x y .center =
    x ⊗ y , tensor-emb-comp-pt x y
  tensor-composable-contr x y .paths (s , p) i =
    let ep = tensor-compose-contr x y .paths (s , tensor-emb-ext p)
    in ep i .fst , λ l r j → ep i .snd j l r

  tensor-emb-ind
    : ∀ {u} (x y : C.ob)
    → (P : (s : C.ob)
         → (∀ l r → tensor-emb s l r ≡ tensor-emb x l (noy y r))
         → Type u)
    → P (x ⊗ y) (tensor-emb-comp-pt x y)
    → ∀ s q → P s q
  tensor-emb-ind x y P base s q =
    contr-ind (tensor-composable-contr x y)
      (λ where (s , q) → P s q)
      base (s , q)

  ⊗-η
    : (x y : C.ob)
    → (s : C.ob)
    → (∀ l r → tensor-emb s l r ≡ tensor-emb x l (noy y r))
    → x ⊗ y ≡ s
  ⊗-η x y = tensor-emb-ind x y (λ s _ → x ⊗ y ≡ s) refl
```

## Embedding property

`tensor-emb-image-contr` shows the emb-fiber at any object is
contractible, via interchange and absorption.

```agda
  tensor-emb-image-contr
    : (x : C.ob)
    → is-contr
        (Σ s ∶ C.ob
        , ∀ l r → tensor-emb s l r ≡ tensor-emb x l r)
  tensor-emb-image-contr x = c'
    where
      c : is-contr
        (Σ s ∶ C.ob
        , ∀ l r → tensor-emb s l r ≡ tensor-emb I l (noy x r))
      c = tensor-composable-contr I x

      path
        : (λ l r → tensor-emb I l (noy x r))
        ≡ (λ l r → tensor-emb x l r)
      path = funext λ l → funext λ r →
        tensor-interchange I x l r
        ∙ ap (λ t → tensor-emb x t r) (absorb-r l)

      c' : is-contr
        (Σ s ∶ C.ob
        , ∀ l r → tensor-emb s l r ≡ tensor-emb x l r)
      c' = subst (λ T → is-contr
        (Σ s ∶ C.ob
        , ∀ l r → tensor-emb s l r ≡ T l r))
        path c

  tensor-emb-inj
    : {x y : C.ob}
    → (∀ l r → tensor-emb x l r ≡ tensor-emb y l r)
    → x ≡ y
  tensor-emb-inj {x} {y} pw =
    ap fst (sym p₁ ∙ p₂)
    where
      p₁ = tensor-emb-image-contr x .paths
        (x , λ _ _ → refl)
      p₂ = tensor-emb-image-contr x .paths
        (y , λ l r → sym (pw l r))

  tensor-emb-inj-ext
    : {x y : C.ob}
    → tensor-emb x ≡ tensor-emb y → x ≡ y
  tensor-emb-inj-ext p =
    tensor-emb-inj λ l r i → p i l r
```

## Yon and noy decomposition

```agda
  tensor-emb-yon
    : (x l r : C.ob)
    → tensor-emb x l r ≡ tensor-emb I (yon x l) r
  tensor-emb-yon x l r =
    ap (tensor-emb x l) (sym (absorb-l r))
    ∙ tensor-interchange x I l r

  tensor-emb-noy
    : (x l r : C.ob)
    → tensor-emb x l r ≡ tensor-emb I l (noy x r)
  tensor-emb-noy x l r =
    ap (λ t → tensor-emb x t r) (sym (absorb-r l))
    ∙ sym (tensor-interchange I x l r)
```

## Unit uniqueness

Any object that acts like a right tensor unit and is
idempotent under `yon` is uniquely the chosen unit `I`. The
argument is the Kraus chain: `yon e` squares to itself and is
idempotent, so it absorbs, forcing `e ≡ I`.

```agda
  tensor-unit-is-prop
    : (e : C.ob)
    → is-equiv (λ (l : C.ob) → tensor-emb e l e)
    → yon e e ≡ e
    → e ≡ I
  tensor-unit-is-prop e re idpt =
    sym (tensor-yon-eval e) ∙ yon-e-absorb I
    where
      e-idem : e ⊗ e ≡ e
      e-idem = ⊗-comp-eq e e ∙ idpt

      yon-e-idpt : (l : C.ob) → yon e (yon e l) ≡ yon e l
      yon-e-idpt l =
        sym (sym (ap (λ t → yon t l) e-idem)
          ∙ tensor-yon-composite e e l)

      yon-e-squared
        : (l : C.ob) → tensor-emb e l e ≡ yon e (yon e l)
      yon-e-squared l =
        tensor-emb-yon e l e
        ∙ sym (ap (tensor-emb I (yon e l)) (tensor-yon-eval e))
        ∙ tensor-interchange I e (yon e l) I
        ∙ ap (yon e) (absorb-r (yon e l))

      yon-e-absorb : (l : C.ob) → yon e l ≡ l
      yon-e-absorb l = equiv→lc re
        (yon-e-squared (yon e l)
        ∙ yon-e-idpt (yon e l)
        ∙ sym (yon-e-squared l))
```

## Coherent unit laws and associativity

The unit laws and associativity are projections from
contractible fibers.

```agda
  ⊗-unitr : (x : C.ob) → x ⊗ I ≡ x
  ⊗-unitr x =
    ap fst
      (is-contr→is-prop (tensor-emb-image-contr x) lhs rhs)
    where
      lhs : Σ s ∶ C.ob
          , ∀ l r → tensor-emb s l r ≡ tensor-emb x l r
      lhs = x ⊗ I
          , λ l r →
              tensor-emb-comp-pt x I l r
              ∙ ap (tensor-emb x l) (absorb-l r)

      rhs : Σ s ∶ C.ob
          , ∀ l r → tensor-emb s l r ≡ tensor-emb x l r
      rhs = x , λ _ _ → refl

  ⊗-unitl : (x : C.ob) → I ⊗ x ≡ x
  ⊗-unitl x =
    ap fst
      (is-contr→is-prop (tensor-composable-contr I x)
        lhs rhs)
    where
      lhs : Σ s ∶ C.ob
          , ∀ l r → tensor-emb s l r ≡ tensor-emb I l (noy x r)
      lhs = I ⊗ x , tensor-emb-comp-pt I x

      rhs : Σ s ∶ C.ob
          , ∀ l r → tensor-emb s l r ≡ tensor-emb I l (noy x r)
      rhs = x , tensor-emb-noy x
```

## Triple composite fiber and associativity

The ternary composite fiber `tensor-E₃` and its
contractibility give the associator.

```agda
  tensor-E₃ : (x y z : C.ob) → C.ob → C.ob → C.ob
  tensor-E₃ x y z l r = tensor-emb x l (noy y (noy z r))

  tensor-E₃-contr
    : (x y z : C.ob)
    → is-contr
        (Σ s ∶ C.ob
        , ∀ l r → tensor-emb s l r ≡ tensor-E₃ x y z l r)
  tensor-E₃-contr x y z .center .fst = (x ⊗ y) ⊗ z
  tensor-E₃-contr x y z .center .snd = tensor-emb-nest x y z
  tensor-E₃-contr x y z .paths =
    is-contr→is-prop
      (subst (λ T → is-contr
        (Σ s ∶ C.ob
        , ∀ l r → tensor-emb s l r ≡ T l r))
        path
        (tensor-composable-contr (x ⊗ y) z)) _
    where
      path
        : (λ l r → tensor-emb (x ⊗ y) l (noy z r))
        ≡ tensor-E₃ x y z
      path = funext λ l → funext λ r →
        tensor-emb-comp-pt x y l (noy z r)

  ⊗-assoc : (x y z : C.ob) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
  ⊗-assoc x y z =
    ap fst
      (is-contr→is-prop (tensor-E₃-contr x y z)
        (tensor-E₃-contr x y z .center) rhs)
    where
      rhs : Σ s ∶ C.ob
          , ∀ l r → tensor-emb s l r ≡ tensor-E₃ x y z l r
      rhs = x ⊗ (y ⊗ z)
          , λ l r →
              tensor-emb-comp-pt x (y ⊗ z) l r
              ∙ ap (tensor-emb x l) (tensor-noy-composite y z r)
```

## Extended composite fibers

`tensor-E₃-contr-ext` and `tensor-emb-image-contr-ext` restate
the triple-composite and image contractions as fibers of
`tensor-emb`, converting the pointwise equations to path
equations with `tensor-emb-ext`. The pentagon consumes the
extended triple fiber.

```agda
  tensor-E₃-contr-ext
    : (x y z : C.ob)
    → is-contr (fiber tensor-emb (tensor-E₃ x y z))
  tensor-E₃-contr-ext x y z = c'
    where
      PW = Σ s ∶ C.ob
         , ∀ l r → tensor-emb s l r ≡ tensor-E₃ x y z l r

      to-ext : PW → fiber tensor-emb (tensor-E₃ x y z)
      to-ext (s , q) = s , tensor-emb-ext q

      c = tensor-E₃-contr x y z

      c' : is-contr (fiber tensor-emb (tensor-E₃ x y z))
      c' .center = to-ext (c .center)
      c' .paths (s , p) =
        ap to-ext (c .paths (s , λ l r i → p i l r))

  -- The extended triple fiber's center identifies with the
  -- right-nested associator target x ⊗ (y ⊗ z). The pentagon,
  -- triangle, and hexagon consume this identification.
  assoc-σ
    : (x y z : C.ob)
    → tensor-E₃-contr-ext x y z .center
    ≡ ( x ⊗ (y ⊗ z)
      , tensor-emb-composite x (y ⊗ z)
      ∙ tensor-emb-ext λ l r →
          ap (tensor-emb x l) (tensor-noy-composite y z r))
  assoc-σ x y z =
    is-contr→is-prop (tensor-E₃-contr-ext x y z) _ _

  tensor-emb-image-contr-ext
    : (x : C.ob)
    → is-contr (fiber tensor-emb (tensor-emb x))
  tensor-emb-image-contr-ext x = c'
    where
      PW = Σ s ∶ C.ob
         , ∀ l r → tensor-emb s l r ≡ tensor-emb x l r

      to-ext : PW → fiber tensor-emb (tensor-emb x)
      to-ext (s , q) = s , tensor-emb-ext q

      c = tensor-emb-image-contr x

      c' : is-contr (fiber tensor-emb (tensor-emb x))
      c' .center = to-ext (c .center)
      c' .paths (s , p) =
        ap to-ext (c .paths (s , λ l r i → p i l r))
```

## Deferred

The following extend the object-level structure and are left
for later milestones:

- **Embedding-property extras**: `emb-is-embedding`,
  `emb-section`, `emb-retraction`,
  `composable-yon`, `emb-yon-ind`, `composable-swap`,
  `yon-inj`, `noy-inj`, and the opposite tensor `op`. These
  support braiding and duality, not the headline associator.
- **Pentagon and triangle**: to be derived natively for the
  tensor in a new `Cat.Monoidal.Coherence` submodule.
- **Morphism-level derived lemmas**: the fields
  (`htensor-emb`, `htensor-unit`, `htensor-compose-contr`,
  `htensor-interchange`, `htensor-yon-eval`,
  `htensor-bifunctor`) and the projections `hnoy`, `hyon`,
  `_⊗ₕ_`, `⊗ₕ-comp-pt` are in place. Still to derive:
  bifunctoriality of `_⊗ₕ_` (`⊗ₕ-preserves-⨾`),
  `htensor-preserves-idn`, unitor and associator naturality,
  and the `idtoiso` bridge into invertible tensor cells.
  These promote `monoidal` from an object-level structure to
  a genuine one-object bicategory.
